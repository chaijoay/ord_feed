#!/usr/bin/perl -w
###
###++
###  FACILITY            : FMS OrderEvent Feeder
###
###  FILE NAME           : fms_order_feed.pl
###
###  ABSTRACT            : prepare and detect Order transaction for FMS
###
###  AUTHOR              : N. Thanakorn
###
###  CREATE DATE         : 12-Jan-2017
###
###  CURRENT VERSION NO  : 1.0
###
###  LAST RELEASE DATE   :
###
###  MODIFICATION HISTORY :
###      0.1     31-Jan-2017     initial version
###      1.0     09-Feb-2017     release version
###++
###
###
### ----- [ Included Library ] -----
###
use strict;
use FindBin;
use lib "$FindBin::Bin/lib/perl";
use Config::IniFiles;
use File::Basename;
use File::Copy;
use IO::Compress::Gzip qw(gzip $GzipError);
use POSIX qw(mktime strftime ceil floor);
use Carp;
use DBI;
###
### ----- [ Constant declaration ] -----
###
use constant APP_VER    => '1.0 (09-Feb-2017)';
###
### ----- [ global ini default value list ] -----
###
my $gszIniLogDir = '';
my $gszIniTmpDir = '';
my $gszIniHistDir = '';
my $gszIniInpDir = '';
my $gszIniOutDir = '';
my $gszInputSnapFile = '';

my $gcIniBackupOutput = 'N';
my $gnIniBackupOutDir = '';

my $gszEnvOraHomeDir = '';
my $gszEnvLdLibDir = '';

my $gnIniNofTopDealer = 0;
my $gnIniMinCountTopDealer = 0;
my $gcIniBackupTopX = 'N';
my $gszIniBackupTopXDir = '';

my $gnIniDealerChkPeriod = 0;
my $gnIniDealerChkCount = 0;

my $gszIniDbUser = '';
my $gszIniDbPwd = '';
my $gszIniDbName = '';


my $gcIniEnableRej = 'N';

my $gszInpPrefix = 'sff_orderevt_';          # in format of Ord_evt_yyyymmddhhmmss.dat

my $gszOutPrefix = 'ORDER_';            # in format of ORDER_Ord_evt_yyyymmddhhmmss.dat.DAT
my $gszHistPrefix = 'for_multidealer_'; # in format of for_multidealer_yyyymmdd.dat (layout <CA_NO>|<DEALER_CODE>)

my $gszSuffix = '.dat';


my $goDBHandle;

use constant SEC_IN_DAY         => 86400;

# --------- Pattern Flag ---------
use constant PAT_NONE           => 0x0000;
use constant PAT_ID_CARD        => 0x0001;
use constant PAT_TOP_X_DEALER   => 0x0002;
use constant PAT_BAD_DEBT       => 0x0004;
use constant PAT_MULTI_DEALER   => 0x0008;

use constant _YES               => 1;
use constant _NO                => 0;

use constant ORD_TYPE_UNK           => 0;
use constant ORD_TYPE_NEW_REG       => 1;
use constant ORD_TYPE_CHG_CHRG_TYPE => 2;
use constant ORD_TYPE_CHG_SERV_IR   => 3;
use constant ORD_TYPE_CHG_SERV_IDD  => 4;
use constant ORD_TYPE_CQS_USAGE     => 5;

use constant SERV_NAME_UNK          => 0;
use constant SERV_NAME_IR           => 1;
use constant SERV_NAME_IDD          => 2;


my $gnPatMatch = PAT_NONE;

###
### ----- [ Map Hash From Config File to Global Config Variable ] -----
###
my %ghParseMapINI = (
    'General'    => {
        'LogPath'                   => \$gszIniLogDir,
        'TempPath'                  => \$gszIniTmpDir,
        'MultiDealerHistoryPath'    => \$gszIniHistDir,
        'SubOrderInputPath'         => \$gszIniInpDir,
        'IumOutputPath'             => \$gszIniOutDir,
        'BackupOutput'              => \$gcIniBackupOutput,
        'BackupOutPath'             => \$gnIniBackupOutDir,
        'NumberOfTopDealer'         => \$gnIniNofTopDealer,
        'MinCountTopDealer'         => \$gnIniMinCountTopDealer,
        'BackupTopX'                => \$gcIniBackupTopX,
        'BackupTopXPath'            => \$gszIniBackupTopXDir,
        'MultiDealerCheckPeroid'    => \$gnIniDealerChkPeriod,
        'MultiDealerCheckCount'     => \$gnIniDealerChkCount,
        'DbUser'                    => \$gszIniDbUser,
        'DbPassword'                => \$gszIniDbPwd,
        'DbName'                    => \$gszIniDbName,
        'ENV_ORACLE_HOME'           => \$gszEnvOraHomeDir,
        'ENV_LD_LIBRARY'            => \$gszEnvLdLibDir
    }
);
###
### ----- global mapping table -----
###
my %ghMapMultiDealer = ();          # for_multidealer_YYYYMMDD.dat
my %ghMapTopXdealer = ();           # Top X Dealer from current processing input file
my %ghMapLovSubCat = ();            # LOV Sub Category 
###
### ----- global for main processing loop -----
###
my $gszRunDir = dirname(__FILE__);
my $gszProcessName = basename(__FILE__, '.pl');
my $gszConfigFile = "${gszRunDir}/${gszProcessName}.ini";
my $gszCurFilePath = '';
my $gszInputFile = '';
# ----- Current Processing Fule File Paths -----
my $gszErrOutFile = '';
my $gszDatOutFile = '';

my $gszBadDebtApp = "${gszRunDir}/chk_bad_debt.exe";

my %ghINI;

my $gszLogDate = '';
my $gszLogFile;

my $giTerminateFlag = 0;
#
# ----- File Processing Counter Variable -----
#
my $glProcFileCnt = 0;
my $glReadRecFileCnt = 0;
my $glWrtRecFileCnt = 0;
my $glErrRecFileCnt = 0;
my $glReadRecAllCnt = 0;
my $glWrtRecAllCnt = 0;
my $glErrRecAllCnt = 0;
###
### ----- Directory Pointer -----
###
my $READ_DIR;
###
### ----- File Pointer -----
###
my $W_APPEND_LOG_FILE;      # log file pointer

my $RW_SNAP_FILE;           # snapshot file pointer
my $R_DAT_IN_FILE;          # Current processing input XDR file pointer
#my $W_OUT_ERR_FILE;         # Error File cont : logs error of missing expected field, invalid format of data, unable to validate or mapping.
my $W_DAT_OUT_FILE;         # Output file pointer for ium


my $gszCurRdRecLn;
###
### ----- Message Log Type -----
###
my $TXT_SEVER_INF = 'INF';
my $TXT_SEVER_WRN = 'WRN';
my $TXT_SEVER_ERR = 'ERR';
###
### --- [ Function definitions ]  ----------------------------------------------
###
sub parseINI {

    tie %ghINI, 'Config::IniFiles', ( -file => "${gszConfigFile}") or die "ERROR: Parse configuration file ($gszConfigFile) Fail\n";
    ### Map Value From Config into Global Config Variable
    while ( my ($szSection, $rhSection) = each(%ghParseMapINI) ) {
        while ( my ($szKey, $rValue) = each(%$rhSection) ) {
            if ( defined $ghINI{$szSection}{$szKey} ) {
                ${$rValue} = $ghINI{$szSection}{$szKey};
            }
            else {
                printf STDERR ("ERROR: Not found %s in Configuration File\n", $szKey);
                return -1;
            }
        }
    }

    ### verify input config
    if ( ! -d $gszIniLogDir ) {
        printf STDERR ("ERROR: Cannot access dir: %s - $!\n", $gszIniLogDir);
        return -1;
    }
    if ( ! -d $gszIniTmpDir ) {
        printf STDERR ("ERROR: Cannot access dir: %s - $!\n", $gszIniTmpDir);
        return -1;
    }
    if ( ! -d $gszIniHistDir ) {
        printf STDERR ("ERROR: Cannot access dir: %s - $!\n", $gszIniHistDir);
        return -1;
    }
    if ( ! -d $gszIniInpDir ) {
        printf STDERR ("ERROR: Cannot access dir: %s - $!\n", $gszIniInpDir);
        return -1;
    }
    if ( ! -d $gszIniOutDir ) {
        printf STDERR ("ERROR: Cannot access dir: %s - $!\n", $gszIniOutDir);
        return -1;
    }
    if ( $gcIniBackupOutput eq 'Y' && ! (-d $gnIniBackupOutDir) ) {
        printf STDERR ("ERROR: Cannot access dir: %s - $!\n", $gnIniBackupOutDir);
        return -1;
    }
    if ( $gcIniBackupTopX eq 'Y' && ! (-d $gszIniBackupTopXDir) ) {
        printf STDERR ("ERROR: Cannot access dir: %s - $!\n", $gszIniBackupTopXDir);
        return -1;
    }
    if ( ! -d $gszEnvOraHomeDir ) {
        printf STDERR ("ERROR: Cannot access dir: %s - $!\n", $gszEnvOraHomeDir);
        return -1;
    }
    #if ( ! -d $gszEnvLdLibDir ) {
    #    printf STDERR ("ERROR: Cannot access dir: %s - $!\n", $gszEnvLdLibDir);
    #    return -1;
    #}

    return 0;
}

sub getSysDate {

    my ($szSecond, $szMinute, $szHour, $szDate, $szMonth, $szYear) = localtime(time);
    $szYear +=1900;
    $szMonth += 1;
    ### Format is "YYYYMMDD"
    return sprintf("%04d%02d%02d", $szYear, $szMonth, $szDate);

}

sub getSysYYYYMMDDH24MiSS {

    my ($szSecond, $szMinute, $szHour, $szDate, $szMonth, $szYear) = localtime(time);
    $szYear +=1900;
    $szMonth += 1;
    ### Format is "YYYYMMDD"
    return sprintf("%04d%02d%02d%02d%02d%02d", $szYear, $szMonth, $szDate, $szHour, $szMinute, $szSecond);

}

sub timeToYYYYMMDDH24MiSS {

    my ($time_t) = @_;
    my ($szSecond, $szMinute, $szHour, $szDate, $szMonth, $szYear) = localtime($time_t);
    $szYear +=1900;
    $szMonth += 1;
    ### Format is "YYYYMMDD"
    return sprintf("%04d-%02d-%02d %02d:%02d:%02d", $szYear, $szMonth, $szDate, $szHour, $szMinute, $szSecond);
}

sub getTimeT {

    my ($ymdHMS) = @_;
    my $time_t = 0;
    if ( length($ymdHMS) < 14 ) {
        return $time_t;
    }
    $time_t = mktime(int(substr($ymdHMS,12,2)), int(substr($ymdHMS,10,2)), int(substr($ymdHMS,8,2)), int(substr($ymdHMS,6,2)), int(substr($ymdHMS,4,2))-1, int(substr($ymdHMS,0,4))-1900, 0, 0, 0);
    return $time_t;

}

sub dateAdd {

    my ($days) = @_;
    my $date_calc = time() + ($days * SEC_IN_DAY);
    my ($szSecond, $szMinute, $szHour, $szDate, $szMonth, $szYear) = localtime($date_calc);
    $szYear +=1900;
    $szMonth += 1;
    return sprintf("%04d%02d%02d", $szYear, $szMonth, $szDate);

}

sub getLogTime {

    my ($szSecond, $szMinute, $szHour, $szDate, $szMonth, $szYear) = localtime(time);
    $szYear +=1900;
    $szMonth += 1;
    ### Format is "YYYY/MM/DD HH24:MI:SS"
    return sprintf("%04d/%02d/%02d %02d:%02d:%02d", $szYear, $szMonth, $szDate, $szHour, $szMinute, $szSecond);

}

sub getNewLogFileFullNameForDate {

    my $szLogDate = shift;
    return sprintf("%s/%s_%s.log", $gszIniLogDir, $gszProcessName, $szLogDate);

}

### Create Log File When Date Changed or Re-Run
### Log File Always Be Flushed
sub writeLog {

    my ($szLogType, $szMessage) = @_;
    my $szLine;
    my $szCurDate;

    $szCurDate = getSysDate();

    ### Check New Date
    if($szCurDate ne $gszLogDate){
        ### New Date or Current Log File Not Exists, So Create New Log File
        ### Save Log Date
        $gszLogDate = $szCurDate;
        $gszLogFile = getNewLogFileFullNameForDate($gszLogDate);
    }

    ### Open Log File
    open($W_APPEND_LOG_FILE, ">>", "$gszLogFile" ) or die "ERROR: Cannot create log file ($gszLogFile)";

    $szLine = sprintf("%s - %s - %s", getLogTime(), $szLogType, $szMessage);
    printf $W_APPEND_LOG_FILE ("%s\n", $szLine);
    close($W_APPEND_LOG_FILE);

}

sub writeLogExit {

    my ($szMessage) = @_;

    if ( $szMessage eq '' ) {
        $szMessage = "Successfully stop";
    }
    else {
        $szMessage = "'${szMessage}' caused stop";
    }
    writeLog($TXT_SEVER_INF, "===== ${gszProcessName} ${szMessage} =====");
    exit;

}

sub printConfigParameters {

    writeLog($TXT_SEVER_INF, '----= Configuration Parameters =----');

    foreach my $szSection (sort(keys(%ghINI))) {
        my $rhSection = $ghINI{$szSection};
        writeLog($TXT_SEVER_INF, "  [$szSection]");

        foreach my $szKey (sort(keys(%$rhSection))) {
            my $rValue = $rhSection->{$szKey};
            if ( ref($rValue) eq 'ARRAY' ) {
                foreach my $szValue (@$rValue) {
                    if ( $szKey eq "DbPassword" ) {
                        next;
                    }
                    writeLog($TXT_SEVER_INF, "    $szKey = $szValue");
                }
            }
            else {
                if ( $szKey eq "DbPassword" ) {
                    next;
                }
                writeLog($TXT_SEVER_INF, "    $szKey = $rValue");
            }
        }
    }
    writeLog($TXT_SEVER_INF, '------------------------------------');

}

sub setSignalInterrupt {

    my ($szSignal) = @_;

    ### What to do for each signal
    if ( $szSignal eq 'TERM' || $szSignal eq 'INT' ) {
        ### When Receive 'Ctrl C' or Kill -TERM
        $giTerminateFlag = 1;
        ### During System Call, Writing something to a file might make perl script abort immediately !!!
        writeLog($TXT_SEVER_INF, 'Receive Interrupt or Terminate signal');
    }

}

sub trapInterruptSignal {

    $SIG{'INT'} = 'setSignalInterrupt';
    $SIG{'TERM'} = 'setSignalInterrupt';

    $giTerminateFlag = 0;

}

sub getMapping {

    my ($hTable, $szKey) = @_;

    if ( !exists($hTable->{$szKey}) ) {
        return '';
    }
    return $hTable->{$szKey};

}

sub loadDealerCountHistory {

    my ($szRadfile, $hTable) = @_;

    my $READ_FILE;
    my $nCnt = 0;

    if ( ! -f $szRadfile ) {
        writeLog($TXT_SEVER_WRN, "cannot open or file does not exist for history '${szRadfile}'");
        return;
    }

    my $szUxCmd = sprintf("sort -u %s > %s.tmp", $szRadfile, $szRadfile);

    system($szUxCmd);
    rename("${szRadfile}.tmp", $szRadfile);

    $szUxCmd = sprintf("gawk -F \"|\" '{ print \$1 }' %s | sort | uniq -c |", $szRadfile);

    %$hTable = ();
    if ( open($READ_FILE, $szUxCmd) ) {

        while ( my $szLine =  <$READ_FILE> ) {

            chomp($szLine);

            my @aMapField = split(' ', $szLine, -1);

            # skip empty record (at least two columns for key and value) [ $#{arrary} returns index of last element which is total_item - 1 ]
            if ( $#{aMapField} < 1 ) {
                next;
            }

            my $szKey = $aMapField[1];
            my $szValue = $aMapField[0];

            $hTable->{$szKey} = $szValue;
            $nCnt += 1;
        }

        close($READ_FILE);
        writeLog($TXT_SEVER_INF, "read history : ${nCnt} records read");
    }
}

sub loadMappingFile {

    ### for_multidealer_YYYYMMDD.dat (include current day if any, exclude current processing file)
    my $map_file = sprintf("%s/%s%s.tmp", $gszIniTmpDir, $gszHistPrefix, getSysYYYYMMDDH24MiSS());

    unlink($map_file);
    for ( my $i=0; $i <= $gnIniDealerChkPeriod; $i++ ) {
        my $hist_file = sprintf("%s/%s%s%s", $gszIniHistDir, $gszHistPrefix, dateAdd($i * (-1)), $gszSuffix);
        if ( -f $hist_file ) {
            my $szUxCmd = sprintf("cat %s >> %s", $hist_file, $map_file);
            system($szUxCmd);
        }
    }
    loadDealerCountHistory($map_file, \%ghMapMultiDealer);
    loadLovBy("FRM_ACCOUNT_SUBCAT", \%ghMapLovSubCat);
    unlink($map_file);

}

sub loadLovBy {

    my ($lov_type, $hTable) = @_;
    my $nCnt = 0;
    
    if ( ! $goDBHandle || ! $goDBHandle->ping() ) {
        connectDB();
    }
    
    %$hTable = ();
    #lov_type = FRM_ACCOUNT_SUBCAT
    my $sSql = "SELECT LOV_DESC, LOV_ID FROM FRAUD_LOV WHERE UPPER(LOV_TYPE) = '${lov_type}'";

    my $oStmt;
    if ( ! ($oStmt = $goDBHandle->prepare($sSql)) ) {
        writeLogExit("cannot prepare sql ($sSql)");
    }

    if ( ! $oStmt->execute() ) {
        writeLogExit("cannot execute sql ($sSql)");
    }

    while ( my @aField = $oStmt->fetchrow_array() ) {
        $hTable->{$aField[0]} = $aField[1];
        $nCnt += 1;

    }

    if ( defined $goDBHandle->errstr ) {
        writeLog($TXT_SEVER_ERR, $goDBHandle->errstr);
    }    

    disconnectDB();
    writeLog($TXT_SEVER_INF, "read fraud_lov : ${nCnt} records read");

}

sub connectDB {

    writeLog($TXT_SEVER_INF, "connecting DB ...");
    my $sDataSource = "dbi:Oracle://Thane:1521/ERM_A";
    my $sDbUser = "cfms"; 
    my $sDbPwd = "Hpfms8365";

    until ( $goDBHandle = DBI->connect($sDataSource, $sDbUser, $sDbPwd, {PrintError => 0, RaiseError => 0}) ) {
        writeLog($TXT_SEVER_WRN, "Cannot connect: $DBI::errstr");
        writeLog($TXT_SEVER_INF, "Re-try connecting in 1 minutes ...");
        sleep(60);
        if ( $giTerminateFlag == 1 ) {
            return;
        }
        writeLog($TXT_SEVER_INF, "Connecting DB ...");

    }
    writeLog($TXT_SEVER_INF, "DB connected successfully");

}

sub disconnectDB {

    if ( $goDBHandle ) {
        writeLog($TXT_SEVER_INF, "disconnect DB");
        $goDBHandle->disconnect;
    }

}

sub purgeOldHist {

    my $start_purge_date = dateAdd( $gnIniDealerChkPeriod * (-1) );
    my $regexHistFile = qr/^$gszHistPrefix(\d{8})$gszSuffix$/i;
    my $HIST_DIR;

    if ( !opendir($HIST_DIR, $gszIniHistDir) ){
        writeLog($TXT_SEVER_ERR, "Cannot read directory ${gszIniHistDir}: $!");
    }
    else {
        while ( my $szHistFile = readdir($HIST_DIR) ) {
            ### Look up File Match Pattern
            if ($szHistFile !~ /$regexHistFile/ || ! -f "${gszIniHistDir}/${szHistFile}") {
                next;
            }

            ### $1 ---> YYYYMMDD
            my $szYMD = $1;
            if ( $start_purge_date > $szYMD ) {
                unlink("${gszIniHistDir}/${szHistFile}");
                writeLog($TXT_SEVER_INF, "file ${szHistFile} is purged");
            }
        }
        closedir($HIST_DIR);
    }

}

sub buildSnapFile {

    my $allow_oldest_date = dateAdd( $gnIniDealerChkPeriod * (-1) );
    writeLog($TXT_SEVER_INF, 'Build new input Snap file ...');

    ###
    ### input file format is changed from: 'Ord_evt_YYYYMMDDHHMMSS.dat'
    #                                  to: 'sff_orderevt_NNNN_YYYYMMDDHHMMSS_NNN.dat'
    ###
    my $regexSyncFileName = qr/^$gszInpPrefix.*(\d{4})_(\d{14})_(\d{3}).*$gszSuffix$/i;

    $gszInputSnapFile = "${gszRunDir}/${gszProcessName}.snap";
    if ( !opendir($READ_DIR, $gszIniInpDir) ){
        writeLog($TXT_SEVER_ERR, "Cannot read directory ${gszIniInpDir}: $!");
        writeLogExit("");
    }

    if ( !open($RW_SNAP_FILE, '>', "${gszInputSnapFile}.tmp") ) {
        writeLog($TXT_SEVER_ERR, "Cannot write Snap file (${gszInputSnapFile}.tmp): $!");
        writeLogExit("");
    }

    while ( my $szFileName = readdir($READ_DIR) ) {
        ### Look up File Match Pattern Sync Filename
        if ($szFileName !~ /$regexSyncFileName/ || ! -f "${gszIniInpDir}/${szFileName}") {
            next;
        }

        ### $2 ---> YYYYMMDDHHMM
        my $szYMDHm = $2;
        my $szYMD = substr($szYMDHm, 0, 8);

        if ( $szYMD ge $allow_oldest_date ) {
            if ( ! -s "${gszIniInpDir}/${szFileName}" ) {
                writeLog($TXT_SEVER_ERR, "Cannot access data file ${szFileName}: $!");
                rename("${gszIniInpDir}/${szFileName}", "${gszIniInpDir}/${szFileName}_ERR");
                next;
            }
            print $RW_SNAP_FILE ("${szYMDHm}|${gszIniInpDir}|${szFileName}\n");
        }
    }
    closedir($READ_DIR);
    close($RW_SNAP_FILE);

    my $szCmd = sprintf("sort -T \"%s\" -t \"|\" -k 1,1 -k 3,3 \"%s\" > \"%s\" ", $gszIniOutDir, "${gszInputSnapFile}.tmp", "${gszInputSnapFile}");

    system($szCmd);
    unlink("${gszInputSnapFile}.tmp");

    writeLog($TXT_SEVER_INF, 'Build new input Snap file finished');

}

sub doBackupProcessedFile {

    return 0;

}

sub openWorkingFiles {

    # $gszErrOutFile = sprintf("%s/%s.err", $gszIniErrDir, $gszInputFile);
    $gszDatOutFile = sprintf("%s/%s%s", $gszIniOutDir, $gszOutPrefix, $gszInputFile);

    if ( !open($W_DAT_OUT_FILE, '>', "${gszDatOutFile}") ) {
        writeLog($TXT_SEVER_ERR, "cannot open to write input file (${gszDatOutFile}): $!");
        writeLogExit("");
    }

}

sub closeWorkingFiles {

    doBackupProcessedFile();

    if ( -s "${gszDatOutFile}.tmp" ) {
        ### Rename output file to indicate its completion
        # .tmp is output from calling check bad debt
        if ( $gcIniBackupOutput eq 'Y' ) {
            copy("${gszDatOutFile}.tmp", "${gnIniBackupOutDir}/${gszOutPrefix}${gszInputFile}.DAT");
            gzip "${gnIniBackupOutDir}/${gszOutPrefix}${gszInputFile}.DAT" => "${gnIniBackupOutDir}/${gszOutPrefix}${gszInputFile}.DAT.gz";
            unlink("${gnIniBackupOutDir}/${gszOutPrefix}${gszInputFile}.DAT");
        }
        rename("${gszDatOutFile}.tmp", "${gszDatOutFile}.DAT");
    }
    else {
        ### delete empty output file
        unlink("${gszDatOutFile}.tmp");         # temp file from calling check bad debt.
    }
    unlink($gszDatOutFile);                     # temp file gen by this script.

    # current processing input
    unlink("${gszIniInpDir}/${gszInputFile}");

}

sub parseInputData {

    my ($rhFields) = @_;

    my $raInputFld = [split(/\|/, $gszCurRdRecLn, -1)];

    $glReadRecFileCnt += 1;

    my $nColumnCnt = @$raInputFld;
    if ( $nColumnCnt >= 27 ) {
        %{$rhFields} = (
            'MOB_NO'            => $raInputFld->[ 0],
            'CA_NO'             => $raInputFld->[ 1],
            'ORD_DATE'          => $raInputFld->[ 2],
            'CQS_USAGE'         => $raInputFld->[ 3],
            'CQS_CHARGE'        => $raInputFld->[ 4],
            'CA_NAME'           => $raInputFld->[ 5],
            'BA_NAME'           => $raInputFld->[ 6],
            'BA_NO'             => $raInputFld->[ 7],
            'BA_ADDR1'          => $raInputFld->[ 8],
            'BA_ADDR2'          => $raInputFld->[ 9],
            'ZIPCODE'           => $raInputFld->[10],
            'ORD_REASON_CD'     => $raInputFld->[11],
            'ORD_REASON'        => $raInputFld->[12],
            'CA_CATEGORY'       => $raInputFld->[13],
            'CA_SUB_CAT'        => $raInputFld->[14],
            'AIS_SHOP'          => $raInputFld->[15],
            'ID_CARD_TYPE'      => $raInputFld->[16],
            'ID_CARD_NO'        => $raInputFld->[17],
            'DEALER_CODE'       => $raInputFld->[18],
            'DEALER_NAME'       => $raInputFld->[19],
            'LOC_CODE'          => $raInputFld->[20],
            'LOC_NAME'          => $raInputFld->[21],
            'ORD_TYPE'          => $raInputFld->[22],
            'SERV_NAME'         => $raInputFld->[23],
            'SERV_DATE'         => $raInputFld->[24],
            'NATIONALITY'       => $raInputFld->[25],
            'PRO_MAIN'          => $raInputFld->[26],
            'MOB_ACTIVE_DT'     => $raInputFld->[27],
            'ASC_NUMBER'        => $raInputFld->[28],
            'PRETTY_FLAG'       => _NO,
            'PATTERN_FLAG'      => $gnPatMatch,
            'DEALER_COUNT'      => 0,
            'ERM_CATEGORY'      => 0,
            'RAWDATA'           => $gszCurRdRecLn
        );
    }
    else {
        $glErrRecFileCnt++;
        writeLog($TXT_SEVER_WRN, "Column counts less than expected[16] : [${nColumnCnt}]");
    }

    return 0;

}

sub wrtOutputFile {

    my ($rhFields) = @_;

    print $W_DAT_OUT_FILE ( $rhFields->{'MOB_NO'},
    '|', $rhFields->{'CA_NO'},
    '|', $rhFields->{'ORD_DATE'},
    '|', $rhFields->{'CQS_USAGE'},
    '|', $rhFields->{'CQS_CHARGE'},
    '|', $rhFields->{'CA_NAME'},
    '|', $rhFields->{'BA_NAME'},
    '|', $rhFields->{'BA_NO'},
    '|', $rhFields->{'BA_ADDR1'},
    '|', $rhFields->{'BA_ADDR2'},
    '|', $rhFields->{'ZIPCODE'},
    '|', $rhFields->{'ORD_REASON_CD'},
    '|', $rhFields->{'ORD_REASON'},
    '|', $rhFields->{'CA_CATEGORY'},
    '|', getMapping(\%ghMapLovSubCat, $rhFields->{'CA_SUB_CAT'}),   #'|', $rhFields->{'CA_SUB_CAT'},
    '|', $rhFields->{'AIS_SHOP'},
    '|', $rhFields->{'ID_CARD_TYPE'},
    '|', $rhFields->{'ID_CARD_NO'},
    '|', $rhFields->{'DEALER_CODE'},
    '|', $rhFields->{'DEALER_NAME'},
    '|', $rhFields->{'LOC_CODE'},
    '|', $rhFields->{'LOC_NAME'},
    '|', $rhFields->{'ORD_TYPE'},
    '|', $rhFields->{'SERV_NAME'},
    '|', $rhFields->{'SERV_DATE'},
    '|', $rhFields->{'NATIONALITY'},
    '|', $rhFields->{'PRO_MAIN'},
    '|', $rhFields->{'MOB_ACTIVE_DT'},
    '|', $rhFields->{'PRETTY_FLAG'},
    '|', $rhFields->{'PATTERN_FLAG'},
    '|', $rhFields->{'DEALER_COUNT'},
    '|', $rhFields->{'ASC_NUMBER'},
    '|', $rhFields->{'ERM_CATEGORY'},
    "\n" );
    $glWrtRecFileCnt += 1;
    my $x = getMapping(\%ghMapLovSubCat, $rhFields->{'CA_SUB_CAT'});
    my $y = $rhFields->{'CA_SUB_CAT'};
#printf ("$x, $y\n");
}

sub verifyInputFields {

    my ($rhFields) = @_;

    # set time_t to a field
    my $tmp = getTimeT($rhFields->{'ORD_DATE'});
    $rhFields->{'ORD_DATE'} = $tmp;

    $tmp = getTimeT($rhFields->{'SERV_DATE'});
    $rhFields->{'SERV_DATE'} = $tmp;

    $tmp = getTimeT($rhFields->{'MOB_ACTIVE_DT'});
    $rhFields->{'MOB_ACTIVE_DT'} = $tmp;

    return 0;

}

sub prepMultipleDealer {

    my ($szInpDir, $szInpFileName) = @_;

    my $nDealerCodeCol = 19;
    my $nCANumberCol = 2;
    # CA_No is 2nd column
    # Dealer Code is 19th column
    # Order Date is 3rd column
    # Skip the record that dealer code is null
    my $inputfile = sprintf("%s/%s", $szInpDir, $szInpFileName);
    my $szUxCmd = sprintf("gawk -F \"|\" '{ if ( \$%d != \"\" ) print \$%d\"|\"\$%d >> \"%s/%s\"substr(\$3, 1, 8)\"%s\" }' %s ", $nDealerCodeCol, $nCANumberCol, $nDealerCodeCol, $gszIniHistDir, $gszHistPrefix, $gszSuffix, $inputfile);

    system($szUxCmd);

}

sub getTopXdealer {

    my ($szInpDir, $szInpFileName, $hTable) = @_;
    my $R_TOP_DEALER;
    my $W_TOP_DEALER;
    my $nCurRec = 0;
    my $nPrevCnt = 0;

    # get top dealer using unix command by selecting dealer code field which is column 19
    my $nDealerCodeCol = 19;
    my $nIsAISShopCol = 16;
    
    my $temp_file = "${gszIniTmpDir}/.TopXDealer.txt";
    unlink($temp_file);
    my $szUxCmd = sprintf("gawk -F \"|\" '{ if ( \$%d != \"\" && \$%d != \"Y\" && \$%d != \"y\" ) print \$%d }' %s/%s | sort | uniq -c | sort -k 1nr,1 > %s", $nDealerCodeCol, $nIsAISShopCol, $nIsAISShopCol, $nDealerCodeCol, $szInpDir, $szInpFileName, $temp_file);
    system($szUxCmd);
    
#printf ("$szUxCmd\n");

    # If backup top dealer is set, open file for writing.
    if ( $gcIniBackupTopX eq 'Y' ) {

        my $szTopOutFile = sprintf("%s/%s_top%d", $gszIniBackupTopXDir, $gszInputFile, $gnIniNofTopDealer);
        if ( !open($W_TOP_DEALER, '>', "${szTopOutFile}") ) {
            writeLog($TXT_SEVER_ERR, "cannot open to write input file (${szTopOutFile}): $!");
            writeLogExit("");
        }

    }

    %$hTable = ();
    if ( open($R_TOP_DEALER, '<', "${temp_file}") ) {
    #if ( open($R_TOP_DEALER, $szUxCmd) ) {
#printf ("DBG-1\n");
        while ( my $line = <$R_TOP_DEALER> ) {
#printf ("DBG-2\n");
            chomp($line);
            $nCurRec++;
#printf ("DBG-3 read line '$line'\n");
            # $aDealer[0] is counts
            # $aDealer[1] is dealer code
            my @aDealer = split(' ', $line, -1);
#printf ("DBG-4 read line" . @aDealer . "\n");
            # dealer count msut greater than MinCountTopDealer
            if ( $aDealer[0] < $gnIniMinCountTopDealer ) {
                next;
            }
#printf ("DBG-5\n");
            # when the next dealer count still have same value as the last dealer, continue to include in a top dealer list
            if ( $nCurRec >= $gnIniNofTopDealer && $nPrevCnt > $aDealer[0] ) {
                last;
            }
#printf ("DBG-6\n");
            $hTable->{$aDealer[1]} = $aDealer[1];
            if ( $gcIniBackupTopX eq 'Y' ) {
                print $W_TOP_DEALER ( $aDealer[0], '|', $aDealer[1], "\n" );
            }
            $nPrevCnt = $aDealer[0];
#printf ("DBG-7\n");
        }
        close($R_TOP_DEALER);
        #unlink($temp_file);

        if ( $gcIniBackupTopX eq 'Y' ) {
            close($W_TOP_DEALER);
        }

    }

}

sub isPrettyNumber {

    my ($rhFields) = @_;

    if ( $rhFields->{'MOB_NO'} =~ /(\d)\1(\d)\2$/ ) {       ### pattern of XXYY    (\d)\1(\d)\2$
        $rhFields->{'PRETTY_FLAG'} = _YES;
    }
    elsif ( $rhFields->{'MOB_NO'} =~ /(\d{2})\1$/ ) {       ### pattern of XYXY    (\d{2})\1$
        $rhFields->{'PRETTY_FLAG'} = _YES;
    }
    elsif ( $rhFields->{'MOB_NO'} =~ /(\d)(\d)\2\1$/ ) {    ### pattern of YXXY    (\d)(\d)\2\1$
        $rhFields->{'PRETTY_FLAG'} = _YES;
    }
    elsif ( $rhFields->{'MOB_NO'} =~ /(\d)\1\1\d$/ ) {      ### pattern of XXXY    (\d)\1\1\d$
        $rhFields->{'PRETTY_FLAG'} = _YES;
    }
    elsif ( $rhFields->{'MOB_NO'} =~ /\d(\d)\1\1$/ ) {      ### pattern of XYYY    \d(\d)\1\1$
        $rhFields->{'PRETTY_FLAG'} = _YES;
    }
    elsif ( $rhFields->{'MOB_NO'} =~ /(123|234|345|456|567|678|789)$/ ) {   ### pattern of ?XYZ    (123|234|345|456|567|678|789)$
        $rhFields->{'PRETTY_FLAG'} = _YES;
    }
    else {
        $rhFields->{'PRETTY_FLAG'} = _NO;
    }
# printf "pretty: $rhFields->{'MOB_NO'}, $rhFields->{'PRETTY_FLAG'} \n";
}

sub checkDigitIdCard {

    my ($rhFields) = @_;

    if ( $rhFields->{'CA_CATEGORY'} eq 'R' && ($rhFields->{'ORD_TYPE'} eq ORD_TYPE_NEW_REG || $rhFields->{'ORD_TYPE'} eq ORD_TYPE_CHG_CHRG_TYPE) ) {
        if ( $rhFields->{'ID_CARD_TYPE'} eq 'ID_CARD' ) {
            if ( length($rhFields->{'ID_CARD_NO'}) != 13 ) {
                $rhFields->{'PATTERN_FLAG'} |= PAT_ID_CARD;
            }
            else {
                my @digit = split(//, $rhFields->{'ID_CARD_NO'});
                my $sum = 0;

                for ( my $i=0; $i < 12; $i++ ) {
                    $sum += $digit[$i] * (13 - $i);
                }

                if ( ((11-($sum%11))%10) != ($digit[12]*1) ) {
                    $rhFields->{'PATTERN_FLAG'} |= PAT_ID_CARD;
                }
            }
        }
    }
# printf "id: $rhFields->{'PATTERN_FLAG'}\n";
}

sub checkTopXdealer {

    my ($rhFields) = @_;
    if ( $rhFields->{'CA_CATEGORY'} eq 'R' && ($rhFields->{'ORD_TYPE'} eq ORD_TYPE_NEW_REG || $rhFields->{'ORD_TYPE'} eq ORD_TYPE_CHG_CHRG_TYPE) ) {
        if ( getMapping(\%ghMapTopXdealer, $rhFields->{'DEALER_CODE'}) ne '' ) {
            $rhFields->{'PATTERN_FLAG'} |= PAT_TOP_X_DEALER;
        }
    }
# printf "topx: $rhFields->{'PATTERN_FLAG'}\n";
}

sub checkMultipleDealer {

    my ($rhFields) = @_;

    if ( $rhFields->{'CA_CATEGORY'} eq 'R' && ($rhFields->{'ORD_TYPE'} eq ORD_TYPE_NEW_REG || $rhFields->{'ORD_TYPE'} eq ORD_TYPE_CHG_CHRG_TYPE) ) {
        my $dealerCnt = getMapping(\%ghMapMultiDealer, $rhFields->{'CA_NO'});

        if ( $dealerCnt ne '' ) {
            if ( ($dealerCnt + 0) >= ($gnIniDealerChkCount + 0) ) {
                $rhFields->{'PATTERN_FLAG'} |= PAT_MULTI_DEALER;
                $rhFields->{'DEALER_COUNT'} = $dealerCnt;
            }
        }
    }
# printf "multi: $rhFields->{'PATTERN_FLAG'}, $rhFields->{'DEALER_COUNT'}\n\n";
}

sub checkBadDebtSubs {

    my $READ_FILE;
    my $pat_bad_debt = PAT_BAD_DEBT;

    my $szCmd = "${gszBadDebtApp} -i=${gszDatOutFile} -o=${gszDatOutFile}.tmp -ca=2 -pat=30 -mask=${pat_bad_debt} -u=${gszIniDbUser} -p=${gszIniDbPwd} -s=${gszIniDbName} |";

    writeLog($TXT_SEVER_INF, "checking bad debt on ${gszDatOutFile}");
    if ( open($READ_FILE, $szCmd) ) {
        while (my $szLine = <$READ_FILE>) {
            chomp($szLine);
            writeLog($TXT_SEVER_INF, "> chk_bad_debt : ${szLine}");
        }
        close($READ_FILE);
    }
    else {
        writeLog($TXT_SEVER_ERR, "unable to execute chk_bad_debt !");
    }
}

sub processOrder {

    my ($szInputPath, $szInputFileName) = @_;
    my $szCurInputFile = sprintf("%s/%s", $szInputPath, $szInputFileName);
    my $szInfoLine = '';

    writeLog($TXT_SEVER_INF, "Processing on: ${szInputFileName}");

    openWorkingFiles();

    $glProcFileCnt += 1;

    if ( open($R_DAT_IN_FILE, '<', $szCurInputFile) ) {

        while ( my $proc_rec = <$R_DAT_IN_FILE> ) {

            chomp($proc_rec);
            $gszCurRdRecLn = $proc_rec;
            my %hParseData = ();

            if ( parseInputData(\%hParseData) != 0 ) {
                next;
            }

            #if ( verifyInputFields(\%hParseData) != 0 ) {
            #    next;
            #}

            # 1). Check if Mobile Number is a Pretty Number then mark Pretty Flag
            isPrettyNumber(\%hParseData);

            # 2). Check ID Card
            checkDigitIdCard(\%hParseData);

            # 3). Check Top x Dealer in one input data file
            checkTopXdealer(\%hParseData);

            # 4). Count multiple dealer in a period of time frame
            checkMultipleDealer(\%hParseData);

            # 6). Write output file
            wrtOutputFile(\%hParseData);

        }
        close($R_DAT_IN_FILE);  # close input data file
    }
    close($W_DAT_OUT_FILE);     # close temp output data file;

    checkBadDebtSubs();         # check bad debt by call exe to execute db

    closeWorkingFiles();        # close and clear all working and temp files

    my $lOthCnt = $glReadRecFileCnt - $glWrtRecFileCnt - $glErrRecFileCnt;
    $szInfoLine = sprintf("   Read=%ld, Mapped=%ld, Errors=%ld, Unknown=%ld", $glReadRecFileCnt, $glWrtRecFileCnt, $glErrRecFileCnt, $lOthCnt);
    writeLog($TXT_SEVER_INF, $szInfoLine);
    writeLog($TXT_SEVER_INF, "Completed on: ${szInputFileName} output to ${gszDatOutFile}.DAT");


    ### reset value for next loop ...
    $glReadRecAllCnt += $glReadRecFileCnt;
    $glWrtRecAllCnt  += $glWrtRecFileCnt;
    $glErrRecAllCnt  += $glErrRecFileCnt;
    $glReadRecFileCnt = 0;
    $glErrRecFileCnt = 0;
    $glWrtRecFileCnt = 0;

}
###
###
###
### <---------------------------------------------------------------------------->
### ######### ######### #########   Main Program   ######### ######### #########
### <---------------------------------------------------------------------------->
###
###
###
### <-- [ configuration loading ] -------------------------------------------->
if ( parseINI() != 0 ) {
    exit;
}

writeLog($TXT_SEVER_INF, "===== ${gszProcessName} Start =====");
printConfigParameters();

### <-- [ signal handle registeration ] ------------------------------------->
trapInterruptSignal();

if ( ! -x $gszBadDebtApp ) {
    writeLog($TXT_SEVER_ERR, "Bad Debt App is not available '${gszBadDebtApp}': $!");
    writeLogExit("");
}

# set environment for bad debt app to query data
$ENV{ORACLE_HOME} = $gszEnvOraHomeDir;
$ENV{LD_LIBRARY_PATH} = $gszEnvLdLibDir;

### < --- --- --- Main Loop --- --- --- >

### <-- [snapshot files building ] ----------------------------------------->
buildSnapFile();

if ( !open($RW_SNAP_FILE, '<', $gszInputSnapFile) ) {
    writeLog($TXT_SEVER_ERR, "Cannot open Snap file to Read '${gszInputSnapFile}': $!");
    writeLogExit("");
}
else {
### <-- [ Loop of file processing ] ---------------------------------------->
    my $snap_rec;

    # making dealer history file from current input
    while ( $snap_rec = <$RW_SNAP_FILE> ) {
        chomp($snap_rec);
        (my $szInFileModDate, $gszCurFilePath, $gszInputFile) = split(/\|/, $snap_rec, 3);
        prepMultipleDealer($gszCurFilePath, $gszInputFile);                 # make history file of dealer (ca_no|dealer_code)
    }

    # load dealer history from file
    loadMappingFile();

    # restart reading file pointer from the first
    seek($RW_SNAP_FILE, 0, 0);

    # main processing loop
    while ( $snap_rec = <$RW_SNAP_FILE> ) {

        chomp($snap_rec);
        (my $szInFileModDate, $gszCurFilePath, $gszInputFile) = split(/\|/, $snap_rec, 3);

        if ( $giTerminateFlag == 1 ) {
            last;
        }

        getTopXdealer($gszCurFilePath, $gszInputFile, \%ghMapTopXdealer);   # make top n dealer from each current input file

        #foreach ( sort keys %ghMapTopXdealer ) { print "$_ : $ghMapTopXdealer{$_}\n"; }
        #print "\n";
        #foreach ( sort keys %ghMapMultiDealer ) { print "$_ : $ghMapMultiDealer{$_}\n"; }

        processOrder($gszCurFilePath, $gszInputFile);

    }
    purgeOldHist()
}

close($RW_SNAP_FILE);
my $lOthCnt = $glReadRecAllCnt - $glWrtRecAllCnt - $glErrRecAllCnt;
my $szInfoLine = sprintf("Read=%ld, Mapped=%ld, Errors=%ld, Unknown=%ld", $glReadRecAllCnt, $glWrtRecAllCnt, $glErrRecAllCnt, $lOthCnt);
if ( ${glProcFileCnt} > 0 ) {
    writeLog($TXT_SEVER_INF, "Total processed input file=${glProcFileCnt}, ${szInfoLine}");
}
else {
    writeLog($TXT_SEVER_INF, "No file to be processed");
}

writeLogExit("");
###
###
###
### <---------------------------------------------------------------------------->
###  ######### ######### #########   End Program   ######### ######### #########
### <---------------------------------------------------------------------------->
###

# ---- Input Format ----- #
# -No-|- Field ----------|-- Remarks ---
# 1   | Mobile Number    |
# 2   | CA no            |
# 3   | Order date       | yyyymmddhh24miss
# 4   | CQS Usage        | duration (only when order type is CQS Usage)
# 5   | CQS Charge       | in satang (only when order type is CQS Usage)
# 6   | CA_Name          |
# 7   | BA_Name          |
# 8   | BA_No            |
# 9   | BA_Address1      |
# 10  | BA_Address2      |
# 11  | Postcode         |
# 12  | Order Reason cd  |
# 13  | Order Reason     |
# 14  | Category         |
# 15  | Sub Category     |
# 16  | Ais Shop         | Y/N
# 17  | ID Card Type     |
# 18  | ID Card No       |
# 19  | Dealer code      |
# 20  | Dealer Name      |
# 21  | Location cd      |
# 22  | Location Name    |
# 23  | Order Type       |
# 24  | Service Nmea     |
# 25  | Service Date     |
# 26  | Nationality      |
# 27  | Promo Name       |
# 28  | Register Date    |
# 29  | ASC Number       |
