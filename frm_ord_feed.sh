
#!/usr/bin/ksh
typeset -r _SCRIPT_NAME="${_##*/}"
_SCRIPT_PATH="${0%/*}" && typeset -r _SCRIPT_PATH=$(cd -- "${_SCRIPT_PATH}" && pwd)
_HOME_PATH="${0%/*}" && typeset -r _HOME_PATH=$(cd -- "${_HOME_PATH}/.." && pwd)

#########################
### Environment #########
#########################
# Don't remove these environments because perl module require LD_LIBRARY_PATH before setting environment in perl
export ERM_ROOT="/appl1/hpe/erm"
export ORACLE_HOME="/appl1/oracle/product/18.0.0.0/client"
export NLS_LANG="AMERICAN_AMERICA.TH8TISASCII"
export LD_LIBRARY_PATH="/usr/lib:${ERM_ROOT}/lib:${ORACLE_HOME}/lib:${ORACLE_HOME}"

$_SCRIPT_PATH/frm_ord_feed.pl 

