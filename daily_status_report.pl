#!/usr/bin/perl -w


# OUTSTANDING TASKS
# ------------------
# add support for --long-switches
# add a check for name resolution failure
# add a check to catch the situation when ping is responding, but SSH to Linux/AIX/xClarity is not working.  Create a hash element something like $blah{$key}{ssh} = "ok"


# CHANGE LOG
# -----------
# 2022-04-19	njeffrey	Script created
# 2022-04-21	njeffrey	Add support for reporting on the health status of Dell iDRAC service processors
# 2022-04-21	njeffrey	Add monitoring for EMC UniSphere (specifically DellEMC Compellent storage) via SNMP
# 2022-04-25	njeffrey	Add monitoring for Lenovo xClarity service processors via SSH 
# 2022-04-25	njeffrey	Add monitoring for Brocade fibre channel switches
# 2022-05-04	njeffrey	Add get_flashsystem_status subroutine
# 2022-05-04	njeffrey	Add get_fortigate_status subroutine
# 2022-05-06	njeffrey	Add columns to Lenovo xClarity output 
# 2022-05-06	njeffrey	Add Linux filesystem mount points /home /oracle /grid /db/backup /systembackup 
# 2022-05-06	njeffrey	Add monitoring for Hewlett Packard ILO4 service processor
# 2022-06-02	njeffrey	Add get_qnap_status subroutine
# 2022-06-02	njeffrey	Add 5 minute wait if the nagios-generated temporary files do not exist for FlashSystem and QNAP 
# 2022-05-06	njeffrey	Add Linux filesystem mount points /data
# 2022-06-16	njeffrey	Add get_ibm_imm2_status subroutine
# 2022-06-29    njeffrey        Add monitoring for IBM AIX hosts
# 2022-06-29    njeffrey        Add monitoring for IBM Hardware Management Console hosts
# 2022-06-29    njeffrey        Add monitoring for MikroTik SwOS hosts
# 2022-06-29    njeffrey        Add get_ciscoios_status subroutine
# 2022-06-29    njeffrey        Put site-specific details like emails and hostnames to a .cfg file
# 2022-07-05	njeffrey        Remove nagios performance data from report 
# 2022-07-07	njeffrey        Add NetApp ONTAP version to report
# 2022-07-09	njeffrey        Add local hostname to report output to tell user where the report came from 
# 2022-07-15	njeffrey        Add how-to instructions at bottom of report
# 2022-08-09	njeffrey        Add get_san_multipathing_linux subroutine
# 2022-10-03	njeffrey        Add check for HP SmartArray  RAID controller for HP ILO4 devices
# 2022-10-18	njeffrey        Add check for working SNMP on Linux and Windows hosts
# 2022-10-18	njeffrey        Add check for working SNMP on EMC Unispere, Dell iDRAC9, HP ILO, Brocade, NetApp Cisco IOS, MikroTik SwOS, FortiGate
# 2022-10-18	njeffrey        Add check for working SSH on Lenovo xClarity hosts
# 2022-11-27	njeffrey        Add SSH-based checks for Linux hosts
# 2022-11-27	njeffrey        Add SSH-based checks for Linux daemons by calling check_linux_daemons
# 2022-11-27	njeffrey        Add SSH-based checks for Oracle databases by calling check_oracle_instances
# 2023-03-31	njeffrey        Add column to Linux hosts output table showing status of non-root user accounts



# NOTES
# -----
# perl script to generate HTML report suitable for displaying on a web page or sending via email
# This report is designed to be used as a high-level validation that all hosts are up and healthy
# This script will report on the health of the following:
#  - Windows hosts                          (via SNMP)
#  - Linux hosts                            (via SNMP)
#  - Dell iDRAC8                            (via SSH)
#  - Dell iDRAC9                            (via SNMP)
#  - EMC UniSphere storage systems          (via SNMP)
#  - IBM xSeries IMM2 service processors    (via SNMP)
#  - Lenovo xClarity service processors     (via SSH)
#  - Brocade fibre channel switches         (via SNMP)
#  - IBM FlashSystem storage                (reads text file created by nagios running on same host)
#  - Hewlett Packard ILO4 service procssor  (via SNMP)
#  - QNAP NAS devices                       (via SNMP)
#  - AIX hosts                              (via SSH-based nagios checks)
#  - IBM Hardware Management Consoles       (reads text fiel created by nagios running on same host)
#  - MikroTik SwOS hosts                    (via SNMP-based nagios checks)
#  - NetApp ONTAP  hosts                    (via SNMP)
#

# ASSUMPTIONS
# -----------
# It is assumed that this script is run daily via cron from the nagios userid.  Example:
#    5 7 * * * /home/nagios/daily_check.pl >/dev/null 2>&1 #generate daily report of host health
# 
# It is assumed that all hosts will respond to ping, and health metrics can be retrieved either by SNMP or SSH
# 



use strict; 				#enforce good coding practices


#declare variables
my ($verbose,$cmd,$oid,$host,$snmpwalk,$snmpget,$ssh,$ping,$localhost,$monitoring_system_url);
my (@linux_hostnames,%linux_hosts,@windows_hostnames,%windows_hosts,@aix_hostnames,%aix_hosts,@hmc_hostnames,%hmc_hosts);                               #operating systems
my (@idrac8_hostnames,%idrac8_hosts,@idrac9_hostnames,%idrac9_hosts,@ibm_imm2_hostnames,%ibm_imm2_hosts,@xclarity_hostnames,%xclarity_hosts,@hpilo4_hostnames,%hpilo4_hosts);               #service processors
my (@brocade_hostnames,%brocade_hosts,@unisphere_hostnames,%unisphere_hosts,@flashsystem_hostnames,%flashsystem_hosts,@netapp_hostnames,%netapp_hosts,@qnap_hostnames,%qnap_hosts); #SAN storage
my (@ciscoios_hostnames,%ciscoios_hosts,@fortigate_hostnames,%fortigate_hosts,@mikrotik_swos_hostnames,%mikrotik_swos_hosts);                           #networking 
my (@san_multipath_linux_hostnames,%san_multipath_linux_hosts);
my ($key,$config_file,$output_file,$bgcolor,$fontcolor);
my ($to,$from,$subject,$sendmail);
my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst); 
my ($count,$drive_letter,@drive_letters,$mount_point,@mount_points);
my ($community,$community_linux,$community_windows,$community_netapp,$community_ciscoios,$community_fortigate);
my ($community_mikrotik_swos,$community_idrac9,$community_hpilo4,$community_brocade,$community_unisphere);

$verbose               = "yes";									#yes/no flag to increase verbosity for debugging
$ping                  = "/bin/ping";								#location of binary
$ssh                   = "/usr/bin/ssh";								#location of binary
$sendmail              = "/usr/sbin/sendmail"; 		 					#location of binary
$snmpget               = "/usr/bin/snmpget";							#location of binary
$snmpwalk              = "/usr/bin/snmpwalk";							#location of binary
$community             = "public";								#SNMP community name
$output_file           = "/home/nagios/daily_status_report.html";				#location of file
$config_file           = "/home/nagios/daily_status_report.cfg";					#location of file
$bgcolor               = "white";								#HTML background color
$localhost             = `hostname -s`;								#get the local hostname
$monitoring_system_url = "";									#initialize to avoid undef errors







sub sanity_checks {
   #
   print "running sanity_checks subroutine \n" if ($verbose eq "yes");
   #
   # confirm ping is available
   if( ! -f $ping) {
      print "ERROR - cannot locate $ping binary\n";
      exit; 											#exit script
   }                                            						#end of if block
   if( ! -x  $ping) {
      print "ERROR - $ping is not executable\n";
      exit; 											#exit script
   }                                            						#end of if block
   #
   # confirm ssh is available
   if( ! -f $ssh ) {
      print "ERROR - cannot locate $ssh binary\n";
      exit; 											#exit script
   }                                            						#end of if block
   if( ! -x  $ssh ) {
      print "ERROR - $ssh is not executable\n";
      exit; 											#exit script
   }                                            						#end of if block
   #
   # confirm snmpget is available
   if( ! -f $snmpget ) {
      print "ERROR - cannot locate $snmpget binary\n";
      exit; 											#exit script
   }                                            						#end of if block
   if( ! -x  $snmpget ) {
      print "ERROR - $snmpget is not executable\n";
      exit; 											#exit script
   }                                            						#end of if block
   #
   # confirm snmpwalk is available
   if( ! -f $snmpwalk ) {
      print "ERROR - Unknown - cannot locate $snmpwalk binary\n";
      exit; 											#exit script
   }                                            						#end of if block
   if( ! -x  $snmpwalk ) {
      print "ERROR - $snmpwalk is not executable\n";
      exit; 											#exit script
   }                                            						#end of if block
} 												#end of subroutine




sub read_config_file {
   #
   print "running read_config_file subroutine \n" if ($verbose eq "yes");
   #
   if ( ! -f "$config_file" ) {									#confirm the config file exists
      print "ERROR: cannot find config file $config_file - exiting script \n";
      exit;
   } 												#end of if block
   if ( -z "$config_file" ) {									#confirm the config file is larger than zero bytes
      print "ERROR: config file $config_file is zero size - exiting script \n";
      exit;
   } 												#end of if block
   print "   opening config file $config_file for reading \n" if ($verbose eq "yes");
   open(IN,"$config_file") or die "Cannot read config file $config_file $! \n"; 		#open file for reading
   while (<IN>) {                                                                            	#read a line from the command output
      #
      # email address details 
      #
      $to                    = $1              if (/^to=([a-zA-Z0-9,_\-\@\.]+)/);		#find line in config file
      $from                  = $1              if (/^from=([a-zA-Z0-9_\-\@\.]+)/);		#find line in config file
      $subject               = $1              if (/^subject=([a-zA-Z0-9 _\-\@]+)/);		#find line in config file
      #
      # URL of monitoring system (nagios, PRTG, etc)
      #
      $monitoring_system_url = $1              if (/^monitoring_system_url=([a-zA-Z0-9:,_\-\/\.]+)/);		#find line in config file
      #
      # device hostnames
      #
      @aix_hostnames                 = split(',' , $1) if (/^aix_hostnames=([a-zA-Z0-9,_\-\.]+)/);	#find line in config file
      @hmc_hostnames                 = split(',' , $1) if (/^hmc_hostnames=([a-zA-Z0-9,_\-\.]+)/);	#find line in config file
      @linux_hostnames               = split(',' , $1) if (/^linux_hostnames=([a-zA-Z0-9,_\-\.]+)/);	#find line in config file
      @san_multipath_linux_hostnames = split(',' , $1) if (/^san_multipath_linux_hostnames=([a-zA-Z0-9,_\-\.]+)/);	#find line in config file
      @windows_hostnames             = split(',' , $1) if (/^windows_hostnames=([a-zA-Z0-9,_\-\.]+)/);  #find line in config file
      @xclarity_hostnames            = split(',' , $1) if (/^xclarity_hostnames=([a-zA-Z0-9,_\-\.]+)/);	#find line in config file
      @ibm_imm2_hostnames            = split(',' , $1) if (/^ibm_imm2_hostnames=([a-zA-Z0-9,_\-\.]+)/);	#find line in config file
      @hpilo4_hostnames              = split(',' , $1) if (/^hpilo4_hostnames=([a-zA-Z0-9,_\-\.]+)/);  	#find line in config file
      @brocade_hostnames             = split(',' , $1) if (/^brocade_hostnames=([a-zA-Z0-9,_\-\.]+)/); 	#find line in config file
      @flashsystem_hostnames         = split(',' , $1) if (/^flashsystem_hostnames=([a-zA-Z0-9,_\-\.]+)/); #find line in config file
      @unisphere_hostnames           = split(',' , $1) if (/^unisphere_hostnames=([a-zA-Z0-9,_\-\.]+)/);#find line in config file
      @idrac8_hostnames              = split(',' , $1) if (/^idrac8_hostnames=([a-zA-Z0-9,_\-\.]+)/);	#find line in config file
      @idrac9_hostnames              = split(',' , $1) if (/^idrac9_hostnames=([a-zA-Z0-9,_\-\.]+)/);	#find line in config file
      @qnap_hostnames                = split(',' , $1) if (/^qnap_hostnames=([a-zA-Z0-9,_\-\.]+)/);  	#find line in config file
      @netapp_hostnames              = split(',' , $1) if (/^netapp_hostnames=([a-zA-Z0-9,_\-\.]+)/);  	#find line in config file
      #
      # SNMP community strings
      #
      $community               = $1 if (/^community=(\S+)/);					#find line in config file \S refers to any non-whitespace character
      $community_linux         = $1 if (/^community_linux=(\S+)/);				#find line in config file
      $community_windows       = $1 if (/^community_windows=(\S+)/);				#find line in config file
      $community_netapp        = $1 if (/^community_netapp=(\S+)/);				#find line in config file
      $community_ciscoios      = $1 if (/^community_ciscoios=(\S+)/);				#find line in config file
      $community_fortigate     = $1 if (/^community_fortigate=(\S+)/);				#find line in config file
      $community_mikrotik_swos = $1 if (/^community_mikrotik_swos=(\S+)/);			#find line in config file
      $community_idrac9        = $1 if (/^community_idrac9=(\S+)/);				#find line in config file
      $community_hpilo4        = $1 if (/^community_hpilo4=(\S+)/);				#find line in config file
      $community_brocade       = $1 if (/^community_brocade=(\S+)/);				#find line in config file
      $community_unisphere     = $1 if (/^community_unisphere=(\S+)/);				#find line in config file
   }                                                                                         	#end of while loop
   close IN;                                                                                 	#close filehandle
   #
   # check to see if to/from/subject are populated
   #
   unless(defined($to)) {
      print "ERROR: Could not find line similar to to=helpdesk\@example.com in config file $config_file \n";
      exit;
   }												#end of unless block
   unless(defined($from)) {
      print "ERROR: Could not find line similar to from=alerts\@example.com in config file $config_file \n";
      exit;
   }												#end of unless block
   unless(defined($subject)) {
      print "ERROR: Could not find line similar to subject=BigCorp daily status check in config file $config_file \n";
      exit;
   }												#end of unless block
   print "   to:$to  from:$from  subject:$subject \n" if ($verbose eq "yes");
} 												#end of subroutine




sub get_date {
   #
   print "running get_date subroutine \n" if ($verbose eq "yes");
   #
   ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime(time);
   $year = $year + 1900;									#$year is actually years since 1900
   $mon  = $mon + 1;										#months are numbered from 0 to 11
   $mon  = "0$mon"  if ($mon  < 10);								#add leading zero if required
   $mday = "0$mday" if ($mday < 10);								#add leading zero if required
   $hour = "0$hour" if ($hour < 10);								#add leading zero if required
   $min  = "0$min"  if ($min  < 10);								#add leading zero if required
   #
   print "   current time is $year-$mon-$mday $hour:$min \n" if ($verbose eq "yes");
} 												#end of subroutine




sub define_hosts {
   #
   print "running define_hosts subroutine \n" if ($verbose eq "yes");
   #
   # build a hash for all linux hostnames we want to check
   #
   foreach $host (@linux_hostnames) {
      $linux_hosts{$host}{hostname} = $host;							#initialize hash element
      $linux_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $linux_hosts{$host}{ssh}      = "unknown";						#initialize hash element
      $linux_hosts{$host}{snmp}     = "unknown";						#initialize hash element
      print "      found linux hostname $linux_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   # build a hash for all bare-metal linux hostnames with iSCSI or Fibre Channel SAN paths
   # Please note that this section is only for physical Linux boxes with SAN storage, not virtual machines.
   #
   foreach $host (@san_multipath_linux_hostnames) {
      $san_multipath_linux_hosts{$host}{hostname} = $host;					#initialize hash element
      $san_multipath_linux_hosts{$host}{ping}     = "unknown";					#initialize hash element
      print "      found linux hostname $linux_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   #
   # build a hash for all windows hostnames we want to check
   #
   foreach $host (@windows_hostnames) {
      $windows_hosts{$host}{hostname} = $host;							#initialize hash element
      $windows_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $windows_hosts{$host}{snmp}     = "unknown";						#initialize hash element
      print "      found windows hostname $windows_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all Dell iDRAC8 service processor hostnames we want to check
   #
   foreach $host (@idrac8_hostnames) {
      $idrac8_hosts{$host}{hostname} = $host;							#initialize hash element
      $idrac8_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $idrac8_hosts{$host}{cpu_load} = 0;							#initialize hash element
      print "      found iDRAC hostname $idrac8_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all Dell iDRAC9 service processor hostnames we want to check
   #
   foreach $host (@idrac9_hostnames) {
      $idrac9_hosts{$host}{hostname} = $host;							#initialize hash element
      $idrac9_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $idrac9_hosts{$host}{cpu_load} = 0;							#initialize hash element
      print "      found iDRAC hostname $idrac9_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all DellEMC UniSphere storage manager hostnames we want to check
   #
   foreach $host (@unisphere_hostnames) {
      $unisphere_hosts{$host}{hostname} = $host;							#initialize hash element
      $unisphere_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $unisphere_hosts{$host}{cpu_load} = 0;							#initialize hash element
      print "      found UniSphere hostname $unisphere_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all IBM xSeries IMM2 service processor hostnames we want to check
   #
   foreach $host (@ibm_imm2_hostnames) {
      $ibm_imm2_hosts{$host}{hostname} = $host;							#initialize hash element
      $ibm_imm2_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $ibm_imm2_hosts{$host}{cpu_load} = 0;							#initialize hash element
      print "      found IBM xSeries IMM2 hostname $ibm_imm2_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all Lenovo xClarity service processor hostnames we want to check
   #
   foreach $host (@xclarity_hostnames) {
      $xclarity_hosts{$host}{hostname} = $host;							#initialize hash element
      $xclarity_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $xclarity_hosts{$host}{cpu_load} = 0;							#initialize hash element
      print "      found xClarity hostname $xclarity_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all Brocade fibre channel switch hostnames we want to check
   #
   foreach $host (@brocade_hostnames) {
      $brocade_hosts{$host}{hostname} = $host;							#initialize hash element
      $brocade_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $brocade_hosts{$host}{cpu_load} = 0;							#initialize hash element
      print "      found Brocade hostname $brocade_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all FlashSystem storage hostnames we want to check
   #
   foreach $host (@flashsystem_hostnames) {
      $flashsystem_hosts{$host}{hostname} = $host;						#initialize hash element
      $flashsystem_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $flashsystem_hosts{$host}{cpu_load} = 0;							#initialize hash element
      print "      found FlashSystem hostname $flashsystem_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all QNAP NAS hostnames we want to check
   #
   foreach $host (@qnap_hostnames) {
      $qnap_hosts{$host}{hostname} = $host;						#initialize hash element
      $qnap_hosts{$host}{ping}     = "unknown";						#initialize hash element
      $qnap_hosts{$host}{cpu_load} = 0;							#initialize hash element
      print "      found qnap hostname $qnap_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all FortiGate firewall hostnames we want to check
   #
   foreach $host (@fortigate_hostnames) {
      $fortigate_hosts{$host}{hostname}       = $host;						#initialize hash element
      $fortigate_hosts{$host}{ping}           = "unknown";					#initialize hash element
      $fortigate_hosts{$host}{cpu_util}       = 0;						#initialize hash element
      $fortigate_hosts{$host}{ram_util}       = 0;						#initialize hash element
      $fortigate_hosts{$host}{bandwidth_kbps} = 0;						#initialize hash element
      $fortigate_hosts{$host}{bandwidth_mbps} = 0;						#initialize hash element
      print "      found fortigate hostname $fortigate_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all HP ILO4 hostnames we want to check
   #
   foreach $host (@hpilo4_hostnames) {
      $hpilo4_hosts{$host}{hostname}       = $host;						#initialize hash element
      $hpilo4_hosts{$host}{ping}           = "unknown";					#initialize hash element
      $hpilo4_hosts{$host}{cpu_util}       = 0;						#initialize hash element
      $hpilo4_hosts{$host}{ram_util}       = 0;						#initialize hash element
      $hpilo4_hosts{$host}{bandwidth_kbps} = 0;						#initialize hash element
      $hpilo4_hosts{$host}{bandwidth_mbps} = 0;						#initialize hash element
      print "      found hpilo4 hostname $hpilo4_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }												#end of foreach loop
   #
   # build a hash for all IBM AIX hostnames we want to check
   #
   foreach $host (@aix_hostnames) {
      $aix_hosts{$host}{hostname}       = $host;                                                #initialize hash element
      $aix_hosts{$host}{ping}           = "unknown";                                            #initialize hash element
      $aix_hosts{$host}{cpu}            = "unknown";                                            #initialize hash element
      $aix_hosts{$host}{paging}         = "unknown";                                            #initialize hash element
      $aix_hosts{$host}{errpt}          = "unknown";                                            #initialize hash element
      print "      found aix hostname $aix_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }                                                                                            #end of foreach loop
   #
   # build a hash for all IBM Hardware Management Console hostnames we want to check
   #
   foreach $host (@hmc_hostnames) {
      $hmc_hosts{$host}{hostname}       = $host;                                                #initialize hash element
      $hmc_hosts{$host}{ping}           = "unknown";                                            #initialize hash element
      $hmc_hosts{$host}{health}         = "unknown";                                            #initialize hash element
      print "      found hmc hostname $hmc_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }                                                                                            #end of foreach loop
   #
   # build a hash for all Mikrotik devices running the SwOS operating system
   #
   foreach $host (@mikrotik_swos_hostnames) {
      $mikrotik_swos_hosts{$host}{hostname}       = $host;                                      #initialize hash element
      $mikrotik_swos_hosts{$host}{ping}           = "unknown";                                  #initialize hash element
      $mikrotik_swos_hosts{$host}{health}         = "unknown";                                  #initialize hash element
      print "      found MikroTik SwOS hostname $mikrotik_swos_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }                                                                                            #end of foreach loop
   #
   # build a hash for all NetApp ONTAP storage systems
   #
   foreach $host (@netapp_hostnames) {
      $netapp_hosts{$host}{hostname}       = $host;                                             #initialize hash element
      $netapp_hosts{$host}{ping}           = "unknown";                                         #initialize hash element
      $netapp_hosts{$host}{health}         = "unknown";                                         #initialize hash element
      print "      found netapp hostname $netapp_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }                                                                                            #end of foreach loop
   #
   # build a hash for all Cisco IOS network devices
   #
   foreach $host (@ciscoios_hostnames) {
      $ciscoios_hosts{$host}{hostname}       = $host;                                           #initialize hash element
      $ciscoios_hosts{$host}{ping}           = "unknown";                                       #initialize hash element
      $ciscoios_hosts{$host}{health}         = "unknown";                                       #initialize hash element
      print "      found ciscoios hostname $ciscoios_hosts{$host}{hostname} \n" if ($verbose eq "yes");
   }                                                                                            #end of foreach loop
} 												#end of subroutine




sub ping_hosts {
   #
   print "running ping_hosts subroutine \n" if ($verbose eq "yes");
   #
   # ping all the linux hosts
   #
   foreach $key (sort keys %linux_hosts) {
      $cmd = "$ping -c 1 $linux_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                      		 	#read a line from the command output
         $linux_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 				#look for ping reply
         $linux_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 				#look for ping reply
      }                                                                    			#end of while loop
      print "      $linux_hosts{$key}{hostname} ping status is $linux_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                          		  	#close filehandle
   } 												#end of foreach loop
   # ping all the bare-metal linux hosts with SAN storage
   #
   foreach $key (sort keys %san_multipath_linux_hosts) {
      $cmd = "$ping -c 1 $san_multipath_linux_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                      		 	#read a line from the command output
         $san_multipath_linux_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 		#look for ping reply
         $san_multipath_linux_hosts{$key}{ping} = "down" if ( /100\% packet loss/ );		#look for ping reply
      }                                                                    			#end of while loop
      print "      $san_multipath_linux_hosts{$key}{hostname} ping status is $san_multipath_linux_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                          		  	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the windows hosts
   #
   foreach $key (sort keys %windows_hosts) {
      $cmd = "$ping -c 1 $windows_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                       			#read a line from the command output
         $windows_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $windows_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                    			#end of while loop
      print "      $windows_hosts{$key}{hostname} ping status is $windows_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                            			#close filehandle
   } 												#end of foreach loop
   #
   # ping all the Dell iDRAC8 service processor hosts
   #
   foreach $key (sort keys %idrac8_hosts) {
      $cmd = "$ping -c 1 $idrac8_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $idrac8_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $idrac8_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $idrac8_hosts{$key}{hostname} ping status is $idrac8_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the Dell iDRAC9 service processor hosts
   #
   foreach $key (sort keys %idrac9_hosts) {
      $cmd = "$ping -c 1 $idrac9_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $idrac9_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $idrac9_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $idrac9_hosts{$key}{hostname} ping status is $idrac9_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the DellEMC Unisphere hosts
   #
   foreach $key (sort keys %unisphere_hosts) {
      $cmd = "$ping -c 1 $unisphere_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $unisphere_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $unisphere_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $unisphere_hosts{$key}{hostname} ping status is $unisphere_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the IBM xSeries IMM2 service processor hosts
   #
   foreach $key (sort keys %ibm_imm2_hosts) {
      $cmd = "$ping -c 1 $ibm_imm2_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $ibm_imm2_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $ibm_imm2_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $ibm_imm2_hosts{$key}{hostname} ping status is $ibm_imm2_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the Lenovo xClarity service processor hosts
   #
   foreach $key (sort keys %xclarity_hosts) {
      $cmd = "$ping -c 1 $xclarity_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $xclarity_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $xclarity_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $xclarity_hosts{$key}{hostname} ping status is $xclarity_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the Brocade fibre channel switch hosts
   #
   foreach $key (sort keys %brocade_hosts) {
      $cmd = "$ping -c 1 $brocade_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $brocade_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $brocade_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $brocade_hosts{$key}{hostname} ping status is $brocade_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the FlashSystem hosts
   #
   foreach $key (sort keys %flashsystem_hosts) {
      $cmd = "$ping -c 1 $flashsystem_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $flashsystem_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $flashsystem_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $flashsystem_hosts{$key}{hostname} ping status is $flashsystem_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the qnap hosts
   #
   foreach $key (sort keys %qnap_hosts) {
      $cmd = "$ping -c 1 $qnap_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $qnap_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $qnap_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $qnap_hosts{$key}{hostname} ping status is $qnap_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the fortigate hosts
   #
   foreach $key (sort keys %fortigate_hosts) {
      $cmd = "$ping -c 1 $fortigate_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $fortigate_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $fortigate_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $fortigate_hosts{$key}{hostname} ping status is $fortigate_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the Hewlett Packard ILO4 service processor hosts
   #
   foreach $key (sort keys %hpilo4_hosts) {
      $cmd = "$ping -c 1 $hpilo4_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                              			#run command
      while (<IN>) {                                                   			    	#read a line from the command output
         $hpilo4_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  ); 			#look for ping reply
         $hpilo4_hosts{$key}{ping} = "down" if ( /100\% packet loss/ ); 			#look for ping reply
      }                                                                			    	#end of while loop
      print "      $hpilo4_hosts{$key}{hostname} ping status is $hpilo4_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                      			      	#close filehandle
   } 												#end of foreach loop
   #
   # ping all the IBM AIX hosts
   #
   foreach $key (sort keys %aix_hosts) {
      $cmd = "$ping -c 1 $aix_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                                                   #run command
      while (<IN>) {                                                                            #read a line from the command output
         $aix_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  );                    #look for ping reply
         $aix_hosts{$key}{ping} = "down" if ( /100\% packet loss/ );                    #look for ping reply
      }                                                                                         #end of while loop
      print "      $aix_hosts{$key}{hostname} ping status is $aix_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
   }                                                                                            #end of foreach loop
   #
   # ping all the IBM Hardware Management Console hosts
   #
   foreach $key (sort keys %hmc_hosts) {
      $cmd = "$ping -c 1 $hmc_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                                                   #run command
      while (<IN>) {                                                                            #read a line from the command output
         $hmc_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  );                    #look for ping reply
         $hmc_hosts{$key}{ping} = "down" if ( /100\% packet loss/ );                    #look for ping reply
      }                                                                                         #end of while loop
      print "      $hmc_hosts{$key}{hostname} ping status is $hmc_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
   }                                                                                            #end of foreach loop
   #
   # ping all the MikroTik SwOS hosts
   #
   foreach $key (sort keys %mikrotik_swos_hosts) {
      $cmd = "$ping -c 1 $mikrotik_swos_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                                                   #run command
      while (<IN>) {                                                                            #read a line from the command output
         $mikrotik_swos_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  );                  #look for ping reply
         $mikrotik_swos_hosts{$key}{ping} = "down" if ( /100\% packet loss/ );                  #look for ping reply
      }                                                                                         #end of while loop
      print "      $mikrotik_swos_hosts{$key}{hostname} ping status is $mikrotik_swos_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
   }                                                                                            #end of foreach loop
   #
   # ping all the NetApp ONTAP  hosts
   #
   foreach $key (sort keys %netapp_hosts) {
      $cmd = "$ping -c 1 $netapp_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                                                   #run command
      while (<IN>) {                                                                            #read a line from the command output
         $netapp_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  );                         #look for ping reply
         $netapp_hosts{$key}{ping} = "down" if ( /100\% packet loss/ );                         #look for ping reply
      }                                                                                         #end of while loop
      print "      $netapp_hosts{$key}{hostname} ping status is $netapp_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
   }                                                                                            #end of foreach loop
   #
   # ping all the Cisco IOS hosts
   #
   foreach $key (sort keys %ciscoios_hosts) {
      $cmd = "$ping -c 1 $ciscoios_hosts{$key}{hostname}";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                                                   #run command
      while (<IN>) {                                                                            #read a line from the command output
         $ciscoios_hosts{$key}{ping} = "up"   if ( / 0\% packet loss/  );                       #look for ping reply
         $ciscoios_hosts{$key}{ping} = "down" if ( /100\% packet loss/ );                       #look for ping reply
      }                                                                                         #end of while loop
      print "      $ciscoios_hosts{$key}{hostname} ping status is $ciscoios_hosts{$key}{ping} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
   }                                                                                            #end of foreach loop
} 												#end of subroutine




sub verify_os_linux {
   #
   print "running verify_os_linux subroutine \n" if ($verbose eq "yes");
   #
   # this subroutine runs to confirm that the contents of the @linux_hosts array really does contain Linux hosts, but performing an SNMP query to verify the operating system
   #
   # query all the linux hosts to confirm the operating system reported by SNMP 
   #
   $community = $community_linux;                                            			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %linux_hosts) {
      #
      # .1.3.6.1.2.1.1.1.0 HOST-RESOURCES-MIB::hrSysDescr
      #  
      # Command output will look similar to the following:
      #    $ /usr/bin/snmpwalk  -v 1 -c public linserv01 .1.3.6.1.2.1.1.1.0
      #    SNMPv2-MIB::sysDescr.0 = STRING: Linux linserv011.example.com 3.10.0-1160.62.1.el7.x86_64 #1 SMP Tue Apr 5 16:57:59 UTC 2022 x86_64
      #
      #    $ /usr/bin/snmpwalk  -v 1 -c public winserv01 .1.3.6.1.2.1.1.1.0
      #    SNMPv2-MIB::sysDescr.0 = STRING: Hardware: Intel64 Family 6 Model 86 Stepping 2 AT/AT COMPATIBLE - Software: Windows Version 6.3 (Build 17763 Multiprocessor Free)
      #
      #
      #
      $linux_hosts{$key}{os}   = "unknown";							#initialize hash element
      $linux_hosts{$key}{snmp} = "unknown";   							#initialize hash element
      next unless ( $linux_hosts{$key}{ping} eq "up" );						#skip hosts that do not respond to ping
      $oid = ".1.3.6.1.2.1.1.1.0";								#SNMP OID for hrProcessorLoad
      $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                 			          	#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( /Linux/ ) {									#look for operating system type in sysDescr
            $linux_hosts{$key}{os}   = "Linux";  						#define operating system
            $linux_hosts{$key}{snmp} = "ok";   							#this also confirms we have working SNMP
         }
         if ( /Windows/ ) {									#look for operating system type in sysDescr
            $linux_hosts{$key}{os}   = "Windows";						#define operating system
            $linux_hosts{$key}{snmp} = "ok";  							#this also confirms we have working SNMP
         }
      }                                                                				#end of while loop
      close IN;                                                        			 	#close filehandle
      print "   host:$linux_hosts{$key}{hostname} OS:$linux_hosts{$key}{os}  \n" if ($verbose eq "yes");
   } 												#end of foreach loop
} 												#end of subroutine



sub verify_os_windows {
   #
   print "running verify_os_windows subroutine \n" if ($verbose eq "yes");
   #
   # this subroutine runs to confirm that the contents of the @windows_hosts array really does contain Windows hosts, but performing an SNMP query to verify the operating system
   #
   # query all the windows hosts to confirm the operating system reported by SNMP 
   #
   $community = $community_windows;                                            			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %windows_hosts) {
      #
      # .1.3.6.1.2.1.1.1.0 HOST-RESOURCES-MIB::hrSysDescr
      #  
      # Command output will look similar to the following:
      #    $ /usr/bin/snmpwalk  -v 1 -c public linserv01 .1.3.6.1.2.1.1.1.0
      #    SNMPv2-MIB::sysDescr.0 = STRING: Linux linserv011.example.com 3.10.0-1160.62.1.el7.x86_64 #1 SMP Tue Apr 5 16:57:59 UTC 2022 x86_64
      #
      #    $ /usr/bin/snmpwalk  -v 1 -c public winserv01 .1.3.6.1.2.1.1.1.0
      #    SNMPv2-MIB::sysDescr.0 = STRING: Hardware: Intel64 Family 6 Model 86 Stepping 2 AT/AT COMPATIBLE - Software: Windows Version 6.3 (Build 17763 Multiprocessor Free)
      #
      #
      #
      $windows_hosts{$key}{os}   = "unknown";							#initialize hash element
      $windows_hosts{$key}{snmp} = "unknown";  							#initialize hash element
      next unless ( $windows_hosts{$key}{ping} eq "up" );					#skip hosts that do not respond to ping
      $oid = ".1.3.6.1.2.1.1.1.0";								#SNMP OID for hrProcessorLoad
      $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                 			          	#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( /Linux/ ) {									#look for operating system type in sysDescr
            $windows_hosts{$key}{os}   = "Linux";  						#define operating system
            $windows_hosts{$key}{snmp} = "ok";  						#this also confirms we have working SNMP
         }
         if ( /Windows/ ) {									#look for operating system type in sysDescr
            $windows_hosts{$key}{os}   = "Windows";						#define operating system
            $windows_hosts{$key}{snmp} = "ok";  						#this also confirms we have working SNMP
         }
      }                                                                				#end of while loop
      close IN;                                                        			 	#close filehandle
      print "   host:$windows_hosts{$key}{hostname} OS:$windows_hosts{$key}{os}  \n" if ($verbose eq "yes");
   } 												#end of foreach loop
} 												#end of subroutine





sub get_cpu_util_linux {
   #
   print "running get_cpu_linux subroutine \n" if ($verbose eq "yes");
   #
   # get the CPU utilization for linux hosts
   #
   $community = $community_linux;                                              			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %linux_hosts) {
      #
      # There may be multiple processors, so you will need to capture the load on all processors then average them.
      # Sample output:
      # $snmpwalk -v 1 -c public hyperv1 .1.3.6.1.2.1.25.3.3
      # HOST-RESOURCES-MIB::hrProcessorLoad.3 = INTEGER: 0
      # HOST-RESOURCES-MIB::hrProcessorLoad.4 = INTEGER: 0
      # HOST-RESOURCES-MIB::hrProcessorLoad.5 = INTEGER: 0
      # HOST-RESOURCES-MIB::hrProcessorLoad.6 = INTEGER: 0
      #
      $linux_hosts{$key}{cpu_load} = 0;								#initialize value to avoid undef errors
      next unless ( $linux_hosts{$key}{ping} eq "up" );						#skip hosts that do not respond to ping
      $count = 0;										#initialize counter variable
      $oid = ".1.3.6.1.2.1.25.3.3.1.2";								#SNMP OID for hrProcessorLoad
      $cmd = "$snmpwalk -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get CPU util on $linux_hosts{$key}{hostname}: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                  	         			#open filehandle using command output
      while (<IN>) {                                           	        	 		#read a line from the command output
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the load for this particular processor
            $count++;										#increment counter 
            $linux_hosts{$key}{cpu_load}+=$1;                         				#add the current reading to assign value to hash
            print "      processor:$count cpu_load:$1 \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      next unless ( $count > 0 );								#skip to next host if cpu count is zero, avoid divide by zero error
      $linux_hosts{$key}{cpu_load} += 1 if ($linux_hosts{$key}{cpu_load} == 0);			#if cpu load is zero, just add 1 to avoid a divide by zero error
      $linux_hosts{$key}{cpu_load} = $linux_hosts{$key}{cpu_load} / $count;  			#calculate average CPU load across all processors
      $linux_hosts{$key}{cpu_load} = sprintf("%.0f", $linux_hosts{$key}{cpu_load});  		#truncate to zero decimal places
      print "      average cpu_load:$linux_hosts{$key}{cpu_load}\% \n" if ($verbose eq "yes");
   } 												#end of foreach loop
} 												#end of subroutine



sub get_cpu_util_windows {
   #
   print "running get_cpu_windows subroutine \n" if ($verbose eq "yes");
   #
   # get the CPU utilization for windows hosts
   #
   $community = $community_windows;                                            			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %windows_hosts) {
      #
      # There may be multiple processors, so you will need to capture the load on all processors then average them.
      # Sample output:
      # $snmpwalk -v 1 -c public hyperv1 .1.3.6.1.2.1.25.3.3
      # HOST-RESOURCES-MIB::hrProcessorLoad.3 = INTEGER: 0
      # HOST-RESOURCES-MIB::hrProcessorLoad.4 = INTEGER: 0
      # HOST-RESOURCES-MIB::hrProcessorLoad.5 = INTEGER: 0
      # HOST-RESOURCES-MIB::hrProcessorLoad.6 = INTEGER: 0
      #
      $windows_hosts{$key}{cpu_load} = 0;							#initialize value to avoid undef errors
      next unless ( $windows_hosts{$key}{ping} eq "up" );					#skip hosts that do not respond to ping
      $count = 0;										#initialize counter variable
      $oid = ".1.3.6.1.2.1.25.3.3.1.2";								#SNMP OID for hrProcessorLoad
      $cmd = "$snmpwalk -v 1 -c $community $windows_hosts{$key}{hostname} $oid";		#define command to be run
      print "   running command to get CPU util on $windows_hosts{$key}{hostname}: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the load for this particular processor
            $count++;										#increment counter 
            $windows_hosts{$key}{cpu_load}+=$1;                         			#add the current reading to assign value to hash
            print "      processor:$count cpu_load:$1 \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      next unless ( $count > 0 );								#skip to next host if cpu count is zero, avoid divide by zero error
      $windows_hosts{$key}{cpu_load} += 1 if ($windows_hosts{$key}{cpu_load} == 0);		#if cpu load is zero, just add 1 to avoid a divide by zero error
      $windows_hosts{$key}{cpu_load} = $windows_hosts{$key}{cpu_load} / $count;  		#calculate average CPU load across all processors
      $windows_hosts{$key}{cpu_load} = sprintf("%.0f", $windows_hosts{$key}{cpu_load});  	#truncate to zero decimal places
      print "      average cpu_load:$windows_hosts{$key}{cpu_load}\% \n" if ($verbose eq "yes");
   } 												#end of foreach loop
} 												#end of subroutine






sub get_ram_util_linux {
   #
   print "running get_ram_util_linux subroutine \n" if ($verbose eq "yes");
   #
   #
   # get RAM details
   #
   # .1.3.6.1.2.1.25.2.3.1     hrStorageTable
   # .1.3.6.1.2.1.25.2.3.1.1   hrStorageTable.hrStorageIndex
   # .1.3.6.1.2.1.25.2.3.1.2   hrStorageTable.hrStorageType
   # .1.3.6.1.2.1.25.2.3.1.3   hrStorageTable.hrStorageDescr
   # .1.3.6.1.2.1.25.2.3.1.4   hrStorageTable.hrStorageAllocationUnits
   # .1.3.6.1.2.1.25.2.3.1.5   hrStorageTable.hrStorageSize
   # .1.3.6.1.2.1.25.2.3.1.6   hrStorageTable.hrStorageUsed
   # .1.3.6.1.2.1.25.2.3.1.7   hrStorageTable.hrStorageAllocationFailures
   #
   #
   # Sample command output:
   # $  snmpwalk   -v 1 -c public hyperv1 .1.3.6.1.2.1.25.2.3.1
   # HOST-RESOURCES-MIB::hrStorageIndex.1 = INTEGER: 1
   # HOST-RESOURCES-MIB::hrStorageIndex.2 = INTEGER: 2
   # HOST-RESOURCES-MIB::hrStorageIndex.3 = INTEGER: 3
   # HOST-RESOURCES-MIB::hrStorageIndex.4 = INTEGER: 4                                              	<---- this is the index that correponds to RAM (may vary by host)
   # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory
   # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam                  	<---- we are interested in RAM
   # HOST-RESOURCES-MIB::hrStorageDescr.1 = STRING: C:\\ Label:  Serial Number e6a835e
   # HOST-RESOURCES-MIB::hrStorageDescr.2 = STRING: D:\\ Label:hyperv1-d  Serial Number f2384eee
   # HOST-RESOURCES-MIB::hrStorageDescr.3 = STRING: Virtual Memory
   # HOST-RESOURCES-MIB::hrStorageDescr.4 = STRING: Physical Memory                                 	<---- description
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.1 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.2 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.3 = INTEGER: 65536 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes                          	<---- size of each allocation unit
   # HOST-RESOURCES-MIB::hrStorageSize.1 = INTEGER: 244049407	                               
   # HOST-RESOURCES-MIB::hrStorageSize.2 = INTEGER: 1953497088
   # HOST-RESOURCES-MIB::hrStorageSize.3 = INTEGER: 600459
   # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635                                	<---- total number of allocation units (multiple by above to get size in bytes)
   # HOST-RESOURCES-MIB::hrStorageUsed.1 = INTEGER: 85040189
   # HOST-RESOURCES-MIB::hrStorageUsed.2 = INTEGER: 1571142078
   # HOST-RESOURCES-MIB::hrStorageUsed.3 = INTEGER: 256187
   # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 263060 					<--- number of used allocation units (multiple by size to get used bytes)
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.1 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.2 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.3 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.4 = Counter32: 0  				<---- should always be zero
   #
   #
   $community = $community_linux;                                            			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %linux_hosts) {
      #
      next unless ( $linux_hosts{$key}{ping} eq "up" );						#skip hosts that do not respond to ping
      $oid = ".1.3.6.1.2.1.25.2.3.1";								#SNMP OID for hrStorageTable
      $cmd = "$snmpwalk -v 1 -c $community $linux_hosts{$key}{hostname} $oid.2";		#search through the hrStorageType to find hrStorageRam
      print "   running command to get RAM util on $linux_hosts{$key}{hostname}: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.2
         # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory
         # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam             <--- figure out the index number from this description
         #
         if ( /hrStorageType.([0-9]+) = OID: HOST-RESOURCES-TYPES::hrStorageRam/ ) {    					#find the load for this particular processor
            $linux_hosts{$key}{ram}{hrStorageIndex} = $1;	                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            print "      host:$linux_hosts{$key}{hostname}  hrStorageIndex:$linux_hosts{$key}{ram}{hrStorageIndex} \n" if ($verbose eq "yes");
         }											#end of if block
      }                                                                				#end of while loop
      close IN;                                                        			 	#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageAllocationUnits
      #
      next unless ($linux_hosts{$key}{ram}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.4.$linux_hosts{$key}{ram}{hrStorageIndex}";			#SNMP OID for       hrStorageTable.hrStorageAllocationUnits.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageAllocationUnits.IndexNumber
      print "   running command to check RAM hrStorageAllocationUnits on $linux_hosts{$key}{hostname}: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.4.X
         # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes
         #
         if ( /INTEGER: ([0-9]+) Bytes/ ) {    							#find the size of each allocation unit
            $linux_hosts{$key}{ram}{hrStorageAllocationUnits} = $1;				#value for hrStorageTable.hrStorageAllocationUnits.IndexNumber
            print "      host:$linux_hosts{$key}{hostname} hrStorageAllocationUnits:$1 \n" if ($verbose eq "yes");
         }											#end of if block
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageSize
      #
      next unless ($linux_hosts{$key}{ram}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.5.$linux_hosts{$key}{ram}{hrStorageIndex}";			#SNMP OID for       hrStorageTable.hrStorageSize.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageSize.IndexNumber
      print "   running command to check RAM hrStorageSize on $linux_hosts{$key}{hostname}: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.5.X
         # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635
         #
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the value
            $linux_hosts{$key}{ram}{hrStorageSize} = $1;					#value for hrStorageTable.hrStorageSize.IndexNumber
            $linux_hosts{$key}{ram}{hrStorageSize_GB} = sprintf("%.1f", $linux_hosts{$key}{ram}{hrStorageAllocationUnits}*$linux_hosts{$key}{ram}{hrStorageSize}/1024/1024/1024); #convert to GB
            print "      host:$linux_hosts{$key}{hostname} hrStorageSize:$linux_hosts{$key}{ram}{hrStorageSize_GB}GB \n" if ($verbose eq "yes")
         }                                                             				#end of if block
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageUsed 
      #
      next unless ($linux_hosts{$key}{ram}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.6.$linux_hosts{$key}{ram}{hrStorageIndex}";			#SNMP OID for       hrStorageTable.hrStorageUsed.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageUsed.IndexNumber
      print "   running command to check RAM hrStorageUsed: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.6.X
         # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 261948
         #
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the value 
            $linux_hosts{$key}{ram}{hrStorageUsed} = $1;					#value for hrStorageTable.hrStorageUsed.IndexNumber
            $linux_hosts{$key}{ram}{hrStorageUsed_GB} = sprintf("%.1f", $linux_hosts{$key}{ram}{hrStorageAllocationUnits}*$linux_hosts{$key}{ram}{hrStorageUsed}/1024/1024/1024); #convert to GB
            print "      host:$linux_hosts{$key}{hostname}  hrStorageUsed:$linux_hosts{$key}{ram}{hrStorageUsed_GB}GB  \n" if ($verbose eq "yes");
         }											#end of if block
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # At this point, we know the total bytes and bytes used.  Based on those values, calculate bytes free.
      #
      $linux_hosts{$key}{ram}{hrStorageFree_GB} = sprintf("%.1f", $linux_hosts{$key}{ram}{hrStorageSize_GB}-$linux_hosts{$key}{ram}{hrStorageUsed_GB} );			#calculate free space
      #
      # Let's also calculate percentages.
      #
      $linux_hosts{$key}{ram}{hrStorageUsed_pct} = sprintf( "%.1f", $linux_hosts{$key}{ram}{hrStorageUsed} / $linux_hosts{$key}{ram}{hrStorageSize} * 100 );	#convert to percentage
      $linux_hosts{$key}{ram}{hrStorageFree_pct} = sprintf( "%.1f", (100 - $linux_hosts{$key}{ram}{hrStorageUsed_pct}) );					#calculate free percentage
      #
      print "      host:$linux_hosts{$key}{hostname}  TotalSize:$linux_hosts{$key}{ram}{hrStorageSize_GB}GB hrStorageUsed:$linux_hosts{$key}{ram}{hrStorageUsed_GB}GB($linux_hosts{$key}{ram}{hrStorageUsed_pct}\%)  hrStorageFree:$linux_hosts{$key}{ram}{hrStorageFree_GB}GB($linux_hosts{$key}{ram}{hrStorageFree_pct}\%) \n" if ($verbose eq "yes");
   } 												#end of foreach loop
} 												#end of subroutine




sub get_ram_util_windows {
   #
   print "running get_ram_util_windows subroutine \n" if ($verbose eq "yes");
   #
   #
   # get RAM details
   #
   # .1.3.6.1.2.1.25.2.3.1     hrStorageTable
   # .1.3.6.1.2.1.25.2.3.1.1   hrStorageTable.hrStorageIndex
   # .1.3.6.1.2.1.25.2.3.1.2   hrStorageTable.hrStorageType
   # .1.3.6.1.2.1.25.2.3.1.3   hrStorageTable.hrStorageDescr
   # .1.3.6.1.2.1.25.2.3.1.4   hrStorageTable.hrStorageAllocationUnits
   # .1.3.6.1.2.1.25.2.3.1.5   hrStorageTable.hrStorageSize
   # .1.3.6.1.2.1.25.2.3.1.6   hrStorageTable.hrStorageUsed
   # .1.3.6.1.2.1.25.2.3.1.7   hrStorageTable.hrStorageAllocationFailures
   #
   #
   # Sample command output:
   # $  snmpwalk   -v 1 -c public hyperv1 .1.3.6.1.2.1.25.2.3.1
   # HOST-RESOURCES-MIB::hrStorageIndex.1 = INTEGER: 1
   # HOST-RESOURCES-MIB::hrStorageIndex.2 = INTEGER: 2
   # HOST-RESOURCES-MIB::hrStorageIndex.3 = INTEGER: 3
   # HOST-RESOURCES-MIB::hrStorageIndex.4 = INTEGER: 4                                              	<---- this is the index that correponds to RAM (may vary by host)
   # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory
   # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam                  	<---- we are interested in RAM
   # HOST-RESOURCES-MIB::hrStorageDescr.1 = STRING: C:\\ Label:  Serial Number e6a835e
   # HOST-RESOURCES-MIB::hrStorageDescr.2 = STRING: D:\\ Label:hyperv1-d  Serial Number f2384eee
   # HOST-RESOURCES-MIB::hrStorageDescr.3 = STRING: Virtual Memory
   # HOST-RESOURCES-MIB::hrStorageDescr.4 = STRING: Physical Memory                                 	<---- description
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.1 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.2 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.3 = INTEGER: 65536 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes                          	<---- size of each allocation unit
   # HOST-RESOURCES-MIB::hrStorageSize.1 = INTEGER: 244049407	                               
   # HOST-RESOURCES-MIB::hrStorageSize.2 = INTEGER: 1953497088
   # HOST-RESOURCES-MIB::hrStorageSize.3 = INTEGER: 600459
   # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635                                          	<---- total number of allocation units (multiple by above to get size in bytes)
   # HOST-RESOURCES-MIB::hrStorageUsed.1 = INTEGER: 85040189
   # HOST-RESOURCES-MIB::hrStorageUsed.2 = INTEGER: 1571142078
   # HOST-RESOURCES-MIB::hrStorageUsed.3 = INTEGER: 256187
   # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 263060 						<---- number of used allocation units (multiple by size to get used bytes)
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.1 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.2 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.3 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.4 = Counter32: 0  					<---- should always be zero
   #
   #
   $community = $community_windows;                                            				#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %windows_hosts) {
      #
      next unless ( $windows_hosts{$key}{ping} eq "up" );					#skip hosts that do not respond to ping
      $oid = ".1.3.6.1.2.1.25.2.3.1";								#SNMP OID for hrStorageTable
      $cmd = "$snmpwalk -v 1 -c $community $windows_hosts{$key}{hostname} $oid.2";		#search through the hrStorageType to find hrStorageRam
      print "   running command to get RAM util on $windows_hosts{$key}{hostname}: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.2
         # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory
         # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam             <--- figure out the index number from this description
         #
         if ( /hrStorageType.([0-9]+) = OID: HOST-RESOURCES-TYPES::hrStorageRam/ ) {    					#find the load for this particular processor
            $windows_hosts{$key}{ram}{hrStorageIndex} = $1;	                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            print "      host:$windows_hosts{$key}{hostname}  hrStorageIndex:$windows_hosts{$key}{ram}{hrStorageIndex} \n" if ($verbose eq "yes");
         }											#end of if block
      }                                                                				#end of while loop
      close IN;                                                        			 	#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageAllocationUnits
      #
      next unless ($windows_hosts{$key}{ram}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.4.$windows_hosts{$key}{ram}{hrStorageIndex}";			#SNMP OID for       hrStorageTable.hrStorageAllocationUnits.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageAllocationUnits.IndexNumber
      print "   running command to check RAM hrStorageAllocationUnits on $windows_hosts{$key}{hostname}: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.4.X
         # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes
         #
         if ( /INTEGER: ([0-9]+) Bytes/ ) {    							#find the size of each allocation unit
            $windows_hosts{$key}{ram}{hrStorageAllocationUnits} = $1;				#value for hrStorageTable.hrStorageAllocationUnits.IndexNumber
            print "      host:$windows_hosts{$key}{hostname} hrStorageAllocationUnits:$1 \n" if ($verbose eq "yes");
         }											#end of if block
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageSize
      #
      next unless ($windows_hosts{$key}{ram}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.5.$windows_hosts{$key}{ram}{hrStorageIndex}";			#SNMP OID for       hrStorageTable.hrStorageSize.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageSize.IndexNumber
      print "   running command to check RAM hrStorageSize on $windows_hosts{$key}{hostname}: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.5.X
         # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635
         #
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the value
            $windows_hosts{$key}{ram}{hrStorageSize} = $1;					#value for hrStorageTable.hrStorageSize.IndexNumber
            $windows_hosts{$key}{ram}{hrStorageSize_GB} = sprintf("%.1f", $windows_hosts{$key}{ram}{hrStorageAllocationUnits}*$windows_hosts{$key}{ram}{hrStorageSize}/1024/1024/1024); #convert to GB
            print "      host:$windows_hosts{$key}{hostname} hrStorageSize:$windows_hosts{$key}{ram}{hrStorageSize_GB}GB \n" if ($verbose eq "yes")
         }                                                             				#end of if block
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageUsed 
      #
      next unless ($windows_hosts{$key}{ram}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.6.$windows_hosts{$key}{ram}{hrStorageIndex}";			#SNMP OID for       hrStorageTable.hrStorageUsed.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageUsed.IndexNumber
      print "   running command to check RAM hrStorageUsed: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.6.X
         # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 261948
         #
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the value 
            $windows_hosts{$key}{ram}{hrStorageUsed} = $1;					#value for hrStorageTable.hrStorageUsed.IndexNumber
            $windows_hosts{$key}{ram}{hrStorageUsed_GB} = sprintf("%.1f", $windows_hosts{$key}{ram}{hrStorageAllocationUnits}*$windows_hosts{$key}{ram}{hrStorageUsed}/1024/1024/1024); #convert to GB
            print "      host:$windows_hosts{$key}{hostname}  hrStorageUsed:$windows_hosts{$key}{ram}{hrStorageUsed_GB}GB  \n" if ($verbose eq "yes");
         }											#end of if block
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # At this point, we know the total bytes and bytes used.  Based on those values, calculate bytes free.
      #
      $windows_hosts{$key}{ram}{hrStorageFree_GB} = sprintf("%.1f", $windows_hosts{$key}{ram}{hrStorageSize_GB}-$windows_hosts{$key}{ram}{hrStorageUsed_GB} );			#calculate free space
      #
      # Let's also calculate percentages.
      #
      $windows_hosts{$key}{ram}{hrStorageUsed_pct} = sprintf( "%.1f", $windows_hosts{$key}{ram}{hrStorageUsed} / $windows_hosts{$key}{ram}{hrStorageSize} * 100 );	#convert to percentage
      $windows_hosts{$key}{ram}{hrStorageFree_pct} = sprintf( "%.1f", (100 - $windows_hosts{$key}{ram}{hrStorageUsed_pct}) );					#calculate free percentage
      #
      print "      host:$windows_hosts{$key}{hostname}  TotalSize:$windows_hosts{$key}{ram}{hrStorageSize_GB}GB hrStorageUsed:$windows_hosts{$key}{ram}{hrStorageUsed_GB}GB($windows_hosts{$key}{ram}{hrStorageUsed_pct}\%)  hrStorageFree:$windows_hosts{$key}{ram}{hrStorageFree_GB}GB($windows_hosts{$key}{ram}{hrStorageFree_pct}\%) \n" if ($verbose eq "yes");
   } 												#end of foreach loop
} 												#end of subroutine




sub get_paging_space_util_linux {
   #
   print "running get_paging_space_util_linux subroutine \n" if ($verbose eq "yes");
   #
   # 
   # get CPU details
   #
   # .1.3.6.1.2.1.25.2.3.1     hrStorageTable
   # .1.3.6.1.2.1.25.2.3.1.1   hrStorageTable.hrStorageIndex
   # .1.3.6.1.2.1.25.2.3.1.2   hrStorageTable.hrStorageType
   # .1.3.6.1.2.1.25.2.3.1.3   hrStorageTable.hrStorageDescr
   # .1.3.6.1.2.1.25.2.3.1.4   hrStorageTable.hrStorageAllocationUnits
   # .1.3.6.1.2.1.25.2.3.1.5   hrStorageTable.hrStorageSize
   # .1.3.6.1.2.1.25.2.3.1.6   hrStorageTable.hrStorageUsed
   # .1.3.6.1.2.1.25.2.3.1.7   hrStorageTable.hrStorageAllocationFailures
   #
   #
   # Sample command output:
   # $  snmpwalk   -v 1 -c public hyperv1 .1.3.6.1.2.1.25.2.3.1
   # HOST-RESOURCES-MIB::hrStorageIndex.1 = INTEGER: 1
   # HOST-RESOURCES-MIB::hrStorageIndex.2 = INTEGER: 2
   # HOST-RESOURCES-MIB::hrStorageIndex.3 = INTEGER: 3 						<---- this is the index that correponds to VirtualMemory (may vary by host)
   # HOST-RESOURCES-MIB::hrStorageIndex.4 = INTEGER: 4                                              	
   # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory         <---- we are interested in VirtualMemory (aka paging space utilization)
   # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam                  	
   # HOST-RESOURCES-MIB::hrStorageDescr.1 = STRING: C:\\ Label:  Serial Number e6a835e
   # HOST-RESOURCES-MIB::hrStorageDescr.2 = STRING: D:\\ Label:hyperv1-d  Serial Number f2384eee
   # HOST-RESOURCES-MIB::hrStorageDescr.3 = STRING: Virtual Memory					<---- description
   # HOST-RESOURCES-MIB::hrStorageDescr.4 = STRING: Physical Memory                                 	
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.1 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.2 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.3 = INTEGER: 65536 Bytes				<---- size of each allocation unit
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes                          	
   # HOST-RESOURCES-MIB::hrStorageSize.1 = INTEGER: 244049407	                               
   # HOST-RESOURCES-MIB::hrStorageSize.2 = INTEGER: 1953497088
   # HOST-RESOURCES-MIB::hrStorageSize.3 = INTEGER: 600459						<---- total number of allocation units (multiple by above to get size in bytes)
   # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635                                          	
   # HOST-RESOURCES-MIB::hrStorageUsed.1 = INTEGER: 85040189
   # HOST-RESOURCES-MIB::hrStorageUsed.2 = INTEGER: 1571142078
   # HOST-RESOURCES-MIB::hrStorageUsed.3 = INTEGER: 256187						<---- number of used allocation units (multiple by size to get used bytes)
   # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 263060 						
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.1 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.2 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.3 = Counter32: 0				<---- should always be zero
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.4 = Counter32: 0  				
   #
   #
   $community = $community_linux;                                            			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %linux_hosts) {
      #
      next unless ( $linux_hosts{$key}{ping} eq "up" );						#skip hosts that do not respond to ping
      $oid = ".1.3.6.1.2.1.25.2.3.1";								#SNMP OID for hrStorageTable
      $cmd = "$snmpwalk -v 1 -c $community $linux_hosts{$key}{hostname} $oid.2";		#search through the hrStorageType to find hrStorageVirtualMemory
      print "   running command to check hrStorageType: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.2
         # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory   <--- figure out the index number from this description
         # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam             
         #
         if ( /hrStorageType.([0-9]+) = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory/ ) { 	#find the value
            $linux_hosts{$key}{paging}{hrStorageIndex} = $1;	                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            print "      host:$linux_hosts{$key}{hostname}  hrStorageIndex:$linux_hosts{$key}{paging}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageAllocationUnits
      #
      next unless ($linux_hosts{$key}{paging}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.4.$linux_hosts{$key}{paging}{hrStorageIndex}";		#SNMP OID for       hrStorageTable.hrStorageAllocationUnits.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageAllocationUnits.IndexNumber
      print "   running command to check hrStorageAllocationUnits: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.4.X
         # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes
         #
         if ( /INTEGER: ([0-9]+) Bytes/ ) {    							#find the size of each allocation unit
            $linux_hosts{$key}{paging}{hrStorageAllocationUnits} = $1;				#value for hrStorageTable.hrStorageAllocationUnits.IndexNumber
            print "      host:$linux_hosts{$key}{hostname}  hrStorageAllocationUnits:$1 \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageSize
      #
      next unless ($linux_hosts{$key}{paging}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.5.$linux_hosts{$key}{paging}{hrStorageIndex}";		#SNMP OID for       hrStorageTable.hrStorageSize.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageSize.IndexNumber
      print "   running command to check hrStorageSize: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.5.X
         # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635
         #
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the value
            $linux_hosts{$key}{paging}{hrStorageSize} = $1;					#value for hrStorageTable.hrStorageSize.IndexNumber
            $linux_hosts{$key}{paging}{hrStorageSize_GB} = sprintf("%.1f", $linux_hosts{$key}{paging}{hrStorageAllocationUnits}*$linux_hosts{$key}{paging}{hrStorageSize}/1024/1024/1024); #convert to GB
            print "      host:$linux_hosts{$key}{hostname}  hrStorageSize:$linux_hosts{$key}{paging}{hrStorageSize_GB}GB \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageUsed 
      #
      next unless ($linux_hosts{$key}{paging}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.6.$linux_hosts{$key}{paging}{hrStorageIndex}";		#SNMP OID for       hrStorageTable.hrStorageUsed.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageUsed.IndexNumber
      print "   running command to check hrStorageUsed: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.6.X
         # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 261948
         #
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the value 
            $linux_hosts{$key}{paging}{hrStorageUsed} = $1;					#value for hrStorageTable.hrStorageUsed.IndexNumber
            $linux_hosts{$key}{paging}{hrStorageUsed_GB} = sprintf("%.1f", $linux_hosts{$key}{paging}{hrStorageAllocationUnits}*$linux_hosts{$key}{paging}{hrStorageUsed}/1024/1024/1024); #convert to GB
            print "      host:$linux_hosts{$key}{hostname}  hrStorageUsed:$linux_hosts{$key}{paging}{hrStorageUsed_GB}GB  \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # At this point, we know the total bytes and bytes used.  Based on those values, calculate bytes free.
      #
      $linux_hosts{$key}{paging}{hrStorageFree_GB} = ( $linux_hosts{$key}{paging}{hrStorageSize_GB} - $linux_hosts{$key}{paging}{hrStorageUsed_GB} );			#calculate free space
      #
      # Let's also calculate percentages.
      #
      $linux_hosts{$key}{paging}{hrStorageUsed_pct} = sprintf( "%.1f", $linux_hosts{$key}{paging}{hrStorageUsed} / $linux_hosts{$key}{paging}{hrStorageSize} * 100 );	#convert to percentage
      $linux_hosts{$key}{paging}{hrStorageFree_pct} = sprintf( "%.1f", (100 - $linux_hosts{$key}{paging}{hrStorageUsed_pct}) );					#calculate free percentage
      #
      print "      host:$linux_hosts{$key}{hostname}  TotalSize:$linux_hosts{$key}{paging}{hrStorageSize_GB}GB hrStorageUsed:$linux_hosts{$key}{paging}{hrStorageUsed_GB}GB($linux_hosts{$key}{paging}{hrStorageUsed_pct}\%)  hrStorageFree:$linux_hosts{$key}{paging}{hrStorageFree_GB}GB($linux_hosts{$key}{paging}{hrStorageFree_pct}\%) \n" if ($verbose eq "yes");
   } 												#end of foreach loop
} 												#end of subroutine




sub get_paging_space_util_windows {
   #
   print "running get_paging_space_util_windows subroutine \n" if ($verbose eq "yes");
   #
   # get CPU details
   #
   # .1.3.6.1.2.1.25.2.3.1     hrStorageTable
   # .1.3.6.1.2.1.25.2.3.1.1   hrStorageTable.hrStorageIndex
   # .1.3.6.1.2.1.25.2.3.1.2   hrStorageTable.hrStorageType
   # .1.3.6.1.2.1.25.2.3.1.3   hrStorageTable.hrStorageDescr
   # .1.3.6.1.2.1.25.2.3.1.4   hrStorageTable.hrStorageAllocationUnits
   # .1.3.6.1.2.1.25.2.3.1.5   hrStorageTable.hrStorageSize
   # .1.3.6.1.2.1.25.2.3.1.6   hrStorageTable.hrStorageUsed
   # .1.3.6.1.2.1.25.2.3.1.7   hrStorageTable.hrStorageAllocationFailures
   #
   #
   # Sample command output:
   # $  snmpwalk   -v 1 -c public hyperv1 .1.3.6.1.2.1.25.2.3.1
   # HOST-RESOURCES-MIB::hrStorageIndex.1 = INTEGER: 1
   # HOST-RESOURCES-MIB::hrStorageIndex.2 = INTEGER: 2
   # HOST-RESOURCES-MIB::hrStorageIndex.3 = INTEGER: 3 						<---- this is the index that correponds to VirtualMemory (may vary by host)
   # HOST-RESOURCES-MIB::hrStorageIndex.4 = INTEGER: 4                                              	
   # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory         <---- we are interested in VirtualMemory (aka paging space utilization)
   # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam                  	
   # HOST-RESOURCES-MIB::hrStorageDescr.1 = STRING: C:\\ Label:  Serial Number e6a835e
   # HOST-RESOURCES-MIB::hrStorageDescr.2 = STRING: D:\\ Label:hyperv1-d  Serial Number f2384eee
   # HOST-RESOURCES-MIB::hrStorageDescr.3 = STRING: Virtual Memory					<---- description
   # HOST-RESOURCES-MIB::hrStorageDescr.4 = STRING: Physical Memory                                 	
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.1 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.2 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.3 = INTEGER: 65536 Bytes				<---- size of each allocation unit
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes                          	
   # HOST-RESOURCES-MIB::hrStorageSize.1 = INTEGER: 244049407	                               
   # HOST-RESOURCES-MIB::hrStorageSize.2 = INTEGER: 1953497088
   # HOST-RESOURCES-MIB::hrStorageSize.3 = INTEGER: 600459						<---- total number of allocation units (multiple by above to get size in bytes)
   # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635                                          	
   # HOST-RESOURCES-MIB::hrStorageUsed.1 = INTEGER: 85040189
   # HOST-RESOURCES-MIB::hrStorageUsed.2 = INTEGER: 1571142078
   # HOST-RESOURCES-MIB::hrStorageUsed.3 = INTEGER: 256187						<---- number of used allocation units (multiple by size to get used bytes)
   # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 263060 						
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.1 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.2 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.3 = Counter32: 0				<---- should always be zero
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.4 = Counter32: 0  				
   #
   #
   #
   $community = $community_windows;                                            			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %windows_hosts) {
      #
      next unless ( $windows_hosts{$key}{ping} eq "up" );					#skip hosts that do not respond to ping
      $oid = ".1.3.6.1.2.1.25.2.3.1";								#SNMP OID for hrStorageTable
      $cmd = "$snmpwalk -v 1 -c $community $windows_hosts{$key}{hostname} $oid.2";		#search through the hrStorageType to find hrStorageVirtualMemory
      print "   running command to check hrStorageType: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.2
         # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory   <--- figure out the index number from this description
         # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam             
         #
         if ( /hrStorageType.([0-9]+) = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory/ ) { 	#find the value
            $windows_hosts{$key}{paging}{hrStorageIndex} = $1;	                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            print "      host:$windows_hosts{$key}{hostname}  hrStorageIndex:$windows_hosts{$key}{paging}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageAllocationUnits
      #
      next unless ($windows_hosts{$key}{paging}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.4.$windows_hosts{$key}{paging}{hrStorageIndex}";		#SNMP OID for       hrStorageTable.hrStorageAllocationUnits.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageAllocationUnits.IndexNumber
      print "   running command to check hrStorageAllocationUnits: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.4.X
         # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes
         #
         if ( /INTEGER: ([0-9]+) Bytes/ ) {    							#find the size of each allocation unit
            $windows_hosts{$key}{paging}{hrStorageAllocationUnits} = $1;				#value for hrStorageTable.hrStorageAllocationUnits.IndexNumber
            print "      host:$windows_hosts{$key}{hostname}  hrStorageAllocationUnits:$1 \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageSize
      #
      next unless ($windows_hosts{$key}{paging}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.5.$windows_hosts{$key}{paging}{hrStorageIndex}";		#SNMP OID for       hrStorageTable.hrStorageSize.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageSize.IndexNumber
      print "   running command to check hrStorageSize: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.5.X
         # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635
         #
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the value
            $windows_hosts{$key}{paging}{hrStorageSize} = $1;					#value for hrStorageTable.hrStorageSize.IndexNumber
            $windows_hosts{$key}{paging}{hrStorageSize_GB} = sprintf("%.1f", $windows_hosts{$key}{paging}{hrStorageAllocationUnits}*$windows_hosts{$key}{paging}{hrStorageSize}/1024/1024/1024); #convert to GB
            print "      host:$windows_hosts{$key}{hostname}  hrStorageSize:$windows_hosts{$key}{paging}{hrStorageSize_GB}GB \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageUsed 
      #
      next unless ($windows_hosts{$key}{paging}{hrStorageIndex});					#break out of foreach loop if the previous section failed to determine the hrStorageIndex
      $oid = ".1.3.6.1.2.1.25.2.3.1.6.$windows_hosts{$key}{paging}{hrStorageIndex}";		#SNMP OID for       hrStorageTable.hrStorageUsed.IndexNumber
      $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageUsed.IndexNumber
      print "   running command to check hrStorageUsed: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.6.X
         # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 261948
         #
         if ( /INTEGER: ([0-9]+)/ ) {    							#find the value 
            $windows_hosts{$key}{paging}{hrStorageUsed} = $1;					#value for hrStorageTable.hrStorageUsed.IndexNumber
            $windows_hosts{$key}{paging}{hrStorageUsed_GB} = sprintf("%.1f", $windows_hosts{$key}{paging}{hrStorageAllocationUnits}*$windows_hosts{$key}{paging}{hrStorageUsed}/1024/1024/1024); #convert to GB
            print "      host:$windows_hosts{$key}{hostname}  hrStorageUsed:$windows_hosts{$key}{paging}{hrStorageUsed_GB}GB  \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # At this point, we know the total bytes and bytes used.  Based on those values, calculate bytes free.
      #
      $windows_hosts{$key}{paging}{hrStorageFree_GB} = ( $windows_hosts{$key}{paging}{hrStorageSize_GB} - $windows_hosts{$key}{paging}{hrStorageUsed_GB} );			#calculate free space
      #
      # Let's also calculate percentages.
      #
      $windows_hosts{$key}{paging}{hrStorageUsed_pct} = sprintf( "%.1f", $windows_hosts{$key}{paging}{hrStorageUsed} / $windows_hosts{$key}{paging}{hrStorageSize} * 100 );	#convert to percentage
      $windows_hosts{$key}{paging}{hrStorageFree_pct} = sprintf( "%.1f", (100 - $windows_hosts{$key}{paging}{hrStorageUsed_pct}) );					#calculate free percentage
      #
      print "      host:$windows_hosts{$key}{hostname}  TotalSize:$windows_hosts{$key}{paging}{hrStorageSize_GB}GB hrStorageUsed:$windows_hosts{$key}{paging}{hrStorageUsed_GB}GB($windows_hosts{$key}{paging}{hrStorageUsed_pct}\%)  hrStorageFree:$windows_hosts{$key}{paging}{hrStorageFree_GB}GB($windows_hosts{$key}{paging}{hrStorageFree_pct}\%) \n" if ($verbose eq "yes");
   } 												#end of foreach loop
} 												#end of subroutine




sub get_windows_drive_util {
   #
   print "running get_windows_drive_util subroutine \n" if ($verbose eq "yes");
   #
   # get CPU details
   #
   # .1.3.6.1.2.1.25.2.3.1     hrStorageTable
   # .1.3.6.1.2.1.25.2.3.1.1   hrStorageTable.hrStorageIndex
   # .1.3.6.1.2.1.25.2.3.1.2   hrStorageTable.hrStorageType
   # .1.3.6.1.2.1.25.2.3.1.3   hrStorageTable.hrStorageDescr
   # .1.3.6.1.2.1.25.2.3.1.4   hrStorageTable.hrStorageAllocationUnits
   # .1.3.6.1.2.1.25.2.3.1.5   hrStorageTable.hrStorageSize
   # .1.3.6.1.2.1.25.2.3.1.6   hrStorageTable.hrStorageUsed
   # .1.3.6.1.2.1.25.2.3.1.7   hrStorageTable.hrStorageAllocationFailures
   #
   #
   # Sample command output:
   # $  snmpwalk   -v 1 -c public hyperv1 .1.3.6.1.2.1.25.2.3.1
   # HOST-RESOURCES-MIB::hrStorageIndex.1 = INTEGER: 1
   # HOST-RESOURCES-MIB::hrStorageIndex.2 = INTEGER: 2
   # HOST-RESOURCES-MIB::hrStorageIndex.3 = INTEGER: 3 						
   # HOST-RESOURCES-MIB::hrStorageIndex.4 = INTEGER: 4                                              	
   # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk		<---- we are interested in hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk		<---- but there might be multiple (one per disk partition)
   # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory         
   # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam                  	
   # HOST-RESOURCES-MIB::hrStorageDescr.1 = STRING: C:\\ Label:  Serial Number e6a835e		<---- this example shows a Windows drive letter C:
   # HOST-RESOURCES-MIB::hrStorageDescr.2 = STRING: D:\\ Label:hyperv1-d  Serial Number f2384eee	<---- this example shows a Windows drive letter D:
   # HOST-RESOURCES-MIB::hrStorageDescr.3 = STRING: Virtual Memory					
   # HOST-RESOURCES-MIB::hrStorageDescr.4 = STRING: Physical Memory                                 	
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.1 = INTEGER: 4096 Bytes				<---- size of each allocation unit
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.2 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.3 = INTEGER: 65536 Bytes				
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes                          	
   # HOST-RESOURCES-MIB::hrStorageSize.1 = INTEGER: 244049407	                               	<---- total number of allocation units (multiple by above to get size in bytes)
   # HOST-RESOURCES-MIB::hrStorageSize.2 = INTEGER: 1953497088
   # HOST-RESOURCES-MIB::hrStorageSize.3 = INTEGER: 600459						
   # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635                                          	
   # HOST-RESOURCES-MIB::hrStorageUsed.1 = INTEGER: 85040189						<---- number of used allocation units (multiple by size to get used bytes)
   # HOST-RESOURCES-MIB::hrStorageUsed.2 = INTEGER: 1571142078
   # HOST-RESOURCES-MIB::hrStorageUsed.3 = INTEGER: 256187						
   # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 263060 						
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.1 = Counter32: 0				<---- should always be zero
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.2 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.3 = Counter32: 0				
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.4 = Counter32: 0  				
   #
   #
   #
   $community = $community_windows;                                            			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %windows_hosts) {
      #
      next unless ( $windows_hosts{$key}{ping} eq "up" );					#skip hosts that do not respond to ping
      next unless ( $windows_hosts{$key}{os}   eq "Windows" );					#skip this subroutine for any hosts not running Windows operating system
      $oid = ".1.3.6.1.2.1.25.2.3.1";								#SNMP OID for hrStorageTable
      $cmd = "$snmpwalk -v 1 -c $community $windows_hosts{$key}{hostname} $oid";		#search through the hrStorageType to find hrStorageVirtualMemory
      print "   running command to check hrStorageType: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1
         # HOST-RESOURCES-MIB::hrStorageIndex.1 = INTEGER: 1						    <---- based on hrStorageType and hrStorageDescr, this is the index we wantj
         # HOST-RESOURCES-MIB::hrStorageIndex.2 = INTEGER: 2
         # HOST-RESOURCES-MIB::hrStorageIndex.3 = INTEGER: 3
         # HOST-RESOURCES-MIB::hrStorageIndex.4 = INTEGER: 4
         # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk              <---- correct hrStorageType
         # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory
         # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam
         # HOST-RESOURCES-MIB::hrStorageDescr.1 = STRING: C:\\ Label:  Serial Number e6a835e                <---- this is drive C:
         # HOST-RESOURCES-MIB::hrStorageDescr.2 = STRING: D:\\ Label:hyperv1-d  Serial Number f2384eee
         # HOST-RESOURCES-MIB::hrStorageDescr.3 = STRING: Virtual Memory
         # HOST-RESOURCES-MIB::hrStorageDescr.4 = STRING: Physical Memory
         #
         if ( /hrStorageDescr.([0-9]+) = STRING: C:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{c}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{c}{drive_letter}   = "C";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive C: hrStorageIndex:$windows_hosts{$key}{windows_drive}{c}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: D:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{d}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{d}{drive_letter}   = "D";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive D: hrStorageIndex:$windows_hosts{$key}{windows_drive}{d}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: E:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{e}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{e}{drive_letter}   = "E";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive E: hrStorageIndex:$windows_hosts{$key}{windows_drive}{e}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: F:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{f}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{f}{drive_letter}   = "F";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive F: hrStorageIndex:$windows_hosts{$key}{windows_drive}{f}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: G:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{g}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{g}{drive_letter}   = "G";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive G: hrStorageIndex:$windows_hosts{$key}{windows_drive}{g}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: H:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{h}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: I:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{i}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{i}{drive_letter}   = "I";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive I: hrStorageIndex:$windows_hosts{$key}{windows_drive}{i}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: J:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{j}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{j}{drive_letter}   = "J";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive J: hrStorageIndex:$windows_hosts{$key}{windows_drive}{j}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: K:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{k}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{k}{drive_letter}   = "K";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive K: hrStorageIndex:$windows_hosts{$key}{windows_drive}{k}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: L:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{l}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{l}{drive_letter}   = "L";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive L: hrStorageIndex:$windows_hosts{$key}{windows_drive}{l}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: M:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{m}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{m}{drive_letter}   = "M";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive M: hrStorageIndex:$windows_hosts{$key}{windows_drive}{m}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: N:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{n}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{n}{drive_letter}   = "N";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive N: hrStorageIndex:$windows_hosts{$key}{windows_drive}{n}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: O:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{o}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{o}{drive_letter}   = "O";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive O: hrStorageIndex:$windows_hosts{$key}{windows_drive}{o}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: P:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{p}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{p}{drive_letter}   = "P";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive P: hrStorageIndex:$windows_hosts{$key}{windows_drive}{p}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: Q:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{q}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{q}{drive_letter}   = "Q";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive Q: hrStorageIndex:$windows_hosts{$key}{windows_drive}{q}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: R:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{r}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{r}{drive_letter}   = "R";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive R: hrStorageIndex:$windows_hosts{$key}{windows_drive}{r}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: S:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{s}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{s}{drive_letter}   = "S";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive S: hrStorageIndex:$windows_hosts{$key}{windows_drive}{s}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: T:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{t}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{t}{drive_letter}   = "T";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive T: hrStorageIndex:$windows_hosts{$key}{windows_drive}{t}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: U:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{u}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{u}{drive_letter}   = "U";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive U: hrStorageIndex:$windows_hosts{$key}{windows_drive}{u}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: V:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{v}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{v}{drive_letter}   = "V";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive V: hrStorageIndex:$windows_hosts{$key}{windows_drive}{v}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: W:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{w}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{w}{drive_letter}   = "W";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive W: hrStorageIndex:$windows_hosts{$key}{windows_drive}{w}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: X:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{x}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{x}{drive_letter}   = "X";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive X: hrStorageIndex:$windows_hosts{$key}{windows_drive}{x}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: Y:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{y}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{y}{drive_letter}   = "Y";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive Y: hrStorageIndex:$windows_hosts{$key}{windows_drive}{y}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: Z:/ ) {  					#find the appropriate windows drive letter
            $windows_hosts{$key}{windows_drive}{z}{hrStorageIndex} = $1;	               	#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $windows_hosts{$key}{windows_drive}{z}{drive_letter}   = "Z";	               	#save drive letter as a hash element instead of a hash key so we can refer to it later
            print "      host:$windows_hosts{$key}{hostname}    Drive Z: hrStorageIndex:$windows_hosts{$key}{windows_drive}{z}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
      }                                                                				#end of while loop
      close IN;                                                         			#close filehandle
      #
      # Now that we know the appropriate hrStorageIndex, get the hrStorageAllocationUnits
      #
      @drive_letters = ("a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z");								#define array elements for drive letters a..z
      for $drive_letter (@drive_letters) {									#loop through for each drive letter a..z  
         #
         # loop through for every drive letter a..z
         next unless (defined($windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageIndex}));		#skip if this drive letter does not exist
         #
         #
         # Now that we know the appropriate hrStorageIndex, get the hrStorageAllocationUnits
         #
         $oid = ".1.3.6.1.2.1.25.2.3.1.4.$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageIndex}";	#SNMP OID for       hrStorageTable.hrStorageAllocationUnits.IndexNumber
         $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";				#get the value from hrStorageTable.hrStorageAllocationUnits.IndexNumber
         print "   running command to check hrStorageAllocationUnits for $windows_hosts{$key}{hostname} drive letter $windows_hosts{$key}{windows_drive}{$drive_letter}{drive_letter}: $cmd \n" if ($verbose eq "yes");
         open(IN,"$cmd 2>&1 |");                                           					#open filehandle using command output
         while (<IN>) {                                                   	 				#read a line from the command output
            # output should look similar to:
            # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.4.X
            # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes
            #
            if ( /INTEGER: ([0-9]+) Bytes/ ) {    								#find the size of each allocation unit
               $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageAllocationUnits} = $1;		#value for hrStorageTable.hrStorageAllocationUnits.IndexNumber
               print "      host:$windows_hosts{$key}{hostname} hrStorageAllocationUnits:$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageAllocationUnits} \n" if ($verbose eq "yes");
            } 													#end of if block
         }                                                                					#end of while loop
         close IN;                                                         					#close filehandle
         #
         #
         # Now that we know the appropriate hrStorageIndex, get the hrStorageSize
         #
         next unless ($windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageIndex});			#break out of for loop if the previous section failed to determine the hrStorageIndex
         next if     ($windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageAllocationUnits} == 0);	#break out of for loop if the hrAllocationUnits=0 (probably an empty CDROM drive)
         $oid = ".1.3.6.1.2.1.25.2.3.1.5.$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageIndex}";	#SNMP OID for       hrStorageTable.hrStorageSize.IndexNumber
         $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";				#get the value from hrStorageTable.hrStorageSize.IndexNumber
         print "   running command to check hrStorageSize for $windows_hosts{$key}{hostname} drive letter $windows_hosts{$key}{windows_drive}{$drive_letter}{drive_letter}: $cmd \n" if ($verbose eq "yes");
         open(IN,"$cmd 2>&1 |");                                           					#open filehandle using command output
         while (<IN>) {                                                   	 				#read a line from the command output
            # output should look similar to:
            # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.5.X
            # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635
            #
            if ( /INTEGER: ([0-9]+)/ ) {    									#find the value
               $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize} = $1;				#value for hrStorageTable.hrStorageSize.IndexNumber
               if ( $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize} > 0 ) {			#avoid divide by zero error
                  $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize_GB} = sprintf("%.1f", $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageAllocationUnits}*$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize}/1024/1024/1024); #convert to GB
               } else {
                  $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize_GB} = 0;			#avoid divide by zero error by manually converting bytes to GB
               }												#end of if/else block
               print "      host:$windows_hosts{$key}{hostname} hrStorageSize:$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize_GB} GB \n" if ($verbose eq "yes");
            }
         }                                                                					#end of while loop
         close IN;                                                         					#close filehandle
         #
         #
         # Now that we know the appropriate hrStorageIndex, get the hrStorageUsed 
         #
         next unless ($windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageIndex});			#break out of foreach loop if the previous section failed to determine the hrStorageIndex
         $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed}    = 0;				#initialize hash element
         $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_GB} = 0;				#initialize hash element
         $oid = ".1.3.6.1.2.1.25.2.3.1.6.$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageIndex}";	#SNMP OID for       hrStorageTable.hrStorageUsed.IndexNumber
         $cmd = "$snmpget -v 1 -c $community $windows_hosts{$key}{hostname} $oid";				#get the value from hrStorageTable.hrStorageUsed.IndexNumber
         print "   running command to check hrStorageUsed on $windows_hosts{$key}{hostname} Drive letter $windows_hosts{$key}{windows_drive}{$drive_letter}{drive_letter}: $cmd \n" if ($verbose eq "yes");
         open(IN,"$cmd 2>&1 |");                                           					#open filehandle using command output
         while (<IN>) {                                                   	 				#read a line from the command output
            # output should look similar to:
            # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.6.X
            # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 261948
            #
            if ( /INTEGER: ([0-9]+)/ ) {    									#find the value 
               $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed} = $1;				#value for hrStorageTable.hrStorageUsed.IndexNumber
               if ( $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed} > 0 ) {			#avoid divide by zero error
                  $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_GB} = sprintf("%.1f", $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageAllocationUnits}*$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed}/1024/1024/1024); #convert to GB
               } else {
                  $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_GB} = 0;			#avoid divide by zero error by manually converting used bytes to used GB
               }												#end of if/else block
               print "      host:$windows_hosts{$key}{hostname}  $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_GB}GB  \n" if ($verbose eq "yes");
            }
         }                                                                					#end of while loop
         close IN;                                                         					#close filehandle
         #
         #
         # At this point, we know the total bytes and bytes used.  Based on those values, calculate bytes free.
         #
         $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageFree_GB} = ( $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize_GB} - $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_GB} );			#calculate free space
         #
         # Let's also calculate percentages.
         #
         if ( $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize} > 0 ) {				#avoid divide by zero error
            $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_pct} = sprintf( "%.1f", $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed} / $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize} * 100 );	#convert to percentage
            $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageFree_pct} = sprintf( "%.1f", (100 - $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_pct}) );					#calculate free percentage
         } else { 
            $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageFree_pct} = 0;  #if disk size is zero (ie a CD-ROM drive without inserted media), set the free% to zero
         }
         #
         print "      host:$windows_hosts{$key}{hostname}  TotalSize:$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageSize_GB}GB hrStorageUsed:$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_GB}GB($windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_pct}\%)  hrStorageFree:$windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageFree_GB}GB($windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageFree_pct}\%) \n" if ($verbose eq "yes");
      } 													#end of for a..z oop
   } 														#end of foreach loop
} 														#end of subroutine




sub get_linux_fs_util {
   #
   print "running get_linux_fs_util subroutine \n" if ($verbose eq "yes");
   #
   # get CPU details
   #
   # .1.3.6.1.2.1.25.2.3.1     hrStorageTable
   # .1.3.6.1.2.1.25.2.3.1.1   hrStorageTable.hrStorageIndex
   # .1.3.6.1.2.1.25.2.3.1.2   hrStorageTable.hrStorageType
   # .1.3.6.1.2.1.25.2.3.1.3   hrStorageTable.hrStorageDescr
   # .1.3.6.1.2.1.25.2.3.1.4   hrStorageTable.hrStorageAllocationUnits
   # .1.3.6.1.2.1.25.2.3.1.5   hrStorageTable.hrStorageSize
   # .1.3.6.1.2.1.25.2.3.1.6   hrStorageTable.hrStorageUsed
   # .1.3.6.1.2.1.25.2.3.1.7   hrStorageTable.hrStorageAllocationFailures
   #
   #
   # Sample command output:
   # $  snmpwalk   -v 1 -c public hyperv1 .1.3.6.1.2.1.25.2.3.1
   # HOST-RESOURCES-MIB::hrStorageIndex.1 = INTEGER: 1
   # HOST-RESOURCES-MIB::hrStorageIndex.2 = INTEGER: 2
   # HOST-RESOURCES-MIB::hrStorageIndex.3 = INTEGER: 3 						
   # HOST-RESOURCES-MIB::hrStorageIndex.4 = INTEGER: 4                                              	
   # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk		<---- we are interested in hrStorageFixedDisk
   # HOST-RESOURCES-MIB::hrStorageType.2 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk		<---- but there might be multiple (one per disk partition)
   # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory         
   # HOST-RESOURCES-MIB::hrStorageType.4 = OID: HOST-RESOURCES-TYPES::hrStorageRam                  	
   # HOST-RESOURCES-MIB::hrStorageDescr.1 = STRING: C:\\ Label:  Serial Number e6a835e		<---- this example shows a Windows drive letter C:
   # HOST-RESOURCES-MIB::hrStorageDescr.2 = STRING: D:\\ Label:hyperv1-d  Serial Number f2384eee	<---- this example shows a Windows drive letter D:
   # HOST-RESOURCES-MIB::hrStorageDescr.3 = STRING: Virtual Memory					
   # HOST-RESOURCES-MIB::hrStorageDescr.4 = STRING: Physical Memory                                 	
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.1 = INTEGER: 4096 Bytes				<---- size of each allocation unit
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.2 = INTEGER: 4096 Bytes
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.3 = INTEGER: 65536 Bytes				
   # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes                          	
   # HOST-RESOURCES-MIB::hrStorageSize.1 = INTEGER: 244049407	                               	<---- total number of allocation units (multiple by above to get size in bytes)
   # HOST-RESOURCES-MIB::hrStorageSize.2 = INTEGER: 1953497088
   # HOST-RESOURCES-MIB::hrStorageSize.3 = INTEGER: 600459						
   # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635                                          	
   # HOST-RESOURCES-MIB::hrStorageUsed.1 = INTEGER: 85040189						<---- number of used allocation units (multiple by size to get used bytes)
   # HOST-RESOURCES-MIB::hrStorageUsed.2 = INTEGER: 1571142078
   # HOST-RESOURCES-MIB::hrStorageUsed.3 = INTEGER: 256187						
   # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 263060 						
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.1 = Counter32: 0				<---- should always be zero
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.2 = Counter32: 0
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.3 = Counter32: 0				
   # HOST-RESOURCES-MIB::hrStorageAllocationFailures.4 = Counter32: 0  				
   #
   #
   #
   $community = $community_linux;                                            			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %linux_hosts) {
      #
      next unless ( $linux_hosts{$key}{ping} eq "up" );							#skip hosts that do not respond to ping
      next unless ( $linux_hosts{$key}{os}   eq "Linux");						#skip this subroutine for any hosts not running Windows operating system
      $oid = ".1.3.6.1.2.1.25.2.3.1";									#SNMP OID for hrStorageTable
      $cmd = "$snmpwalk -v 1 -c $community $linux_hosts{$key}{hostname} $oid";				#search through the hrStorageType to find hrStorageVirtualMemory
      print "   running command to check hrStorageType on host $linux_hosts{$key}{hostname}: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           				#open filehandle using command output
      while (<IN>) {                                                   	 				#read a line from the command output
         # output should look similar to:
         # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1
         # HOST-RESOURCES-MIB::hrStorageIndex.1 = INTEGER: 1
         # HOST-RESOURCES-MIB::hrStorageIndex.3 = INTEGER: 3
         # HOST-RESOURCES-MIB::hrStorageIndex.6 = INTEGER: 6
         # HOST-RESOURCES-MIB::hrStorageIndex.7 = INTEGER: 7
         # HOST-RESOURCES-MIB::hrStorageIndex.8 = INTEGER: 8
         # HOST-RESOURCES-MIB::hrStorageIndex.10 = INTEGER: 10
         # HOST-RESOURCES-MIB::hrStorageIndex.35 = INTEGER: 35
         # HOST-RESOURCES-MIB::hrStorageIndex.37 = INTEGER: 37
         # HOST-RESOURCES-MIB::hrStorageIndex.38 = INTEGER: 38
         # HOST-RESOURCES-MIB::hrStorageIndex.52 = INTEGER: 52
         # HOST-RESOURCES-MIB::hrStorageIndex.58 = INTEGER: 58
         # HOST-RESOURCES-MIB::hrStorageIndex.59 = INTEGER: 59
         # HOST-RESOURCES-MIB::hrStorageType.1 = OID: HOST-RESOURCES-TYPES::hrStorageRam
         # HOST-RESOURCES-MIB::hrStorageType.3 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory
         # HOST-RESOURCES-MIB::hrStorageType.6 = OID: HOST-RESOURCES-TYPES::hrStorageOther
         # HOST-RESOURCES-MIB::hrStorageType.7 = OID: HOST-RESOURCES-TYPES::hrStorageOther
         # HOST-RESOURCES-MIB::hrStorageType.8 = OID: HOST-RESOURCES-TYPES::hrStorageOther
         # HOST-RESOURCES-MIB::hrStorageType.10 = OID: HOST-RESOURCES-TYPES::hrStorageVirtualMemory
         # HOST-RESOURCES-MIB::hrStorageType.35 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk          	<---- there are multiple hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.37 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.38 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.52 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.58 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageType.59 = OID: HOST-RESOURCES-TYPES::hrStorageFixedDisk
         # HOST-RESOURCES-MIB::hrStorageDescr.1 = STRING: Physical memory
         # HOST-RESOURCES-MIB::hrStorageDescr.3 = STRING: Virtual memory
         # HOST-RESOURCES-MIB::hrStorageDescr.6 = STRING: Memory buffers
         # HOST-RESOURCES-MIB::hrStorageDescr.7 = STRING: Cached memory
         # HOST-RESOURCES-MIB::hrStorageDescr.8 = STRING: Shared memory
         # HOST-RESOURCES-MIB::hrStorageDescr.10 = STRING: Swap space
         # HOST-RESOURCES-MIB::hrStorageDescr.35 = STRING: /dev/shm
         # HOST-RESOURCES-MIB::hrStorageDescr.37 = STRING: /run
         # HOST-RESOURCES-MIB::hrStorageDescr.38 = STRING: /sys/fs/cgroup
         # HOST-RESOURCES-MIB::hrStorageDescr.52 = STRING: /							<---- so we find the filesystem name 
         # HOST-RESOURCES-MIB::hrStorageDescr.58 = STRING: /boot
         # HOST-RESOURCES-MIB::hrStorageDescr.59 = STRING: /run/user/9005
         #
         if ( /hrStorageDescr.([0-9]+) = STRING: \/$/ ) {  						#find the appropriate filesystem mount point
            $linux_hosts{$key}{linux_fs}{root}{hrStorageIndex} = $1;                   			#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $linux_hosts{$key}{linux_fs}{root}{mount_point} = "/";                   			#save as a hash element instead of a hash key so we can query the value later
            print "      host:$linux_hosts{$key}{hostname}  mount_point:$linux_hosts{$key}{linux_fs}{root}{mount_point}  hrStorageIndex:$linux_hosts{$key}{linux_fs}{root}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: \/home$/ ) { 	 					#find the appropriate filesystem mount point
            $linux_hosts{$key}{linux_fs}{_home}{hrStorageIndex} = $1;                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $linux_hosts{$key}{linux_fs}{_home}{mount_point} = "/home";                  		#save as a hash element instead of a hash key so we can query the value later
            print "      host:$linux_hosts{$key}{hostname}  mount_point:$linux_hosts{$key}{linux_fs}{_home}{mount_point}  hrStorageIndex:$linux_hosts{$key}{linux_fs}{_home}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: \/repo01$/ ) {  					#find the appropriate filesystem mount point
            $linux_hosts{$key}{linux_fs}{_repo01}{hrStorageIndex} = $1;                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $linux_hosts{$key}{linux_fs}{_repo01}{mount_point} = "/repo01";                  		#save as a hash element instead of a hash key so we can query the value later
            print "      host:$linux_hosts{$key}{hostname}  mount_point:$linux_hosts{$key}{linux_fs}{_repo01}{mount_point}  hrStorageIndex:$linux_hosts{$key}{linux_fs}{_repo01}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: \/apps\/oracle$/ ) {  					#find the appropriate filesystem mount point
            $linux_hosts{$key}{linux_fs}{_apps_oracle}{hrStorageIndex} = $1;                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $linux_hosts{$key}{linux_fs}{_apps_oracle}{mount_point} = "/apps/oracle";                  	#save as a hash element instead of a hash key so we can query the value later
            print "      host:$linux_hosts{$key}{hostname}  mount_point:$linux_hosts{$key}{linux_fs}{_apps_oracle}{mount_point}  hrStorageIndex:$linux_hosts{$key}{linux_fs}{_apps_oracle}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: \/oracle$/ ) {  					#find the appropriate filesystem mount point
            $linux_hosts{$key}{linux_fs}{_oracle}{hrStorageIndex} = $1;                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $linux_hosts{$key}{linux_fs}{_oracle}{mount_point} = "/oracle";                  		#save as a hash element instead of a hash key so we can query the value later
            print "      host:$linux_hosts{$key}{hostname}  mount_point:$linux_hosts{$key}{linux_fs}{_oracle}{mount_point}  hrStorageIndex:$linux_hosts{$key}{linux_fs}{_oracle}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: \/grid$/ ) {  						#find the appropriate filesystem mount point
            $linux_hosts{$key}{linux_fs}{_grid}{hrStorageIndex} = $1;                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $linux_hosts{$key}{linux_fs}{_grid}{mount_point} = "/grid";                  		#save as a hash element instead of a hash key so we can query the value later
            print "      host:$linux_hosts{$key}{hostname}  mount_point:$linux_hosts{$key}{linux_fs}{_grid}{mount_point}  hrStorageIndex:$linux_hosts{$key}{linux_fs}{_grid}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: \/systembackup$/ ) {  					#find the appropriate filesystem mount point
            $linux_hosts{$key}{linux_fs}{_systembackup}{hrStorageIndex} = $1;                  		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $linux_hosts{$key}{linux_fs}{_systembackup}{mount_point} = "/systembackup";        		#save as a hash element instead of a hash key so we can query the value later
            print "      host:$linux_hosts{$key}{hostname}  mount_point:$linux_hosts{$key}{linux_fs}{_systembackup}{mount_point}  hrStorageIndex:$linux_hosts{$key}{linux_fs}{_systembackup}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: \/db\/backup$/ ) {  					#find the appropriate filesystem mount point
            $linux_hosts{$key}{linux_fs}{_db_backup}{hrStorageIndex} = $1;                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $linux_hosts{$key}{linux_fs}{_db_backup}{mount_point} = "/db/backup";                  	#save as a hash element instead of a hash key so we can query the value later
            print "      host:$linux_hosts{$key}{hostname}  mount_point:$linux_hosts{$key}{linux_fs}{_db_backup}{mount_point}  hrStorageIndex:$linux_hosts{$key}{linux_fs}{_db_backup}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
         if ( /hrStorageDescr.([0-9]+) = STRING: \/data$/ ) {  						#find the appropriate filesystem mount point
            $linux_hosts{$key}{linux_fs}{_db_backup}{hrStorageIndex} = $1;                   		#now we know the appropriate index to use for the AllocationUnits/Size/Used OIDs
            $linux_hosts{$key}{linux_fs}{_db_backup}{mount_point} = "/data";   	               		#save as a hash element instead of a hash key so we can query the value later
            print "      host:$linux_hosts{$key}{hostname}  mount_point:$linux_hosts{$key}{linux_fs}{_db_backup}{mount_point}  hrStorageIndex:$linux_hosts{$key}{linux_fs}{_db_backup}{hrStorageIndex} \n" if ($verbose eq "yes");
         }
      }                                                                					#end of while loop
      close IN;                                                         				#close filehandle
      #
      #
      @mount_points = ("root","_home","_repo01","_apps_oracle","_oracle","_grid","_systembackup","_db_backup","_backup");	#define array elements for filesystem mount points, substitute / character for _ because / is not a legal hash key character
      for $mount_point (@mount_points) {								#loop through for each mount point
         #
         # Now that we know the appropriate hrStorageIndex, get the hrStorageAllocationUnits
         #
         next unless ($linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageIndex});			#break out of foreach loop if the previous section failed to determine the hrStorageIndex
         $oid = ".1.3.6.1.2.1.25.2.3.1.4.$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageIndex}";	#SNMP OID for       hrStorageTable.hrStorageAllocationUnits.IndexNumber
         $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageAllocationUnits.IndexNumber
         print "   running command to check hrStorageAllocationUnits for host:$linux_hosts{$key}{hostname} mount point $linux_hosts{$key}{linux_fs}{$mount_point}{mount_point}: $cmd \n" if ($verbose eq "yes");
         open(IN,"$cmd 2>&1 |");                                           				#open filehandle using command output
         while (<IN>) {                                                   	 			#read a line from the command output
            # output should look similar to:
            # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.4.X
            # HOST-RESOURCES-MIB::hrStorageAllocationUnits.4 = INTEGER: 65536 Bytes
            #
            if ( /INTEGER: ([0-9]+) Bytes/ ) {    							#find the size of each allocation unit
               $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageAllocationUnits} = $1;		#value for hrStorageTable.hrStorageAllocationUnits.IndexNumber
               print "      host:$linux_hosts{$key}{hostname} hrStorageAllocationUnits:$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageAllocationUnits} \n" if ($verbose eq "yes");
            }
         }                                                                				#end of while loop
         close IN;                                                         				#close filehandle
         #
         # Now that we know the appropriate hrStorageIndex, get the hrStorageSize
         #
         next unless ($linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageIndex});			#break out of foreach loop if the previous section failed to determine the hrStorageIndex
         $oid = ".1.3.6.1.2.1.25.2.3.1.5.$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageIndex}";	#SNMP OID for       hrStorageTable.hrStorageSize.IndexNumber
         $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageSize.IndexNumber
         print "   running command to check hrStorageSize for host:$linux_hosts{$key}{hostname} mount_point:$linux_hosts{$key}{linux_fs}{$mount_point}{mount_point}: $cmd \n" if ($verbose eq "yes");
         open(IN,"$cmd 2>&1 |");                                           				#open filehandle using command output
         while (<IN>) {                                                   	 			#read a line from the command output
            # output should look similar to:
            # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.5.X
            # HOST-RESOURCES-MIB::hrStorageSize.4 = INTEGER: 522635
            #
            if ( /INTEGER: ([0-9]+)/ ) {    								#find the value
               $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageSize} = $1;				#value for hrStorageTable.hrStorageSize.IndexNumber
               $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageSize_GB} = sprintf("%.1f", $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageAllocationUnits}*$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageSize}/1024/1024/1024); #convert to GB
               print "      host:$linux_hosts{$key}{hostname} hrStorageSize:$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageSize_GB} GB \n" if ($verbose eq "yes");
            }
         }                                                                				#end of while loop
         close IN;                                                         				#close filehandle
         #
         # Now that we know the appropriate hrStorageIndex, get the hrStorageUsed 
         #
         next unless ($linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageIndex});			#break out of foreach loop if the previous section failed to determine the hrStorageIndex
         $oid = ".1.3.6.1.2.1.25.2.3.1.6.$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageIndex}";	#SNMP OID for       hrStorageTable.hrStorageUsed.IndexNumber
         $cmd = "$snmpget -v 1 -c $community $linux_hosts{$key}{hostname} $oid";			#get the value from hrStorageTable.hrStorageUsed.IndexNumber
         print "   running command to check hrStorageUsed for host:$linux_hosts{$key}{hostname} mount_point:$linux_hosts{$key}{linux_fs}{$mount_point}{mount_point}: $cmd \n" if ($verbose eq "yes");
         open(IN,"$cmd 2>&1 |");                                           				#open filehandle using command output
         while (<IN>) {                                                   	 			#read a line from the command output
            # output should look similar to:
            # $ snmpwalk   -v 1 -c public myhost01 .1.3.6.1.2.1.25.2.3.1.6.X
            # HOST-RESOURCES-MIB::hrStorageUsed.4 = INTEGER: 261948
            #
            if ( /INTEGER: ([0-9]+)/ ) {    								#find the value 
               $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed} = $1;				#value for hrStorageTable.hrStorageUsed.IndexNumber
               $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_GB} = sprintf("%.1f", $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageAllocationUnits}*$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed}/1024/1024/1024); #convert to GB
               print "      host:$linux_hosts{$key}{hostname}  $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_GB}GB  \n" if ($verbose eq "yes");
            }
         }                                                                				#end of while loop
         close IN;                                                         				#close filehandle
         #
         # At this point, we know the total bytes and bytes used.  Based on those values, calculate bytes free.
         #
         $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageFree_GB} = ( $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageSize_GB} - $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_GB} );			#calculate free space
         #
         # Let's also calculate percentages.
         #
         $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_pct} = sprintf( "%.1f", $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed} / $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageSize} * 100 );	#convert to percentage
         $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageFree_pct} = sprintf( "%.1f", (100 - $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_pct}) );					#calculate free percentage
         #
         print "      host:$linux_hosts{$key}{hostname}  TotalSize:$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageSize_GB}GB hrStorageUsed:$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_GB}GB($linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_pct}\%)  hrStorageFree:$linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageFree_GB}GB($linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageFree_pct}\%) \n" if ($verbose eq "yes");
      } 												#end of for loop
   } 													#end of foreach loop
} 													#end of subroutine




sub get_san_multipath_linux_status {
   #
   print "running get_san_multipath_linux_status subroutine \n" if ($verbose eq "yes");
   #
   # query all bare-metal Linux boxes that have iSCSI and/or Fibre Channel SAN paths using the built-in Linux dm-multipath package
   # HINT: this subroutine just execute an existing nagios check that is assumed to already exist.
   #       In other words, it is assumed the local machine is already monitoring Linux SAN paths via nagios, and this check just grabs the current status from that nagios check.
   #       The output of the /usr/local/nagios/libexec/check_linux_multipath script will look similar to the following:
   #       dm-multipath SAN disk paths OK - active:12 passive:0 faulty:0 shaky:0 | active=12;;;; passive=0;;;; faulty=0;;;; shaky=0;;;;
   #
   foreach $key (sort keys %san_multipath_linux_hosts) {
      #
      # initialize hash elements
      $san_multipath_linux_hosts{$key}{health}  = "UNKNOWN";   				#initialize hash element
      $san_multipath_linux_hosts{$key}{active}  = 0;    				#initialize hash element
      $san_multipath_linux_hosts{$key}{passive} = 0;    				#initialize hash element
      $san_multipath_linux_hosts{$key}{faulty}  = 0;    				#initialize hash element
      $san_multipath_linux_hosts{$key}{shaky}   = 0;    				#initialize hash element
      #
      #
      next unless ( $san_multipath_linux_hosts{$key}{ping} eq "up" );                   #skip hosts that do not respond to ping
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $san_multipath_linux_hosts{$key}{hostname} /usr/local/nagios/libexec/check_linux_multipath";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                          		        #open filehandle from command output
      while (<IN>) {                                                            	#read a line from the command output
         $san_multipath_linux_hosts{$key}{health}  = "OK"       if ( /SAN disk paths OK/       );
         $san_multipath_linux_hosts{$key}{health}  = "WARN"     if ( /SAN disk paths WARN/     );
         $san_multipath_linux_hosts{$key}{health}  = "CRITICAL" if ( /SAN disk paths CRITICAL/ );
         $san_multipath_linux_hosts{$key}{health}  = "UNKNOWN"  if ( /SAN disk paths UNKNOWN/  );
         $san_multipath_linux_hosts{$key}{active}  = $1         if ( /active:([0-9]+)/         );
         $san_multipath_linux_hosts{$key}{passive} = $1         if ( /passive:([0-9]+)/        );
         $san_multipath_linux_hosts{$key}{faulty}  = $1         if ( /faulty:([0-9]+)/         );
         $san_multipath_linux_hosts{$key}{shaky}   = $1         if ( /shaky:([0-9]+)/          );
         print "   health:$san_multipath_linux_hosts{$key}{health} active:$san_multipath_linux_hosts{$key}{active} passive:$san_multipath_linux_hosts{$key}{passive} faulty:$san_multipath_linux_hosts{$key}{faulty} shaky:$san_multipath_linux_hosts{$key}{shaky} \n" if ($verbose eq "yes");
      }                                                                         	#end of while loop
      close IN;                                                                 	#close filehandle
   } 											#end of foreach loop
} 											#end of subroutine




# NOTE: The iDRAC8 does not seem to support SNMP, so setup SSH key pairs and use racadm commands to get health metrics
sub get_dell_idrac8_status {
   #
   print "running get_dell_idrac8_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the Dell iDRAC8 service processor hosts to get the health status  by SNMP 
   #
   foreach $key (sort keys %idrac8_hosts) {
      next unless ( $idrac8_hosts{$key}{ping} eq "up" );						#skip hosts that do not respond to ping
      #
      # Different Dell iDRAC controllers may use slightly different OID values.
      $idrac8_hosts{$key}{GlobalSystemStatus}  = "unknown need SSH key pair";				#initialize hash element
      $idrac8_hosts{$key}{GlobalStorageStatus} = "unknown need SSH key pair";				#initialize hash element
      $idrac8_hosts{$key}{Model}               = "unknown need SSH key pair";				#initialize hash element
      $idrac8_hosts{$key}{ServiceTag}          = "unknown need SSH key pair";				#initialize hash element
   } 													#end of foreach loop
} 													#end of subroutine




sub get_dell_idrac9_status {
   #
   print "running get_dell_idrac9_status subroutine \n" if ($verbose eq "yes");
   #
   #
   # Different Dell iDRAC9 controllers may use slightly different OID values.
   # NOTE: The examples below may differ depending on the model of the IPMI controller
   #
   # .1.3.6.1.4.1.674.10892.5.2.1.0 GlobalSystemStatus 1=Other 2=Unknown 3=ok 4=nonCritical 5=Critical 6=nonRecoverable
   # GlobalSystemStatus             This attribute defines the overall rollup status of all components in the system being monitored by the remote access card.
   #
   # .1.3.6.1.4.1.674.10892.5.2.3.0 GlobalStorageStatus 1=Other 2=Unknown 3=ok 4=nonCritical 5=Critical 6=nonRecoverable
   # GlobalStorageStatus             This attribute defines the overall storage status being monitored by the remote access card.
   #
   # 1.3.6.1.4.1.674.10892.5.2.4.0  1=Other 2=Unknown 3=Off 4=On
   # systemPowerState               This attribute defines the power state of the system.
   #
   # 1.3.6.1.4.1.674.10892.5.2.5.0
   # systemPowerUpTime               This attribute defines the power-up time of the system in seconds
   #
   # 1.3.6.1.4.1.674.10892.5.1.3.2.0
   # systemServiceTag                This attribute defines the service tag of the system.
   #
   # 1.3.6.1.4.1.674.10892.5.1.3.12.0 Model number
   #
   #  
   # Command output will look similar to the following:
   #    $ /usr/bin/snmpget  -v 1 -c public idrac01 .1.3.6.1.4.1.674.10892.5.2.1.0   #OID for GlobalSystemStatus
   #    SNMPv2-SMI::enterprises.674.10892.5.2.1.0 = INTEGER: 3
   #
   #    $ /usr/bin/snmpget  -v 1 -c public idrac01 .1.3.6.1.4.1.674.10892.5.2.1.0   #OID for GlobalStorageStatus
   #    SNMPv2-SMI::enterprises.674.10892.5.2.1.0 = INTEGER: 3
   #
   #    $ /usr/bin/snmpget  -v 1 -c public idrac01 1.3.6.1.4.1.674.10892.5.1.3.2.0   #OID for systemServiceTag
   #    SNMPv2-SMI::enterprises.674.10892.5.1.3.2.0 = STRING: "JK38MXX"
   #
   #    $ /usr/bin/snmpget  -v 1 -c public idrac01 1.3.6.1.4.1.674.10892.5.1.3.12.0   #OID for Model
   #    SNMPv2-SMI::enterprises.674.10892.5.1.3.12.0 = STRING: "PowerEdge R740"
   #
   #
   #
   # Check the iDRAC SNMP OID for GlobalSystemStatus
   #
   # 
   # query all the Dell iDRAC service processor hosts to get the health status  by SNMP 
   #
   $community = $community_idrac9;                                            	#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %idrac9_hosts) {
      next unless ( $idrac9_hosts{$key}{ping} eq "up" );			#skip hosts that do not respond to ping
      $idrac9_hosts{$key}{snmp}               = "unknown";			#initialize hash element
      $idrac9_hosts{$key}{GlobalSystemStatus} = "unknown";			#initialize hash element
      $oid = ".1.3.6.1.4.1.674.10892.5.2.1.0";					#SNMP OID for GlobalSystemStatus
      $cmd = "$snmpget -v 1 -c $community $idrac9_hosts{$key}{hostname} $oid";	#define command to be run
      print "   running command to get iDRAC GlobalSystemStatus: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           	#open filehandle using command output
      while (<IN>) {                                                   	 	#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) {
            $idrac9_hosts{$key}{GlobalSystemStatus} = $1;			#value for GlobalSystemStatus
            $idrac9_hosts{$key}{GlobalSystemStatus} = "Other"          if ( $idrac9_hosts{$key}{GlobalSystemStatus} eq "1" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalSystemStatus} = "Unknown"        if ( $idrac9_hosts{$key}{GlobalSystemStatus} eq "2" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalSystemStatus} = "ok"             if ( $idrac9_hosts{$key}{GlobalSystemStatus} eq "3" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalSystemStatus} = "nonCritical"    if ( $idrac9_hosts{$key}{GlobalSystemStatus} eq "4" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalSystemStatus} = "Critical"       if ( $idrac9_hosts{$key}{GlobalSystemStatus} eq "5" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalSystemStatus} = "nonRecoverable" if ( $idrac9_hosts{$key}{GlobalSystemStatus} eq "6" );	#convert integer to human readable text
            $idrac9_hosts{$key}{snmp}               = "ok";									#finding a value here means we have working SNMP
         }                                                             		#end of if block
      }                                                                		#end of while loop
      close IN;                                                         	#close filehandle
      print "   host:$idrac9_hosts{$key}{hostname} GlobalSystemStatus:$idrac9_hosts{$key}{GlobalSystemStatus}  \n" if ($verbose eq "yes");
      #
      # Check the iDRAC SNMP OID for GlobalStorageStatus
      #
      $idrac9_hosts{$key}{GlobalStorageStatus} = "unknown";			#initialize hash element
      $oid = ".1.3.6.1.4.1.674.10892.5.2.3.0";					#SNMP OID for GlobalStorageStatus
      $cmd = "$snmpget -v 1 -c $community $idrac9_hosts{$key}{hostname} $oid";	#define command to be run
      print "   running command to get iDRAC GlobalStorageStatus: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           	#open filehandle using command output
      while (<IN>) {                                                   	 	#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) {
            $idrac9_hosts{$key}{GlobalStorageStatus} = $1;			#value for GlobalSystemStatus
            $idrac9_hosts{$key}{GlobalStorageStatus} = "Other"          if ( $idrac9_hosts{$key}{GlobalStorageStatus} eq "1" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalStorageStatus} = "Unknown"        if ( $idrac9_hosts{$key}{GlobalStorageStatus} eq "2" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalStorageStatus} = "ok"             if ( $idrac9_hosts{$key}{GlobalStorageStatus} eq "3" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalStorageStatus} = "nonCritical"    if ( $idrac9_hosts{$key}{GlobalStorageStatus} eq "4" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalStorageStatus} = "Critical"       if ( $idrac9_hosts{$key}{GlobalStorageStatus} eq "5" );	#convert integer to human readable text
            $idrac9_hosts{$key}{GlobalStorageStatus} = "nonRecoverable" if ( $idrac9_hosts{$key}{GlobalStorageStatus} eq "6" );	#convert integer to human readable text
         }                                                             		#end of if block
      }                                                                		#end of while loop
      close IN;                                                         	#close filehandle
      print "   host:$idrac9_hosts{$key}{hostname} GlobalStorageStatus:$idrac9_hosts{$key}{GlobalStorageStatus}  \n" if ($verbose eq "yes");
      #
      # Check the iDRAC SNMP OID for server Model number
      #
      $idrac9_hosts{$key}{Model} = "unknown";					#initialize hash element
      $oid = "1.3.6.1.4.1.674.10892.5.1.3.12.0";				#SNMP OID for Model
      $cmd = "$snmpget -v 1 -c $community $idrac9_hosts{$key}{hostname} $oid";	#define command to be run
      print "   running command to get iDRAC server Model: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           	#open filehandle using command output
      while (<IN>) {                                                   	 	#read a line from the command output
         s/"//g;								#get rid of " character 
         if ( / = STRING: ([a-zA-Z0-9 ]+)/ ) {
            $idrac9_hosts{$key}{Model} = $1;					#value for server Model number
         }                                                             		#end of if block
      }                                                                		#end of while loop
      close IN;                                                         	#close filehandle
      print "   host:$idrac9_hosts{$key}{hostname} Model:$idrac9_hosts{$key}{Model}  \n" if ($verbose eq "yes");
      #
      # Check the iDRAC SNMP OID for ServiceTag
      #
      $idrac9_hosts{$key}{ServiceTag} = "unknown";				#initialize hash element
      $oid = "1.3.6.1.4.1.674.10892.5.1.3.2.0";					#SNMP OID for ServiceTag
      $cmd = "$snmpget -v 1 -c $community $idrac9_hosts{$key}{hostname} $oid";	#define command to be run
      print "   running command to get iDRAC ServiceTag: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           	#open filehandle using command output
      while (<IN>) {                                                   	 	#read a line from the command output
         s/"//g;								#get rid of " character 
         if ( / = STRING: ([a-zA-Z0-9]+)/ ) {
            $idrac9_hosts{$key}{ServiceTag} = $1;				#value for ServiceTag
         }                                                             		#end of if block
      }                                                                		#end of while loop
      close IN;                                                         	#close filehandle
      print "   host:$idrac9_hosts{$key}{hostname} ServiceTag:$idrac9_hosts{$key}{ServiceTag}  \n" if ($verbose eq "yes");
   } 										#end of foreach loop
} 										#end of subroutine




sub get_emc_unisphere_status {
   #
   print "running get_emc_unisphere_status subroutine \n" if ($verbose eq "yes");
   #
   #
   # Different DellEMC UniSphere systems different OID values.
   # This assumes the use of the DELL-STORAGE-SC-MIB  (aka Compellent Storage)
   #
   # .1.3.6.1.4.1.674.11000.2000.500.1.2.6.0 1=other, 2=unknown, 3=ok), 4=noncritical, 5=critical, 6=nonrecoverable
   # productIDGlobalStatus	        Current status of the product. This is a rollup for the entire product including any monitored devices. 
   #                                 The status is intended to give initiative to an SNMP monitor to get further data when this status is abnormal. 
   #                                 The value here maps from the System Status icon on the SC GUI: grey->unknown, green->ok, yellow->noncritical, red->critical. 
   #                                 If the productIDGlobalStatus is not ok then scLastWorstAlert contains the scAlertNbr of the alert that is responsible for the negative status
   #
   # 1.3.6.1.4.1.674.11000.2000.500.1.2.44
   # scLastWorstAlert		If the productIDGlobalStatus is not ok then scLastWorstAlert contains the scAlertNbr of the alert that is responsible for the negative status.
   #
   # .1.3.6.1.4.1.674.11000.2000.500.1.2.13.1.3   1=up 2=down 3=degraded
   # scCtlrStatus	             	This attribute defines the status of a single controller
   #
   # .1.3.6.1.4.1.674.10892.5.2.3.0 GlobalStorageStatus 1=Other 2=Unknown 3=ok 4=nonCritical 5=Critical 6=nonRecoverable
   # GlobalStorageStatus             This attribute defines the overall storage status being monitored by the remote access card.
   #
   # .1.3.6.1.4.1.674.11000.2000.500.1.2.13.1.8
   # scCtrlServiceTag                This attribute defines the service tag of the system.
   #
   # .1.3.6.1.4.1.674.11000.2000.500.1.2.13.1.8
   # scCtlrModel			Model number of individual controller
   #
   # 1.3.6.1.4.1.674.11000.2000.500.1.2.1.0
   # productIDDisplayName		Name of this product for display purposes.  Example: Dell-Compellent Storage Center
   #
   # 1.3.6.1.4.1.674.11000.2000.500.1.2.5.0
   # productIDSerialNumber		The Dell Service Tag for the overall system (typically the same as the ssCtrlServiceTag for individual controllers)
   #  
   # 1.3.6.1.4.1.674.11000.2000.500.1.2.15.1.7
   # scEnclModel			enclosure model 
   #  
   # Command output will look similar to the following:
   #    $ /usr/bin/snmpget  -v 1 -c public unisphere01 .1.3.6.1.4.1.674.11000.2000.500.1.2.6.0   #OID for productIDGlobalStatus
   #    SNMPv2-SMI::enterprises.674.11000.2000.500.1.2.6.0 = INTEGER: 3
   #
   #    $ /usr/bin/snmpget  -v 1 -c public unisphere01 1.3.6.1.4.1.674.11000.2000.500.1.2.1.0A   #OID for productIDDisplayName
   #    SNMPv2-SMI::enterprises.674.11000.2000.500.1.2.1.0 = STRING: "Dell-Compellent Storage Center"
   #
   #    $ /usr/bin/snmpget  -v 1 -c public unisphere01 1.3.6.1.4.1.674.11000.2000.500.1.2.5.0    #OID for productIDSerialNumber (also ServiceTag)
   #    SNMPv2-SMI::enterprises.674.11000.2000.500.1.2.5.0 = STRING: "D9T9JXX"
   #
   #
   #
   #
   # query all the DellEMC UniSphere storage manager hosts to get the health status  by SNMP 
   #
   $community = $community_unisphere;                                            			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %unisphere_hosts) {
      next unless ( $unisphere_hosts{$key}{ping} eq "up" );						#skip hosts that do not respond to ping
      #
      # Check the UniSphere SNMP OID for productIDGlobalStatus
      #
      $unisphere_hosts{$key}{snmp}                  = "unknown";					#initialize hash element
      $unisphere_hosts{$key}{productIDGlobalStatus} = "unknown";					#initialize hash element
      $oid = ".1.3.6.1.4.1.674.11000.2000.500.1.2.6.0";							#SNMP OID for GlobalSystemStatus
      $cmd = "$snmpget -v 1 -c $community $unisphere_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get UniSphere productIDGlobalStatus: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           				#open filehandle using command output
      while (<IN>) {                                                   	 				#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) {
            $unisphere_hosts{$key}{productIDGlobalStatus} = $1;											#value for productIDGlobalStatus
            $unisphere_hosts{$key}{productIDGlobalStatus} = "Other"          if ( $unisphere_hosts{$key}{productIDGlobalStatus} eq "1" );	#convert integer to human readable text
            $unisphere_hosts{$key}{productIDGlobalStatus} = "Unknown"        if ( $unisphere_hosts{$key}{productIDGlobalStatus} eq "2" );	#convert integer to human readable text
            $unisphere_hosts{$key}{productIDGlobalStatus} = "ok"             if ( $unisphere_hosts{$key}{productIDGlobalStatus} eq "3" );	#convert integer to human readable text
            $unisphere_hosts{$key}{productIDGlobalStatus} = "nonCritical"    if ( $unisphere_hosts{$key}{productIDGlobalStatus} eq "4" );	#convert integer to human readable text
            $unisphere_hosts{$key}{productIDGlobalStatus} = "Critical"       if ( $unisphere_hosts{$key}{productIDGlobalStatus} eq "5" );	#convert integer to human readable text
            $unisphere_hosts{$key}{productIDGlobalStatus} = "nonRecoverable" if ( $unisphere_hosts{$key}{productIDGlobalStatus} eq "6" );	#convert integer to human readable text
            $unisphere_hosts{$key}{snmp}                  = "ok";										#finding a value here means we have working SNMP
         }                                                 			            		#end of if block
      }                                                                					#end of while loop
      close IN;                                                         				#close filehandle
      print "   host:$unisphere_hosts{$key}{hostname} productIDGlobalStatus:$unisphere_hosts{$key}{productIDGlobalStatus}  \n" if ($verbose eq "yes");
      #
      # Check the UniSphere SNMP OID for ServiceTag
      #
      $unisphere_hosts{$key}{ServiceTag} = "unknown";							#initialize hash element
      $oid = "1.3.6.1.4.1.674.11000.2000.500.1.2.5.0";							#SNMP OID for ServiceTag
      $cmd = "$snmpget -v 1 -c $community $unisphere_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get UniSphere ServiceTag: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           				#open filehandle using command output
      while (<IN>) {                                                   			 		#read a line from the command output
         s/"//g;											#get rid of " character 
         if ( / = STRING: ([a-zA-Z0-9]+)/ ) {
            $unisphere_hosts{$key}{ServiceTag} = $1;							#value for ServiceTag
         }                                                             					#end of if block
      }                                                                					#end of while loop
      close IN;                                                        			 		#close filehandle
      print "   host:$unisphere_hosts{$key}{hostname} ServiceTag:$unisphere_hosts{$key}{ServiceTag}  \n" if ($verbose eq "yes");
   } 													#end of foreach loop
} 													#end of subroutine



sub get_ibm_imm2_status {
   #
   print "running get_ibm_imm2_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the IBM xSeries IMM2 service processors via SNMP to get the health status
   # HINT: this subroutine just execute an existing nagios check that is assumed to already exist.
   #       In other words, it is assumed the local machine is already monitoring IBM xSeries IMM2 service processors via nagios, and this check just grabs the current status from that nagios check.
   #
   foreach $key (sort keys %ibm_imm2_hosts) {
      #
      my $nagios_tempfile = "/tmp/nagios.check_ibm_imm2.$ibm_imm2_hosts{$key}{hostname}";	#location of temporary file used by nagios check
      #
      # The temporary file created by the nagios check will have content similar to the following:
      # $  cat /tmp/nagios.check_ibm_imm2.somehostname.example.com
      # IBM IMM2 OK - System_Health:Normal  Ambient_Temperature:19.0C  Power_Status:Normal  RAM:512GB  CPU_speed:2600Mhz  CPU_sockets:2  CPU_cores:12  CPU_threads:24 
      #
      # initialize hash elements
      $ibm_imm2_hosts{$key}{Model_Number}        = "UNKNOWN";    				#initialize hash element
      $ibm_imm2_hosts{$key}{Serial_Number}       = "UNKNOWN";    				#initialize hash element
      $ibm_imm2_hosts{$key}{System_Health}       = "UNKNOWN";    				#initialize hash element
      $ibm_imm2_hosts{$key}{Power_Status}        = "UNKNOWN";    				#initialize hash element
      $ibm_imm2_hosts{$key}{Ambient_Temperature} = "UNKNOWN";    				#initialize hash element
      #
      # run this section if the nagios temporary file cannot be found, which would indicate a problem with nagios
      #
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 1 minute to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         $ibm_imm2_hosts{$key}{health} = "UNKNOWN, cannot find nagios check output in file: $nagios_tempfile";    			#save value to hash
         print "   ibm_imm2_health:$ibm_imm2_hosts{$key}{health} \n" if ($verbose eq "yes");
      }
      # 
      # run this section if the nagios temporary file exists
      #
      print "   reading file $nagios_tempfile \n" if ($verbose eq "yes");
      open(IN,"$nagios_tempfile") or warn "Cannot open /tmp/nagios.check_ibm_imm2_hosts{$key}{hostname} file for reading $! \n";
      while (<IN>) {                                                            #read a line from the command output
         if ( /^IBM IMM2/ ) {                               			#find health metric
            $ibm_imm2_hosts{$key}{Model_Number}        = $1 if ( /Model:([a-zA-Z0-9\-]+)/            );
            $ibm_imm2_hosts{$key}{Serial_Number}       = $1 if ( /Serial:([a-zA-Z0-9\-]+)/           );
            $ibm_imm2_hosts{$key}{System_Health}       = $1 if ( /System_Health:([a-zA-Z0-9]+)/      );
            $ibm_imm2_hosts{$key}{Power_Status}        = $1 if ( /Power_Status:([a-zA-Z0-9]+)/       );
            $ibm_imm2_hosts{$key}{Ambient_Temperature} = $1 if ( /Ambient_Temperature:([0-9\.]+)/    );
            print "   System_Health:$ibm_imm2_hosts{$key}{System_Health} Power_Status:$ibm_imm2_hosts{$key}{Power_Status} Ambient_Temperature:$ibm_imm2_hosts{$key}{Ambient_Temperature}C \n" if ($verbose eq "yes");
         } 
      }                                                                         #end of while loop
      close IN;                                                                 #close filehandle
   } 										#end of foreach loop
} 										#end of subroutine








sub get_lenovo_xclarity_status {
   #
   print "running get_lenovo_xclarity_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the Lenovo xClarity service processor hosts to get the health status via SSH
   # HINT: in environments where nagios is already in use, the nagios user may have SSH key pairs already configured.
   #
   # It is assumed that SSH key pairs are already configured for password-less logins, using the following procedure:
   #       Ensure that SSH key pairs are configured correctly by attempting to SSH into the remote host as the nagios user.
   #      If you get prompted for a password, SSH key pair authentication is not working.
   #      Login to the xClarity controller, click BMC Configuration, User/LDAP, create a user called nagios, paste in contents of $HOME/.ssh/id_rsa.pub  
   #
   foreach $key (sort keys %xclarity_hosts) {
      $xclarity_hosts{$key}{ssh} = "unknown";					#initialize hash element
      #
      #
      # initialize hash elements
      $xclarity_hosts{$key}{syshealth}{summary}{Cooling_Devices} = "unknown";
      $xclarity_hosts{$key}{syshealth}{summary}{Power_Modules}   = "unknown";
      $xclarity_hosts{$key}{syshealth}{summary}{Local_Storage}   = "unknown";
      $xclarity_hosts{$key}{syshealth}{summary}{Processors}      = "unknown";
      $xclarity_hosts{$key}{syshealth}{summary}{Memory}          = "unknown";
      $xclarity_hosts{$key}{syshealth}{summary}{System}          = "unknown";
      $xclarity_hosts{$key}{temperature}{ambient}                = 9999;	#use numeric dummy value instead of "unknown" so we can do math against it
      $xclarity_hosts{$key}{vpd}{sys}{Model}                     = "unknown";
      $xclarity_hosts{$key}{vpd}{sys}{Serial}                    = "unknown";
      #
      #
      # SSH into the xClarity service processor to get health status
      # Expected output will look similar to:
      #   system> syshealth summary
      #   Power     On
      #   State     Booting OS or in undetected OS
      #   Restarts  14
      #   Component Type     Status
      #   ==================================
      #   Cooling Devices    Normal
      #   Power Modules      Warning
      #   Local Storage      Normal
      #   Processors         Normal
      #   Memory             Normal
      #   System             Normal     
      #
      next unless ( $xclarity_hosts{$key}{ping} eq "up" );					#skip hosts that do not respond to ping
      #
      # confirm SSH is working
      #
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $xclarity_hosts{$key}{hostname} syshealth summary";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                    #open filehandle from command output
      while (<IN>) {                                                            #read a line from the command output
         if ( /^Cooling Devices +([a-zA-Z]+)/ ) {                               #find health metric
            $xclarity_hosts{$key}{ssh} = "ok";    				#finding a value here means we have working SSH
         }                                                                      #end of if block
      } 									# end of while loop 
      #
      # at this point, we know SSH is working, so continue with the rest of the checks
      #
      next unless ( $xclarity_hosts{$key}{ssh} eq "ok" );			#skip hosts that do not respond to ssh
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $xclarity_hosts{$key}{hostname} syshealth summary";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                    #open filehandle from command output
      while (<IN>) {                                                            #read a line from the command output
         if ( /^Cooling Devices +([a-zA-Z]+)/ ) {                               #find health metric
            $xclarity_hosts{$key}{syshealth}{summary}{Cooling_Devices} = $1;    #save value to hash
            print "   Cooling_Devices:$xclarity_hosts{$key}{syshealth}{summary}{Cooling_Devices} \n" if ($verbose eq "yes");
         }                                                                      #end of if block
         if ( /^Power Modules +([a-zA-Z]+)/ ) {                                 #find health metric
            $xclarity_hosts{$key}{syshealth}{summary}{Power_Modules} = $1;      #save value to hash
            print "   Power_Modules:$xclarity_hosts{$key}{syshealth}{summary}{Power_Modules} \n" if ($verbose eq "yes");
         }                                                                      #end of if block
         if ( /^Local Storage +([a-zA-Z]+)/ ) {                                 #find health metric
            $xclarity_hosts{$key}{syshealth}{summary}{Local_Storage} = $1;      #save value to hash
            print "   Local_Storage:$xclarity_hosts{$key}{syshealth}{summary}{Local_Storage} \n" if ($verbose eq "yes");
         }                                                                      #end of if block
         if ( /^Processors +([a-zA-Z]+)/ ) {                                    #find health metric
            $xclarity_hosts{$key}{syshealth}{summary}{Processors} = $1;         #save value to hash
            print "   Processors:$xclarity_hosts{$key}{syshealth}{summary}{Processors} \n" if ($verbose eq "yes");
         }                                                                      #end of if block
         if ( /^Memory +([a-zA-Z]+)/ ) {                                        #find health metric
            $xclarity_hosts{$key}{syshealth}{summary}{Memory} = $1;             #save value to hash
            print "   Memory:$xclarity_hosts{$key}{syshealth}{summary}{Memory} \n" if ($verbose eq "yes");
         }                                                                      #end of if block
         if ( /^System +([a-zA-Z]+)/ ) {                                        #find health metric
            $xclarity_hosts{$key}{syshealth}{summary}{System} = $1;             #save value to hash
            print "   System:$xclarity_hosts{$key}{syshealth}{summary}{System} \n" if ($verbose eq "yes");
         }                                                                      #end of if block
      }                                                                         #end of while loop
      close IN;                                                                 #close filehandle
      #
      # Get the VPD (Vital Product Data) from the xClarity Controller.  We are most interested in model/serial/firmware.
      #
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes  $xclarity_hosts{$key}{hostname} vpd sys";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                    #open filehandle from command output
      while (<IN>) {                                                            #read a line from the command output
         next if (/^Machine Type/);					     	#skip header row
         next if (/^\-/);					     	     	#skip header row
         if ( /^([a-zA-Z0-9]+) +([a-zA-Z0-9]+)/ ) {                             #find health metric
            $xclarity_hosts{$key}{vpd}{sys}{Model}  = $1;                       #save value to hash
            $xclarity_hosts{$key}{vpd}{sys}{Serial} = $2;                       #save value to hash
            print "   Model:$xclarity_hosts{$key}{vpd}{sys}{Model} Serial:$xclarity_hosts{$key}{vpd}{sys}{Serial} \n" if ($verbose eq "yes");
         }                                                                      #end of if block
      }                                                                         #end of while loop
      close IN;                                                                 #close filehandle
      #
      # Get the ambient temperature at the air inlet vents
      #
      # # Sample output is shown below:
      #   system> temps
      #   Temperatures are displayed in degrees Fahrenheit/Celsius
      #                    WR            W             T             SS            HS
      #   ---------------------------------------------------------------------------------------
      #   CPU1 Temp        N/A           N/A           93.20/34.00   N/A           N/A
      #   CPU1 DTS         N/A           N/A           -59.80/-51.00 32.00/-0.20   32.00/0.00
      #   DIMM 1 Temp      N/A           N/A           80.60/27.00   N/A           N/A
      #   DIMM 2 Temp      N/A           N/A           80.60/27.00   N/A           N/A
      #   DIMM 3 Temp      N/A           N/A           84.20/29.00   N/A           N/A
      #   DIMM 4 Temp      N/A           N/A           84.20/29.00   N/A           N/A
      #   DIMM 5 Temp      N/A           N/A           82.40/28.00   N/A           N/A
      #   DIMM 6 Temp      N/A           N/A           82.40/28.00   N/A           N/A
      #   DIMM 7 Temp      N/A           N/A           80.60/27.00   N/A           N/A
      #   DIMM 8 Temp      N/A           N/A           80.60/27.00   N/A           N/A
      #   DIMM 9 Temp      N/A           N/A           78.80/26.00   N/A           N/A
      #   DIMM 10 Temp     N/A           N/A           78.80/26.00   N/A           N/A
      #   DIMM 11 Temp     N/A           N/A           77.00/25.00   N/A           N/A
      #   DIMM 12 Temp     N/A           N/A           77.00/25.00   N/A           N/A
      #   PCH Temp         N/A           N/A           105.80/41.00  N/A           N/A
      #   Ambient Temp     109.40/43     109.40/43.00  62.60/17.00   116.60/47.00  122.00/50.00
      #   Exhaust Temp     N/A           N/A           69.80/21.00   N/A           N/A
      #
      #   column headings:
      #        WR is warning reset (Positive-going Threshold Hysteresis value)
      #        W is warning (Upper non-critical Threshold)
      #        T is temperature (current)
      #        SS is soft shutdown (Upper critical Threshold)
      #        HS is hard shutdown (Upper non-recoverable Threshold) 
      #
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes  $xclarity_hosts{$key}{hostname} temps";
      print "   running command to get temperature readings: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                    #open filehandle from command output
      while (<IN>) {                                                            #read a line from the command output
         next if (/^\-/);					     	     	#skip header row
         if ( /^Ambient Temp +[0-9\.\/]+ +[0-9\.\/]+ +[0-9\.]+\/([0-9\.]+)/ ) {   #find ambient temperature
            $xclarity_hosts{$key}{temperature}{ambient}  = $1;                       #save value to hash
            print "   Ambient_Temperature:$xclarity_hosts{$key}{temperature}{ambient}C \n" if ($verbose eq "yes");
         }                                                                      #end of if block
      }                                                                         #end of while loop
      close IN;                                                                 #close filehandle
   } 										#end of foreach loop
} 										#end of subroutine





sub get_brocade_status {
   #
   print "running get_brocade_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the Brocade fibre channel switches to get the health status  by SNMP 
   #
   $community = $community_brocade;                           			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %brocade_hosts) {
      #
      #
      $brocade_hosts{$key}{snmp}          = "unknown";				#initialize hash element
      $brocade_hosts{$key}{switch_type}   = "unknown";				#initialize hash element
      $brocade_hosts{$key}{switch_status} = "unknown";				#initialize hash element
      next unless ( $brocade_hosts{$key}{ping} eq "up" );			#skip hosts that do not respond to ping
      #
      # Get the Brocade switch model number
      #
      $oid = ".1.3.6.1.2.1.47.1.1.1.1.2.1";					#SNMP OID for switch type
      $cmd = "$snmpget -v 1 -c $community $brocade_hosts{$key}{hostname} $oid";	#define command to be run
      print "   running command to get Brocade switch model type: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           	#open filehandle using command output
      while (<IN>) {                                                   	 	#read a line from the command output
         s/"//g;								#get rid of " character to simplify regex
         if ( /STRING: ([0-9a-zA-Z_\.]+)/ ) {  					#look for a response to the snmp query
            $brocade_hosts{$key}{switch_type} = $1;				#value for switch type / model number
            $brocade_hosts{$key}{snmp}        = "ok";				#finding a value here means we have working SNMP
         }                                                             		#end of if block
      }                                                                		#end of while loop
      close IN;                                                         	#close filehandle
      print "   host:$brocade_hosts{$key}{hostname} switch_type:$brocade_hosts{$key}{switch_type}  \n" if ($verbose eq "yes");
      #
      # Get the Brocade switch health status
      #
      #  OID: 1.3.6.1.4.1.1588.2.1.1.1.1.20.0 
      # Possible OID values:
      #   1 - sw-ok                    switch OK
      #   2 - sw-faulty                The switch has experienced an unknown fault
      #   3 - sw-embedded-port-fault   The switch has experienced an embedded port fault
      #
      $oid = "1.3.6.1.4.1.1588.2.1.1.1.1.20.0"; 
      $cmd = "$snmpget -v 1 -c $community $brocade_hosts{$key}{hostname} $oid";	#define command to be run
      print "   running command to get Brocade switch health status: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd |"); 							#open a filehandle for reading 
      while (<IN>) {                          					#read a line from STDIN
         if ( /INTEGER: ([0-9]+)/ ) {  						#look for a response to the snmp query
            $brocade_hosts{$key}{switch_status} = $1;				#assign more mnemonic variable name (1=ok 2=faulty 3=embedded-port-fault)
            $brocade_hosts{$key}{switch_status} = "OK"                  if ($brocade_hosts{$key}{switch_status} eq "1");	#change integer to human readable value
            $brocade_hosts{$key}{switch_status} = "Unknown fault"       if ($brocade_hosts{$key}{switch_status} eq "2");	#change integer to human readable value
            $brocade_hosts{$key}{switch_status} = "Embedded port fault" if ($brocade_hosts{$key}{switch_status} eq "3");	#change integer to human readable value
            print "   switch_status is $brocade_hosts{$key}{switch_status}  \n" if ($verbose eq "yes");
         } 									#end of if block
      }										#end of while loop
      close IN;									#close filehandle
      #
      print "   host:$brocade_hosts{$key}{hostname} switch_status:$brocade_hosts{$key}{switch_status}  \n" if ($verbose eq "yes");
   } 										#end of foreach loop
} 										#end of subroutine



sub get_flashsystem_status {
   #
   print "running get_flashsystem_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the IBM FlashSystem storage systems via SSH to get the health status via SSH
   # HINT: this subroutine just execute an existing nagios check that is assumed to already exist.
   #       In other words, it is assumed the local machine is already monitoring FlashSystem storage via nagios, and this check just grabs the current status from that nagios check.
   #
   foreach $key (sort keys %flashsystem_hosts) {
      #
      my $nagios_tempfile = "/tmp/nagios.check_ibm_flashsystem.$flashsystem_hosts{$key}{hostname}";	#location of temporary file used by nagios check
      #
      # The temporary file created by the nagios check will have content similar to the following:
      # $  cat /tmp/nagios.check_ibm_flashsystem.fs7200.example.com
      # FlashSystem health OK. cluster_name:FS7200-PROD cpu_util:2% config_node:node2 node_count:2 code_level:8.3.1.2 smtp:172.16.0.21 vdisks:5 mdisks:1 pdisks:16 external_storage_systems:0 consistency_groups:0 metro_mirrors:0 vdisk_read_latency:1ms vdisk_write_latency:0ms | CPU_util:4%;;;; vdisk_read_latency_ms:0;;;; vdisk_write_latency_ms:0;;;;
      #
      # initialize hash element
      $flashsystem_hosts{$key}{health}                 = "UNKNOWN"; 		#initialize to avoid undef errors
      $flashsystem_hosts{$key}{cluster_name}           = "UNKNOWN";    		#initialize to avoid undef errors
      $flashsystem_hosts{$key}{cpu_util}               = 9999;    		#dummy integer value to avoid undef errors
      $flashsystem_hosts{$key}{vdisk_read_latency_ms}  = 9999;    		#dummy integer value to avoid undef errors
      $flashsystem_hosts{$key}{vdisk_write_latency_ms} = 9999;    		#dummy integer value to avoid undef errors
      #
      # run this section if the nagios temporary file cannot be found, which would indicate a problem with nagios
      #
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 5 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 4 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 3 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 2 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 1 minute  to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         $flashsystem_hosts{$key}{health} = "UNKNOWN, cannot find nagios check output in file: $nagios_tempfile";    			#save value to hash
         print "   FlashSystem_health:$flashsystem_hosts{$key}{health} \n" if ($verbose eq "yes");
      }
      # 
      # run this section if the nagios temporary file exists
      #
      print "   reading file $nagios_tempfile \n" if ($verbose eq "yes");
      open(IN,"$nagios_tempfile") or warn "Cannot open /tmp/nagios.check_ibm_flashsystem.$flashsystem_hosts{$key}{hostname} file for reading $! \n";
      while (<IN>) {                                                            #read a line from the command output
         if ( /^FlashSystem health/ ) {                               		#find health metric
            $flashsystem_hosts{$key}{health}                 = "OK"       if (/FlashSystem health OK/      ); 	
            $flashsystem_hosts{$key}{health}                 = "WARN"     if (/FlashSystem health WARN/    ); 
            $flashsystem_hosts{$key}{health}                 = "CRITICAL" if (/FlashSystem health CRITICAL/); 
            $flashsystem_hosts{$key}{cluster_name}           = $1         if (/cluster_name:([a-zA-Z0-9_\-\.]+)/);
            $flashsystem_hosts{$key}{cpu_util}               = $1         if (/cpu_util:([0-9]+)/);
            $flashsystem_hosts{$key}{vdisk_read_latency_ms}  = $1         if (/vdisk_read_latency:([0-9]+)/);
            $flashsystem_hosts{$key}{vdisk_write_latency_ms} = $1         if (/vdisk_write_latency:([0-9]+)/);
            print "   FlashSystem_health:$flashsystem_hosts{$key}{health} cluster_name:$flashsystem_hosts{$key}{cluster_name} cpu_util:$flashsystem_hosts{$key}{cpu_util}\% read_latency:$flashsystem_hosts{$key}{vdisk_read_latency_ms}ms write_latency:$flashsystem_hosts{$key}{vdisk_write_latency_ms}ms \n" if ($verbose eq "yes");
         } 
      }                                                                         #end of while loop
      close IN;                                                                 #close filehandle
   } 										#end of foreach loop
} 										#end of subroutine




sub get_qnap_status {
   #
   print "running get_qnap_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the IBM FlashSystem storage systems via SSH to get the health status via SSH
   # HINT: this subroutine just execute an existing nagios check that is assumed to already exist.
   #       In other words, it is assumed the local machine is already monitoring FlashSystem storage via nagios, and this check just grabs the current status from that nagios check.
   #
   foreach $key (sort keys %qnap_hosts) {
      #
      my $nagios_tempfile = "/tmp/nagios.check_qnap_nas.$qnap_hosts{$key}{hostname}";	#location of temporary file used by nagios check
      #
      # The temporary file created by the nagios check will have content similar to the following:
      # $  cat /tmp/nagios.check_qnap_nas.mynas01.example.com
      # QNAP NAS Health OK - OverallHealth:GOOD DiskCount:12 AverageTemperature:24.9C/65.9F Model:TVS-1271U-RP Serial:Q15CI10XXX fan_count:3 fan_rpm:4571 | AverageTemperatureC:24.9;;;; AverageTemperatureF:65.9;;;; fan_rpm:4571
      #
      # initialize hash element
      $qnap_hosts{$key}{health} = "UNKNOWN";    				#save value to hash
      next unless ( $qnap_hosts{$key}{ping} eq "up" );				#skip hosts that do not respond to ping
      #
      # run this section if the nagios temporary file cannot be found, which would indicate a problem with nagios
      #
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 5 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 4 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 3 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 2 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 1 minute  to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         $qnap_hosts{$key}{health} = "UNKNOWN, cannot find nagios check output in file: $nagios_tempfile";    			#save value to hash
         print "   qnap_health:$qnap_hosts{$key}{health} \n" if ($verbose eq "yes");
      }
      # 
      # run this section if the nagios temporary file exists
      #
      print "   reading file $nagios_tempfile \n" if ($verbose eq "yes");
      open(IN,"$nagios_tempfile") or warn "Cannot open /tmp/nagios.check_qnap_nas.$qnap_hosts{$key}{hostname} file for reading $! \n";
      while (<IN>) {                                                            #read a line from the command output
         if ( /^QNAP NAS Health/ ) {                               		#find health metric
            s/\|.*//g;								#get rid of nagios performance data after the | character, not relevant for this report
            $qnap_hosts{$key}{health} = $_;    					#save details of problem to hash
            print "   qnap_health:$qnap_hosts{$key}{health} \n" if ($verbose eq "yes");
         } 
      }                                                                         #end of while loop
      close IN;                                                                 #close filehandle
   } 										#end of foreach loop
} 										#end of subroutine




sub get_netapp_status {
   #
   print "running get_netapp_status subroutine \n" if ($verbose eq "yes");
   #
   $community = $community_netapp;                                              #set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   # query all the NetApp ONTAP storage systems via  SNMP
   #
   #  1.3.6.1.4.1.789.1.2.2.4.0 miscGlobalStatus 1=other 2=unknown 3=ok 4=nonCritical 5=critical 6=nonRecoverable
   #  This indicates the overall status of the appliance.  The algorithm to determine the value uses both
   #  hardware status (e.g. the number of failed fans) and volume status (e.g. number of volumes that are full).
   #  The algorithm is subject to change in future releases, but the range of values will not change.
   #
   #  Sample output: 
   #  $ snmpget -v 1 -c public netapp01 .1.3.6.1.4.1.789.1.2.2.4.0
   #  SNMPv2-SMI::enterprises.789.1.2.2.4.0 = INTEGER: 3                <--  1=other 2=unknown 3=ok 4=nonCritical 5=critical 6=nonRecoverable
   #
   #  Sample output for sysDescr OID, which contains the ONTAP version
   #  $ snmpwalk -v 1 -c public filer01.example.com .1.3.6.1.2.1.1.1.0
   #  SNMPv2-MIB::sysDescr.0 = STRING: NetApp Release 9.9.1P3: Wed Sep 29 12:55:55 UTC 2021
   #
   #
   #
   foreach $key (sort keys %netapp_hosts) {
      #
      # Confirm SNMP is working
      #
      $netapp_hosts{$key}{snmp}          = "unknown";   		                               	#initialize hash element
      $netapp_hosts{$key}{ontap_version} = "";   		                               	#initialize hash element
      $oid = ".1.3.6.1.2.1.1.1.0";                                                      	#SNMP OID for sysDescr
      $cmd = "$snmpget -v 1 -c $community $netapp_hosts{$key}{hostname} $oid";                  #define command to be run
      print "   running command to get sysName: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                                                   #open filehandle using command output
      while (<IN>) {                                                                            #read a line from the command output
         s/"//g; 										#get rid of " character to make regex simpler
         if ( / = STRING: NetApp Release ([a-zA-Z0-9 \.]+):/ ) { 				#Capture the ONTAP version
            $netapp_hosts{$key}{ontap_version} = $1;                                         	#value for currently running ONTAP version
            $netapp_hosts{$key}{snmp}          = "ok";                                         	#finding a value here means we have working SNMP
         }                                                                                      #end of if block
      }                                                                                         #end of while loop
      close IN;                                                                                 #close filehandle
      print "   host:$netapp_hosts{$key}{hostname} ontap_version:$netapp_hosts{$key}{ontap_version} \n" if ($verbose eq "yes");

      #
      # Check the NetApp ONTAP SNMP OID for the overall health of the hardware and software
      #
      $netapp_hosts{$key}{miscGlobalStatus} = "Unknown";                                        #initialize hash element
      $oid = ".1.3.6.1.4.1.789.1.2.2.4.0";                                                      #SNMP OID for all physical memory module condition / status / health
      $cmd = "$snmpget -v 1 -c $community $netapp_hosts{$key}{hostname} $oid";                  #define command to be run
      print "   running command to get netapp global status: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                                                   #open filehandle using command output
      while (<IN>) {                                                                            #read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) {
            $netapp_hosts{$key}{miscGlobalStatus} = $1;                                         #value for GlobalSystemStatus
            $netapp_hosts{$key}{miscGlobalStatus} = "Other"          if ( $netapp_hosts{$key}{miscGlobalStatus} eq "1" );   #convert integer to human readable text
            $netapp_hosts{$key}{miscGlobalStatus} = "Unknown"        if ( $netapp_hosts{$key}{miscGlobalStatus} eq "2" );   #convert integer to human readable text
            $netapp_hosts{$key}{miscGlobalStatus} = "OK"             if ( $netapp_hosts{$key}{miscGlobalStatus} eq "3" );   #convert integer to human readable text
            $netapp_hosts{$key}{miscGlobalStatus} = "nonCritical"    if ( $netapp_hosts{$key}{miscGlobalStatus} eq "4" );   #convert integer to human readable text
            $netapp_hosts{$key}{miscGlobalStatus} = "Critical"       if ( $netapp_hosts{$key}{miscGlobalStatus} eq "5" );   #convert integer to human readable text
            $netapp_hosts{$key}{miscGlobalStatus} = "nonRecoverable" if ( $netapp_hosts{$key}{miscGlobalStatus} eq "6" );   #convert integer to human readable text
         }                                                                                      #end of if block
      }                                                                                         #end of while loop
      close IN;                                                                                 #close filehandle
      print "   host:$netapp_hosts{$key}{hostname} miscGlobalStatus:$netapp_hosts{$key}{miscGlobalStatus} \n" if ($verbose eq "yes");
   }                                                                                            #end of foreach loop
}                                                                                               #end of subroutine



sub get_ciscoios_status {
   #
   print "running get_ciscoios_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the Cisco IOS devices get the health status  by SNMP
   #
   # .1.3.6.1.4.1.9.9.109.1.1.1.1.8    cpmCPUTotal5minRev       Five minute average of all processor utilization
   # Sample output:   snmpwalk -v 1 -c public switchstack01  .1.3.6.1.4.1.9.9.109.1.1.1.1.8
   # SNMPv2-SMI::enterprises.9.9.109.1.1.1.1.8.11 = Gauge32: 6
   # SNMPv2-SMI::enterprises.9.9.109.1.1.1.1.8.12 = Gauge32: 4
   # SNMPv2-SMI::enterprises.9.9.109.1.1.1.1.8.13 = Gauge32: 3
   # SNMPv2-SMI::enterprises.9.9.109.1.1.1.1.8.14 = Gauge32: 4
   #
   $community = $community_ciscoios;                                                            #set SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %ciscoios_hosts) {
      $ciscoios_hosts{$key}{snmp} = "unknown";                                                  #initialize hash element
      #
      #
      # Get the ciscoios CPU utilization
      #
      $ciscoios_hosts{$key}{cpu_util} = 0;                                                      #initialize hash element
      $count = 0;                                                                               #initialize counter variable
      $oid = ".1.3.6.1.4.1.9.9.109.1.1.1.1.8";                                                  #SNMP OID for CPU utilization percentage
      $cmd = "$snmpwalk -v 1 -c $community $ciscoios_hosts{$key}{hostname} $oid";               #define command to be run
      print "   running command to get ciscoios CPU utilization: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                                                   #open filehandle using command output
      while (<IN>) {                                                                            #read a line from the command output
         s/"//g;                                                                                #get rid of " character to simplify regex
         if ( /Gauge32: ([0-9]+)/ ) {                                                           #look for a response to the snmp query
            $ciscoios_hosts{$key}{cpu_util} = $ciscoios_hosts{$key}{cpu_util}+ $1;              #running total of all processors
            $count++;                                                                           #increment counter for number of processors
            $ciscoios_hosts{$key}{snmp} = "ok";              					#finding a value here means we  have working SNMP
         }                                                                                      #end of if block
      }                                                                                         #end of while loop
      close IN;                                                                                 #close filehandle
      $ciscoios_hosts{$key}{cpu_util} = $ciscoios_hosts{$key}{cpu_util} / $count;               #calculate average CPU util across all processors
      $ciscoios_hosts{$key}{cpu_util} = sprintf("%.0f",$ciscoios_hosts{$key}{cpu_util});        #truncate to 0 decimal places
      print "   host:$ciscoios_hosts{$key}{hostname} cpu_util:$ciscoios_hosts{$key}{cpu_util}\% \n" if ($verbose eq "yes");
   }                                                                                            #end of foreach loop
}                                                                                               #end of subroutine






sub get_fortigate_status {
   #
   print "running get_fortigate_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the Brocade fibre channel switches to get the health status  by SNMP 
   #
   $community = $community_fortigate;                           			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %fortigate_hosts) {
      $fortigate_hosts{$key}{snmp} = "unknown";					#initialize value to avoid undef errors
      $fortigate_hosts{$key}{cpu_util} = 0;					#initialize value to avoid undef errors
      next unless ( $fortigate_hosts{$key}{ping} eq "up" );			#skip hosts that do not respond to ping
      #
      #
      # Get the fortigate CPU utilization
      #
      $oid = ".1.3.6.1.4.1.12356.101.4.1.3.0";					#SNMP OID for CPU utilization percentage
      $cmd = "$snmpget -v 1 -c $community $fortigate_hosts{$key}{hostname} $oid";	#define command to be run
      print "   running command to get fortigate CPU utilization: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           	#open filehandle using command output
      while (<IN>) {                                                   	 	#read a line from the command output
         s/"//g;								#get rid of " character to simplify regex
         if ( /Gauge32: ([0-9]+)/ ) {  						#look for a response to the snmp query
            $fortigate_hosts{$key}{cpu_util} = $1;				#value for CPU % utilization
            $fortigate_hosts{$key}{snmp}     = "ok";				#finding a value here means we have working SNMP
         }                                                             		#end of if block
      }                                                                		#end of while loop
      close IN;                                                         	#close filehandle
      #
      # Get the fortigate RAM utilization
      #
      $oid = ".1.3.6.1.4.1.12356.101.4.1.4.0";					#SNMP OID for memory utilization percentage
      $cmd = "$snmpget -v 1 -c $community $fortigate_hosts{$key}{hostname} $oid";	#define command to be run
      print "   running command to get fortigate RAM utilization: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           	#open filehandle using command output
      while (<IN>) {                                                   	 	#read a line from the command output
         s/"//g;								#get rid of " character to simplify regex
         if ( /Gauge32: ([0-9]+)/ ) {  						#look for a response to the snmp query
            $fortigate_hosts{$key}{ram_util} = $1;				#value for memory % utilization
         }                                                             		#end of if block
      }                                                                		#end of while loop
      close IN;                                                         	#close filehandle
      #
      # Get the fortigate current bandwidth utilization 
      # 1.3.6.1.4.1.12356.101.13.2.1.1.5 
      # {iso(1) identified-organization(3) dod(6) internet(1) private(4) enterprise(1) fortinet(12356) fnFortiGateMib(101) fgHighAvailability(13) fgHaTables(2) fgHaStatsTable(1) fgHaStatsEntry(1) fgHaStatsNetUsage(5)}
      #
      $oid = "1.3.6.1.4.1.12356.101.13.2.1.1.5.1";
      $cmd = "$snmpget -v 1 -c $community $fortigate_hosts{$key}{hostname} $oid";	#define command to be run
      print "   running command to get fortigate bandwidth utilization: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           	#open filehandle using command output
      while (<IN>) {                                                   	 	#read a line from the command output
         s/"//g;								#get rid of " character to simplify regex
         if ( /Gauge32: ([0-9]+)/ ) {  						#look for a response to the snmp query
            $fortigate_hosts{$key}{bandwidth_kbps} = $1;			#value for current bandwidth in kbps
            $fortigate_hosts{$key}{bandwidth_mbps} = $fortigate_hosts{$key}{bandwidth_kbps}/1024; #convert kbps to mbps
            $fortigate_hosts{$key}{bandwidth_mbps} = sprintf("%.1f",$fortigate_hosts{$key}{bandwidth_mbps}); #truncate to 1 decimal place
         }                                                             		#end of if block
      }                                                                		#end of while loop
      close IN;                                                         	#close filehandle
      print "   host:$fortigate_hosts{$key}{hostname} cpu_util:$fortigate_hosts{$key}{cpu_util}\% ram_util:$fortigate_hosts{$key}{ram_util}\% bandwith_util:$fortigate_hosts{$key}{bandwidth_mbps}Mbps \n" if ($verbose eq "yes");
   } 										#end of foreach loop
} 										#end of subroutine




sub get_hpilo4_status {
   #
   print "running get_hpilo4_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the Hewlett Packard ILO4 service processor hosts to get the health status  by SNMP 
   #
   $community = $community_hpilo4;                           			#set the SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   foreach $key (sort keys %hpilo4_hosts) {
      #
      #
      # FANS
      # ----
      # .1.3.6.1.4.1.232.6.2.6.7.1.2.0 (Fan Index)
      # .1.3.6.1.4.1.232.6.2.6.7.1.3.0 (Fan Locale    (1=other, 2=unknown, 3=system, 4=systemBoard, 5=ioBoard, 6=cpu, 7=memory, 8=storage, 9=removable media, 
      #                                               10=power supply, 11=ambent, 12=chassis, 13=bridge card, 14=management board, 15=backplane, 16=network slot, 17=blade slot, 18=virtual)
      # .1.3.6.1.4.1.232.6.2.6.7.1.4.0 (Fan Present   (1=other, 2=absent,     3=present)
      # .1.3.6.1.4.1.232.6.2.6.7.1.5.0 (Fan Present   (1=other, 2=tachOutput, 3=spinDetect)
      # .1.3.6.1.4.1.232.6.2.6.7.1.6.0 (Fan Speed     (1=other, 2=normal,     3=high)
      # .1.3.6.1.4.1.232.6.2.6.7.1.9.0 (Fan Condition (1=other, 2=ok,         3=degraded, 4=failed)
      #
      # 
      # TEMPERATURE
      # -----------
      #  .1.3.6.1.4.1.232.6.2.6.8.1.2.0 (Temperature Sensor Index)
      #  .1.3.6.1.4.1.232.6.2.6.8.1.3.0 (Temperature Sensor Locale (1=other, 2=unknown, 3=system, 4=systemBoard, 5=ioBoard, 6=cpu, 7=memory, 8=storage, 9=removable media, 10=power supply, 11=ambent, 12=chassis, 13=bridge card)
      #  .1.3.6.1.4.1.232.6.2.6.8.1.7.0 (Threshold Type (1=other, 5=blowout, 9=caution, 15=critical, 16=noreaction)
      #  .1.3.6.1.4.1.232.6.2.6.8.1.4.0 (Temperature Celsius)
      #  .1.3.6.1.4.1.232.6.2.6.8.1.5.0 (TemperatureThreshold)
      #  .1.3.6.1.4.1.232.6.2.6.8.1.6.0 (TemperatureCondition)
      #
      #
      # CPU
      # ---
      #  .1.3.6.1.4.1.232.1.2.2.1.1.1  (CPU Index)
      #  .1.3.6.1.4.1.232.1.2.2.1.1.3  (CPU Name)
      #  .1.3.6.1.4.1.232.1.2.2.1.1.4  (CPU Speed in MHz)
      #  .1.3.6.1.4.1.232.1.2.2.1.1.5  (CPU Step)
      #  .1.3.6.1.4.1.232.1.2.2.1.1.6  (CPU status (1=unknown, 2=ok, 3=degraded, 4=failed, 5=disabled)
      #  .1.3.6.1.4.1.232.1.2.2.1.1.15 (Number of enabled CPU cores)
      #  .1.3.6.1.4.1.232.1.2.2.1.1.25 (Number of available CPU threads)
      #  .1.3.6.1.4.1.232.1.2.2.1.1.26 (CPU power status (1=unknown, 2=Low Powered, 3=Normal Powered, 4=High Powered)
      #
      #
      # Logical Drives
      # --------------
      #  .1.3.6.1.4.1.232.3.2.3.1.1.2.0 (Logical Drive Index)
      #  .1.3.6.1.4.1.232.3.2.3.1.1.1.0 (Logical Drive Controller)
      #  .1.3.6.1.4.1.232.3.2.3.1.1.3.0 (Logical Drive Fault Tolerance (1=other, 2=none, 3=RAID 1/RAID 1+0 (Mirroring), 4=RAID 4 (Data Guard), 5=RAID 5 (Distributed Data Guard), 
      #                                                                 7=RAID 6 (Advanced Data Guarding), 8=RAID 50, 9=RAID 60, 10=RAID 1 ADM (Advanced Data Mirroring), 11=RAID 10 ADM (Advanced Data Mirroring with Striping))
      #  .1.3.6.1.4.1.232.3.2.3.1.1.9.0 (Logical Drive Size in Mb)
      #  .1.3.6.1.4.1.232.3.2.3.1.1.4.0 (Logical Drive Status (1=other, 2=ok, 3=Failed, 4=Unconfigured, 5=Recovering, 6=Ready Rebuild, 7=Rebuilding, 8=Wrong Drive, 9=Bad Connect, 
      #                                                      10=Overheating, 11=Shutdown, 12=Expanding, 13=Not Available, 14=Queued For Expansion, 15=Multi-path Access Degraded, 
      #                                                      16=Erasing, 17=Predictive Spare Rebuild Ready, 18=Rapid Parity Initialization In Progress, 19=Rapid Parity Initialization Pending, 
      #                                                      20=No Access – Encrypted with No Controller Key, 21=Unencrypted to Encrypted Transformation in Progress, 
      #                                                      22=New Logical Drive Key Rekey in Progress, 23=No Access – Encrypted with Controller Encryption Not Enabled, 
      #                                                      24=Unencrypted To Encrypted Transformation Not Started, 25=New Logical Drive Key Rekey Request Received)
      #  .1.3.6.1.4.1.232.3.2.3.1.1.11.0 (Logical Drive Condition (1=other, 2=ok, 3=degraded, 4=failed)
      #
      #
      #
      # Physical Drives
      # ---------------
      #  .1.3.6.1.4.1.232.3.2.5.1.1.2.0 (Drive Index)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.5.0 (Drive Bay)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.64.0 (Drive Location)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.3.0 (Drive Vendor)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.51.0 (Drive Serial Number)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.45.0 (Drive Size in Mb)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.65.0 (Drive Link Rate (1=other, 2=1.5Gbps, 3=3.0Gbps, 4=6.0Gbps, 5=12.0Gbps))
      #  .1.3.6.1.4.1.232.3.2.5.1.1.70.0 (Drive Current Temperature)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.71.0 (Drive Temperature Threshold)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.72.0 (Drive Maximum Temperature)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.6.0 (Drive Status (1=Other, 2=Ok, 3=Failed, 4=Predictive Failure, 5=Erasing, 6=Erase Done, 7=Erase Queued, 8=SSD Wear Out, 9=Not Authenticated)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.37.0 (Drive Condition (1=other, 2=ok, 3=degraded, 4=failed)
      #  .1.3.6.1.4.1.232.3.2.5.1.1.9.0 (Drive Reference Time in hours)
      #
      #
      # iLO NIC
      # ---------
      # .1.3.6.1.4.1.232.9.2.5.2.1.1 (iLO location)
      # .1.3.6.1.4.1.232.9.2.5.1.1.2 (iLO NIC model)
      # .1.3.6.1.4.1.232.9.2.5.1.1.4 (iLO NIC MAC)
      # .1.3.6.1.4.1.232.9.2.5.1.1.5 (iLO NIC IPv4)
      # .1.3.6.1.4.1.232.9.2.5.1.1.9 (iLO NIC speed)
      # .1.3.6.1.4.1.232.9.2.5.1.1.14 (iLO NIC FQDN)
      # .1.3.6.1.4.1.232.9.2.5.2.1.2 (Tx bytes)
      # .1.3.6.1.4.1.232.9.2.5.2.1.3 (Tx packets)
      # .1.3.6.1.4.1.232.9.2.5.2.1.6 (Tx discard packets)
      # .1.3.6.1.4.1.232.9.2.5.2.1.7 (Tx error packets)
      # .1.3.6.1.4.1.232.9.2.5.2.1.9 (Rx bytes)
      # .1.3.6.1.4.1.232.9.2.5.2.1.10 (Rx packets)
      # .1.3.6.1.4.1.232.9.2.5.2.1.13 (Rx discard packets)
      # .1.3.6.1.4.1.232.9.2.5.2.1.14 (Rx error packets)
      # .1.3.6.1.4.1.232.9.2.5.2.1.15 (Rx unknown packets)
      #
      # Memory
      # ------
      # .1.3.6.1.4.1.232.6.2.14.13.1.1 (Memory Index)
      # .1.3.6.1.4.1.232.6.2.14.13.1.13 (Location)
      # .1.3.6.1.4.1.232.6.2.14.13.1.9 (Manufacturer)
      # .1.3.6.1.4.1.232.6.2.14.13.1.10 (Part Number)
      # .1.3.6.1.4.1.232.6.2.14.13.1.6 (Size in Kbytes)
      # .1.3.6.1.4.1.232.6.2.14.13.1.8 (Memory Technology)
      # .1.3.6.1.4.1.232.6.2.14.13.1.7 (Memory Type)
      # .1.3.6.1.4.1.232.6.2.14.13.1.19 (Memory status (1=other, 2=notPresent, 3=present, 4=good, 5=add, 6=upgrade, 7=missing, 8=doesNotMatch, 9=notSupported, 10=badConfig, 11=degraded, 12=spare, 13=partial)
      # .1.3.6.1.4.1.232.6.2.14.13.1.20 (Memory condition (1=other, 2=ok, 3=degraded, 4=degradedModuleIndexUnknown) 
      #
      # POWER SUPPLY STATUS
      # -------------------
      # 1.3.6.1.4.1.232.6.2.9.1.0 	cpqHeFltTolPwrSupplyCondition 	This value specifies the overall condition of the fault tolerant  power supply sub-system.  (1=other, 2=ok, 3=degraded, 4=failed)
      #
      # Command output will look similar to the following:
      #    $ /usr/bin/snmpwalk  -v 1 -c public ilo .1.3.6.1.4.1.232.6.2.14.13.1.20    #OID for memory condition, shows health status of each DIMM (1=other, 2=ok, 3=degraded, 4=degradedModuleIndexUnknown)
      #    SNMPv2-SMI::enterprises.232.6.2.14.13.1.20.0 = INTEGER: 2                  (Memory condition (1=other, 2=ok, 3=degraded, 4=degradedModuleIndexUnknown)
      #    SNMPv2-SMI::enterprises.232.6.2.14.13.1.20.1 = INTEGER: 2                  (Memory condition (1=other, 2=ok, 3=degraded, 4=degradedModuleIndexUnknown)
      #    SNMPv2-SMI::enterprises.232.6.2.14.13.1.20.2 = INTEGER: 2                  (Memory condition (1=other, 2=ok, 3=degraded, 4=degradedModuleIndexUnknown)
      #    SNMPv2-SMI::enterprises.232.6.2.14.13.1.20.3 = INTEGER: 2                  (Memory condition (1=other, 2=ok, 3=degraded, 4=degradedModuleIndexUnknown)
      #
      #
      #    $ /usr/bin/snmpwalk  -v 1 -c public ilo .1.3.6.1.4.1.232.3.2.5.1.1.37.0   #OID for Physical Drive Condition (1=other, 2=ok, 3=degraded, 4=failed)
      #    SNMPv2-SMI::enterprises.232.3.2.5.1.1.37.0.0 = INTEGER: 2                 <--- this server has two physical disks
      #    SNMPv2-SMI::enterprises.232.3.2.5.1.1.37.0.1 = INTEGER: 2                 <--- this server has two physical disks
      #
      #
      #    $ /usr/bin/snmpwalk  -v 1 -c public ilo .1.3.6.1.4.1.232.3.2.3.1.1.4.0    #OID for Logical Drive Status (1=other, 2=ok, 3=Failed, 4=Unconfigured, 5=Recovering, 6=Ready Rebuild, 7=Rebuilding, 8=Wrong Drive, 9=Bad Connect, 
      #    SNMPv2-SMI::enterprises.232.3.2.3.1.1.4.0.1 = INTEGER: 2                 <--- this server has a single logical drive (probably a RAID-1 mirror of 2 physical disks)
      #
      #    $ /usr/bin/snmpwalk  -v 1 -c public ilo 1.3.6.1.4.1.232.6.2.6.7.1.9.0     #OID for Fan Condition (1=other, 2=ok, 3=degraded, 4=failed)
      #    SNMPv2-SMI::enterprises.232.6.2.6.7.1.9.0.1 = INTEGER: 2                  <--- this server has 7 fans
      #    SNMPv2-SMI::enterprises.232.6.2.6.7.1.9.0.2 = INTEGER: 2
      #    SNMPv2-SMI::enterprises.232.6.2.6.7.1.9.0.3 = INTEGER: 2
      #    SNMPv2-SMI::enterprises.232.6.2.6.7.1.9.0.4 = INTEGER: 2
      #    SNMPv2-SMI::enterprises.232.6.2.6.7.1.9.0.5 = INTEGER: 2
      #    SNMPv2-SMI::enterprises.232.6.2.6.7.1.9.0.6 = INTEGER: 2
      #    SNMPv2-SMI::enterprises.232.6.2.6.7.1.9.0.7 = INTEGER: 2
      #
      #    $ /usr/bin/snmpget  -v 1 -c public ilo  1.3.6.1.4.1.232.6.2.9.1.0 	    #OID for cpqHeFltTolPwrSupplyCondition overall condition of the fault tolerant  power supply sub-system.  (1=other, 2=ok, 3=degraded, 4=failed)
      #    SNMPv2-SMI::enterprises.232.6.2.9.1.0 = INTEGER: 2                       <--- there are multiple power supplies, but this single value shows overall power supply redundancy status
      #
      #
      # Check the HP ILO4  SNMP OID for power supply redundancy
      #
      $hpilo4_hosts{$key}{snmp}                          = "unknown";				#initialize hash element
      $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} = "unknown";				#initialize hash element
      next unless ( $hpilo4_hosts{$key}{ping} eq "up" );					#skip hosts that do not respond to ping
      $oid = ".1.3.6.1.4.1.232.6.2.9.1.0";							#SNMP OID for cpqHeFltTolPwrSupplyCondition
      $cmd = "$snmpwalk -v 1 -c $community $hpilo4_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get hpilo4 power supply redundancy: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) { 
            $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} = $1;				#capture status of power supply redundancy
            $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} = "other"    if ( $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} eq "1" );  #convert from integer to humand readable value
            $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} = "ok"       if ( $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} eq "2" );  #convert from integer to humand readable value
            $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} = "degraded" if ( $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} eq "3" );  #convert from integer to humand readable value
            $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} = "failed"   if ( $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} eq "4" );  #convert from integer to humand readable value
            $hpilo4_hosts{$key}{snmp}                          = "ok";      								       #finding a value here means we have working SNMP
         }											#end of if block
      }												#end of while loop
      close IN;                                                         			#close filehandle
      print "   host:$hpilo4_hosts{$key}{hostname}  powersupply_redundancy:$hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} \n" if ($verbose eq "yes");
      #
      # Check the HP ILO4  SNMP OID for fan status
      #
      $hpilo4_hosts{$key}{fans}{count} = 0;							#initialize hash element
      $hpilo4_hosts{$key}{fans}{ok}    = 0;							#initialize hash element
      $oid = ".1.3.6.1.4.1.232.6.2.6.7.1.9.0";							#SNMP OID for all fans
      $cmd = "$snmpwalk -v 1 -c $community $hpilo4_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get hpilo4 fans: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) { $hpilo4_hosts{$key}{fans}{count}++; }			#increment counter variable for the status of all fans
         if ( / = INTEGER: 2/        ) { $hpilo4_hosts{$key}{fans}{ok}++;    }			#increment counter variable for the number of fans in "ok" status
      } 											#end of while loop
      close IN;                                                         			#close filehandle
      $hpilo4_hosts{$key}{fans}{not_ok} = $hpilo4_hosts{$key}{fans}{count} - $hpilo4_hosts{$key}{fans}{ok};
      print "   host:$hpilo4_hosts{$key}{hostname} fan_count:$hpilo4_hosts{$key}{fans}{count} fan_ok:$hpilo4_hosts{$key}{fans}{ok} fan_not_ok:$hpilo4_hosts{$key}{fans}{not_ok} \n" if ($verbose eq "yes");
      #
      # Check the HP ILO4  SNMP OID for Physical Disk Drive status
      #
      $hpilo4_hosts{$key}{physical_disks}{count} = 0;						#initialize hash element
      $hpilo4_hosts{$key}{physical_disks}{ok}    = 0;						#initialize hash element
      $oid = ".1.3.6.1.4.1.232.3.2.5.1.1.37.0";							#SNMP OID for all physical disk drives
      $cmd = "$snmpwalk -v 1 -c $community $hpilo4_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get hpilo4 physical disk drives: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) { $hpilo4_hosts{$key}{physical_disks}{count}++; }	#increment counter variable for the status of all physical disks
         if ( / = INTEGER: 2/        ) { $hpilo4_hosts{$key}{physical_disks}{ok}++; }		#increment counter variable for the number of physical disks in "ok" status
      } 											#end of while loop
      close IN;                                                       	  			#close filehandle
      $hpilo4_hosts{$key}{physical_disks}{not_ok} = $hpilo4_hosts{$key}{physical_disks}{count} - $hpilo4_hosts{$key}{physical_disks}{ok};
      print "   host:$hpilo4_hosts{$key}{hostname} physical_disks_count:$hpilo4_hosts{$key}{physical_disks}{count} physical_disks_ok:$hpilo4_hosts{$key}{physical_disks}{ok} physical_disks_not_ok:$hpilo4_hosts{$key}{physical_disks}{not_ok} \n" if ($verbose eq "yes");
      #
      # Check the HP ILO4  SNMP OID for Logical Disk Drive status
      #
      $hpilo4_hosts{$key}{logical_disks}{count} = 0;						#initialize hash element
      $hpilo4_hosts{$key}{logical_disks}{ok}    = 0;						#initialize hash element
      $oid = ".1.3.6.1.4.1.232.3.2.3.1.1.4.0";							#SNMP OID for all logical disk drives
      $cmd = "$snmpwalk -v 1 -c $community $hpilo4_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get hpilo4 logical disk drives: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) { $hpilo4_hosts{$key}{logical_disks}{count}++; }		#increment counter variable for the status of all physical disks
         if ( / = INTEGER: 2/        ) { $hpilo4_hosts{$key}{logical_disks}{ok}++; }		#increment counter variable for the number of physical disks in "ok" status
      } 											#end of while loop
      close IN;                                                       	  			#close filehandle
      $hpilo4_hosts{$key}{logical_disks}{not_ok} = $hpilo4_hosts{$key}{logical_disks}{count} - $hpilo4_hosts{$key}{logical_disks}{ok};
      print "   host:$hpilo4_hosts{$key}{hostname} logical_disks_count:$hpilo4_hosts{$key}{logical_disks}{count} logical_disks_ok:$hpilo4_hosts{$key}{logical_disks}{ok} logical_disks_not_ok:$hpilo4_hosts{$key}{logical_disks}{not_ok} \n" if ($verbose eq "yes");

      #
      # Check the HP SmartArray RAID controller status 
      #
      # HINT: There will usually be only one RAID controller (or none at all if machine boots from SAM).  In rare cases, there may be multiple RAID controllers.
      # Sample output:
      # $ snmpwalk -v 1 -c public ilo.example.com.1.3.6.1.4.1.232.3.2.2.1.1.12
      # SNMPv2-SMI::enterprises.232.3.2.2.1.1.12.0 = INTEGER: 2   <-- status of first  RAID controller 1=other 2=ok 3=degraed 4=failed
      # SNMPv2-SMI::enterprises.232.3.2.2.1.1.12.1 = INTEGER: 3   <-- status of second RAID controller 1=other 2=ok 3=degraed 4=failed
      # SNMPv2-SMI::enterprises.232.3.2.2.1.1.12.2 = INTEGER: 4   <-- status of third  RAID controller 1=other 2=ok 3=degraed 4=failed
      #  
      # Sample output with -Onq switch.  We use this switch to make snmpwalk on Linux have output simimlar to snmpinfo on AIX.
      # $ snmpwalk -Onq -v 1 -c public ilo.example.com.1.3.6.1.4.1.232.3.2.2.1.1.12
      # .1.3.6.1.4.1.232.3.2.2.1.1.12.0 2 <-- status of first  RAID controller 1=other 2=ok 3=degraed 4=failed
      # .1.3.6.1.4.1.232.3.2.2.1.1.12.1 3 <-- status of second RAID controller 1=other 2=ok 3=degraed 4=failed
      # .1.3.6.1.4.1.232.3.2.2.1.1.12.2 4 <-- status of third  RAID controller 1=other 2=ok 3=degraed 4=failed
      #
      $hpilo4_hosts{$key}{raid_controller}{count}   = 0;  #counter for number of installed RAID controllers
      $hpilo4_hosts{$key}{raid_controller}{ok}      = 0;  
      $hpilo4_hosts{$key}{raid_controller}{not_ok}  = 0;  
      #
      #
      #
      # Check status of RAID controller and an associated array accelerators / write cache modules
      #
      # /iso/iso-identified-organization/dod/internet/private/enterprises/hp/cpqDriveArray/cpqDaComponent/cpqDaCntlr/cpqDaCntlrTable/cpqDaCntlrEntry/cpqDaCntlrBoardCondition 
      $oid = "1.3.6.1.4.1.232.3.2.2.1.1.12";
      $cmd = "$snmpwalk -Onq -v 1 -c $community $hpilo4_hosts{$key}{hostname} $oid";
      print "   running command to check status of of HPE SmartArray RAID controller: $cmd \n" if ($verbose eq "yes");
      open (IN,"$cmd |");						#open filehandle
      while (<IN>) {						#read a line from the filehandle
         s/\"//g;							#get rid of any quotation marks in the output
         s/=//g;							#get rid of any equal sign in the output
         if ( /[0-9\.]+ +([0-9]+)/) {				#parse out the line of output into OID and value
            $hpilo4_hosts{$key}{raid_controller}{count}++;   			#increment counter for number of installed RAID controllers
            $hpilo4_hosts{$key}{raid_controller}{ok}++     if ($1 == 2);   	#increment counter for number of RAID controllers with OK status
            $hpilo4_hosts{$key}{raid_controller}{not_ok}++ if ($1 != 2);   	#increment counter for number of RAID controllers with anything other than OK status
         }
      }								#end of while loop
      close IN;							#close filehandle
      print "   raid_controller_count:$hpilo4_hosts{$key}{raid_controller}{count} raid_controller_ok:$hpilo4_hosts{$key}{raid_controller}{ok} raid_controller_not_ok:$hpilo4_hosts{$key}{raid_controller}{not_ok}";
      #
      # Check the HP ILO4  SNMP OID for physical Processor status
      #
      $hpilo4_hosts{$key}{processor_status}{count} = 0;						#initialize hash element
      $hpilo4_hosts{$key}{processor_status}{ok}    = 0;						#initialize hash element
      $oid = ".1.3.6.1.4.1.232.1.2.2.1.1.6";							#SNMP OID for all physical processor condition / status / health
      $cmd = "$snmpwalk -v 1 -c $community $hpilo4_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get hpilo4 processor status: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) { $hpilo4_hosts{$key}{processor_status}{count}++; }		#increment counter variable for the status of all physical disks
         if ( / = INTEGER: 2/        ) { $hpilo4_hosts{$key}{processor_status}{ok}++; }		#increment counter variable for the number of physical disks in "ok" status
      } 											#end of while loop
      close IN;                                                       	  			#close filehandle
      $hpilo4_hosts{$key}{processor_status}{not_ok} = $hpilo4_hosts{$key}{processor_status}{count} - $hpilo4_hosts{$key}{processor_status}{ok};
      print "   host:$hpilo4_hosts{$key}{hostname} processor_count:$hpilo4_hosts{$key}{processor_status}{count} processor_ok:$hpilo4_hosts{$key}{processor_status}{ok} processor_not_ok:$hpilo4_hosts{$key}{processor_status}{not_ok} \n" if ($verbose eq "yes");
      #
      # Check the HP ILO4  SNMP OID for physical memory DIMM status
      #
      $hpilo4_hosts{$key}{memory_module_status}{count} = 0;					#initialize hash element
      $hpilo4_hosts{$key}{memory_module_status}{ok}    = 0;					#initialize hash element
      $oid = ".1.3.6.1.4.1.232.6.2.14.13.1.20";							#SNMP OID for all physical memory module condition / status / health
      $cmd = "$snmpwalk -v 1 -c $community $hpilo4_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get hpilo4 memory module status: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) { $hpilo4_hosts{$key}{memory_module_status}{count}++; }	#increment counter variable for the status of all physical disks
         if ( / = INTEGER: 2/        ) { $hpilo4_hosts{$key}{memory_module_status}{ok}++; }	#increment counter variable for the number of physical disks in "ok" status
      } 											#end of while loop
      close IN;                                                       	  			#close filehandle
      $hpilo4_hosts{$key}{memory_module_status}{not_ok} = $hpilo4_hosts{$key}{memory_module_status}{count} - $hpilo4_hosts{$key}{memory_module_status}{ok};
      print "   host:$hpilo4_hosts{$key}{hostname} memory_module_count:$hpilo4_hosts{$key}{memory_module_status}{count} memory_module_ok:$hpilo4_hosts{$key}{memory_module_status}{ok} memory_module_not_ok:$hpilo4_hosts{$key}{memory_module_status}{not_ok} \n" if ($verbose eq "yes");
      #
      # Check the HP ILO4  SNMP OID for ambient temperature at air inlet vent
      #
      $hpilo4_hosts{$key}{ChassisInletTemperatureC} = 9999;					#initialize hash element with dummy numeric value so we can do math against it
      $oid = "1.3.6.1.4.1.232.6.2.6.8.1.4.0.1";							#SNMP OID for all physical memory module condition / status / health
      $cmd = "$snmpget -v 1 -c $community $hpilo4_hosts{$key}{hostname} $oid";			#define command to be run
      print "   running command to get hpilo4 ambient temperature: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1 |");                                           			#open filehandle using command output
      while (<IN>) {                                                   	 			#read a line from the command output
         if ( / = INTEGER: ([0-9]+)/ ) { 
            $hpilo4_hosts{$key}{ChassisInletTemperatureC} = $1;  				#save value to hash
         }											#end of if block
      } 											#end of while loop
      close IN;                                                       	  			#close filehandle
      print "   host:$hpilo4_hosts{$key}{hostname} Ambient_Temperature:$hpilo4_hosts{$key}{ChassisInletTemperatureC}C  \n" if ($verbose eq "yes");
   } 												#end of foreach loop
} 												#end of subroutine




sub get_linux_status {
   #
   print "running get_linux_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the Linux hosts to get NTP time sync status  via SSH
   # This assues there is already a nagios monitoring system in place with preshared ssh keys
   #
   foreach $key (sort keys %linux_hosts) {
      #
      # confirm SSH key pair authentication is working
      #
      $linux_hosts{$key}{ssh} = "unknown";                                                     	#initialize hash element to avoid undef errors
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $linux_hosts{$key}{hostname} hostname";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         if ( /[a-zA-Z0-9]+/ ) {                                               			#find output of the "hostname" command
            $linux_hosts{$key}{ssh} = "OK";                                                     #set the hash element to be used later as a boolean
         } else {                                                                               #end of if block
            s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
            $linux_hosts{$key}{ssh} = "unknown";                                                #if SSH is not OK, set hash element 
         }                                                                                      #end of if/else block
      }                                                                                         #end of while loop
      print "   SSH:$linux_hosts{$key}{ssh} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
      next unless ( $linux_hosts{$key}{ssh} eq "OK" );						#break out of subroutine if SSH is not working
      #
      # get NTP status utilization
      #
      $linux_hosts{$key}{ntp} = "unknown";                                                     	#initialize hash element to avoid undef errors
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $linux_hosts{$key}{hostname} /usr/local/nagios/libexec/check_unix_time_sync";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         if ( /^time sync OK/ ) {                                                               #find output of nagios check
            $linux_hosts{$key}{ntp} = "OK";                                                     #shorten the status to just "OK"
         } else {                                                                               #end of if block
            s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
            $linux_hosts{$key}{ntp} = $_;                                                       #if NTP is not OK, include details of the problem
         }                                                                                      #end of if/else block
      }                                                                                         #end of while loop
      print "   NTP:$linux_hosts{$key}{ntp} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
      #
      # check UNIX password age for root user
      #
      $linux_hosts{$key}{root_password_age_days} = 99999;               			#initialize hash element to avoid undef errors
      $linux_hosts{$key}{root_password_age}      = "UNKNOWN";               			#initialize hash element to avoid undef errors
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $linux_hosts{$key}{hostname} /usr/local/nagios/libexec/check_unix_password_age --maxage=180 --user=root";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
         if ( /user:root age:([0-9]+) minage:[0-9]+ maxage:([0-9]+) days_left:([0-9\-]+)/ ) {   #parse the output of the nagios check for the root user
            $linux_hosts{$key}{root_password_age_days}      = $1;                               #parse out the password age in days
            $linux_hosts{$key}{root_password_maxage_days}   = $2;                               #parse out the password age in days
            $linux_hosts{$key}{root_password_age_days_left} = $3;                               #parse out the password age in days remaining before expiry
            #xxxx
         }
         if ( /^password age OK/ ) {                                                            #find output of nagios check
            $linux_hosts{$key}{root_password_age} = "OK";                                       #shorten output to "OK"
         } else {                                                                               #end of if block
            $linux_hosts{$key}{root_password_age} = $_;                                         #if not OK, include details of the problem
         }                                                                                      #end of if/else block
         #
         if ( $linux_hosts{$key}{root_password_maxage_days} - $linux_hosts{$key}{root_password_age_days} > 14 ) {
            $linux_hosts{$key}{root_password_age} = "OK";                                       #shorten output to "OK"
         }
      }                                                                                         #end of while loop
      print "   password_age:$linux_hosts{$key}{root_password_age} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
      #
      # check UNIX password age for all other users.  This tells us if *any* user account is expired.
      # Unlike the previous section, this just gives an "OK" rather than the number of days.
      #
      $linux_hosts{$key}{unix_password_age} = "UNKNOWN";               				#initialize hash element to avoid undef errors
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $linux_hosts{$key}{hostname} /usr/local/nagios/libexec/check_unix_password_age --maxage=180";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
         if ( /^password age OK/ ) {                                                            #find output of nagios check
            $linux_hosts{$key}{unix_password_age} = "OK";                                       #shorten the status to just "OK"
         } elsif ( /^password age WARN/ ) {                                                     #find output of nagios check
            $linux_hosts{$key}{unix_password_age} = $_;   	                                #if not OK, include details of the problem
         } elsif ( /^password age CRITICAL/ ) {                                                 #find output of nagios check
            $linux_hosts{$key}{unix_password_age} = $_;   	                                #if not OK, include details of the problem
         } else {                                                 				#find output of nagios check
            $linux_hosts{$key}{unix_password_age} = $_;   	                                #if not OK, include details of the problem
         }                                                                                      #end of if/else block
      }                                                                                         #end of while loop
      print "   password_age:$linux_hosts{$key}{unix_password_age} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
      #
      # check state of linux daemons
      #
      $linux_hosts{$key}{daemons} = "unknown";  		             			#initialize hash element to avoid undef errors
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $linux_hosts{$key}{hostname} /usr/local/nagios/libexec/check_linux_daemons";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
         if ( /^linux daemons OK/ ) {                                                           #find output of nagios check
            $linux_hosts{$key}{daemons} = "OK";                		                       	#shorten the status to just "OK"
         } else {                                                                               #end of if block
            $linux_hosts{$key}{daemons} = $_;                          		               	#if paging is not OK, include details of the problem
         }                                                                                      #end of if/else block
      }                                                                                         #end of while loop
      print "   daemons:$linux_hosts{$key}{daemons} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
      #
      # check state of Oracle databases
      #
      $linux_hosts{$key}{oracle_databases} = "unknown";  		             			#initialize hash element to avoid undef errors
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $linux_hosts{$key}{hostname} /usr/local/nagios/libexec/check_oracle_instances";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
         if ( /^oracle instances OK/ ) {                                                        #find output of nagios check
            $linux_hosts{$key}{oracle_databases} = "OK";      		                       	#shorten the status to just "OK"
         } else {                                                                               #end of if block
            $linux_hosts{$key}{oracle_databases} = $_;                          		               	#if paging is not OK, include details of the problem
         }                                                                                      #end of if/else block
      }                                                                                         #end of while loop
      print "   daemons:$linux_hosts{$key}{oracle_databases} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
   }                                                                                            #end of foreach loop
}                                                                                               #end of subroutine



sub get_aix_status {
   #
   print "running get_aix_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the AIX hosts to get CPU utilization via SSH
   # This assues there is already a nagios monitoring system in place with preshared ssh keys
   #
   foreach $key (sort keys %aix_hosts) {
      #
      # get CPU utilization
      #
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $aix_hosts{$key}{hostname} /usr/local/nagios/libexec/check_aix_cpu";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         if ( /^AIX_CPU OK/ ) {                                                                 #find output of nagios check
            $aix_hosts{$key}{cpu} = "OK";                                                       #shorten the status to just "OK"
         } else {                                                                               #end of if block
            s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
            $aix_hosts{$key}{cpu} = $_;                                                         #if CPU is not OK, include details of the problem
         }                                                                                      #end of if/else block
      }                                                                                         #end of while loop
      print "   CPU:$aix_hosts{$key}{cpu} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
      #
      # get paging space utilization
      #
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $aix_hosts{$key}{hostname} /usr/local/nagios/libexec/check_aix_paging";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         if ( /^AIX paging OK/ ) {                                                              #find output of nagios check
            $aix_hosts{$key}{paging} = "OK";                                                    #shorten the status to just "OK"
         } else {                                                                               #end of if block
            s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
            $aix_hosts{$key}{paging} = $_;                                                      #if paging is not OK, include details of the problem
         }                                                                                      #end of if/else block
      }                                                                                         #end of while loop
      print "   paging:$aix_hosts{$key}{paging} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
      #
      # get error report status
      #
      $cmd = "$ssh -o PreferredAuthentications=publickey -o PubKeyAuthentication=yes $aix_hosts{$key}{hostname} /usr/local/nagios/libexec/check_aix_errpt";
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         if ( /^AIX errpt OK/ ) {                                                               #find output of nagios check
            $aix_hosts{$key}{errpt} = "OK";                                                     #shorten the status to just "OK"
         } else {                                                                               #end of if block
            s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
            $aix_hosts{$key}{errpt} = $_;                                                       #if paging is not OK, include details of the problem
         }                                                                                      #end of if/else block
      }                                                                                         #end of while loop
      print "   errpt:$aix_hosts{$key}{errpt} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
   }                                                                                            #end of foreach loop
}                                                                                               #end of subroutine




sub get_hmc_status {
   #
   print "running get_hmc_status subroutine \n" if ($verbose eq "yes");
   #
   # query all the IBM Hardware Management Consoles SSH to get the health status of managed IBM POWER systems
   # HINT: this subroutine just execute an existing nagios check that is assumed to already exist.
   #       In other words, it is assumed the local machine is already monitoring HMC devices via nagios, and this check just grabs the current status from that nagios check.
   #
   foreach $key (sort keys %hmc_hosts) {
      #
      my $nagios_tempfile = "/tmp/nagios.check_hmc.$hmc_hosts{$key}{hostname}.tmp";     #location of temporary file used by nagios check
      #
      # The temporary file created by the nagios check will have content similar to the following:
      # $ cat /tmp/nagios.check_hmc.hmc01.example.com.tm
      # HMC checks OK - all 2 managed systems are running normally.  9009-22A*7803XXX  9009-22A*7803YYY  |
      #
      #
      #
      # run this section if the nagios temporary file cannot be found, which would indicate a problem with nagios
      #
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 5 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 4 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 3 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 2 minutes to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         print "   $nagios_tempfile file not found, waiting for 1 minute  to see if it appears... \n" if ($verbose eq "yes");
         sleep 60;
      }
      if ( ! -e "$nagios_tempfile" ) {
         $hmc_hosts{$key}{health} = "UNKNOWN, cannot find nagios check output in file: $nagios_tempfile";                       #save value to hash
         print "   hmc_health:$hmc_hosts{$key}{health} \n" if ($verbose eq "yes");
      }
      #
      # run this section if the nagios temporary file exists
      #
      if ( -e "$nagios_tempfile" ) {
         $hmc_hosts{$key}{health} = "UNKNOWN";                                                  #initialize hash element to avoid undef errors
         print "   reading file $nagios_tempfile \n" if ($verbose eq "yes");
         open(IN,"$nagios_tempfile") or warn "Cannot open /tmp/nagios.check_hmc.$hmc_hosts{$key}{hostname}.tmp file for reading $! \n";
         while (<IN>) {                                                                         #read a line from the command output
            if ( /^HMC checks OK/ ) {                                                           #find output of nagios check
               $hmc_hosts{$key}{health} = "OK";                                                 #shorten the status to just "OK"
            } 
            if ( /^HMC checks WARN/ ) {                                                         #find output of nagios check
               $hmc_hosts{$key}{health} = "WARN";                                               #shorten the status to just "OK"
            } 
            if ( /^HMC checks CRITICAL/ ) {                                                     #find output of nagios check
               $hmc_hosts{$key}{health} = "CRITICAL";                                           #shorten the status to just "OK"
            } 
            if ( /^HMC checks UNKNOWN/ ) {                                                      #find output of nagios check
               $hmc_hosts{$key}{health} = "UNKNOWN";                                            #shorten the status to just "OK"
            } 
         }                                                                                      #end of while loop
         print "   hmc_health:$hmc_hosts{$key}{health} \n" if ($verbose eq "yes");
         close IN;                                                                              #close filehandle
      }                                                                                         #end of if block
   }                                                                                            #end of foreach loop
}                                                                                               #end of subroutine





sub get_mikrotik_swos_status {
   #
   print "running get_mikrotik_swos_status subroutine \n" if ($verbose eq "yes");
   #
   $community = $community_mikrotik_swos;                                                       #set SNMP community string for this device type
   print "   setting SNMP community to $community \n" if ($verbose eq "yes");
   #
   # query all the MikroTik SwOS hosts to get system health via SNMP (by running an existing nagios check)
   # This assues there is already a nagios monitoring system in place with preshared ssh keys
   #
   foreach $key (sort keys %mikrotik_swos_hosts) {
      $mikrotik_swos_hosts{$key}{snmp} = "unknown";                                          	#initialize hash element
      #
      # get CPU utilization
      #
      $cmd = "/usr/local/nagios/libexec/check_mikrotik_swos -H $mikrotik_swos_hosts{$key}{hostname} -C public";  #just call the nagios check
      print "   running command: $cmd \n" if ($verbose eq "yes");
      open(IN,"$cmd 2>&1|");                                                                    #open filehandle from command output
      while (<IN>) {                                                                            #read a line from the command output
         if ( /^MikroTik SwOS OK/ ) {                                                           #find output of nagios check
            $mikrotik_swos_hosts{$key}{health} = "OK";                                          #shorten the status to just "OK"
            $mikrotik_swos_hosts{$key}{snmp}   = "ok";                                          #finding a value here means we have working SNMP
         } else {                                                                               #end of if block
            s/\|.*//g;										#get rid of nagios performance data after the | character, not relevant for this report
            $mikrotik_swos_hosts{$key}{health} = $_;                                            #if CPU is not OK, include details of the problem
            $mikrotik_swos_hosts{$key}{snmp}   = "ok";                                          #finding a value here means we have working SNMP
         }                                                                                      #end of if/else block
      }                                                                                         #end of while loop
      print "   health:$mikrotik_swos_hosts{$key}{cpu} \n" if ($verbose eq "yes");
      close IN;                                                                                 #close filehandle
   }                                                                                            #end of foreach loop
}                                                                                               #end of subroutine




sub generate_html_report_header {
   #
   print "running generate_html_report_header subroutine \n" if ($verbose eq "yes");
   #
   print "   opening $output_file for writing \n" if ($verbose eq "yes");
   open (OUT,">$output_file") or die "Cannot open $output_file for writing: $! \n";
   print OUT "<html><head><title>Status Report</title></head><body> \n";	
   print OUT "<br>This report is generated by the $0 script on $localhost \n";	
   print OUT "<br>Last updated $year-$mon-$mday $hour:$min \n";
   print OUT "<p>\&nbsp\;</p> \n";
}										#end of subroutine




sub generate_html_report_linux_hosts {
   #
   print "running generate_html_report_linux_hosts subroutine \n" if ($verbose eq "yes");
   #
   #
   return unless (@linux_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for Linux hosts
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=13> Linux Hosts \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SSH <td> NTP <td> root pw age <td>other pw <td> daemons <td>Oracle DB <td> SNMP <td> CPU util <td> RAM util<td> Paging Space util <td> Disk util \n";
   foreach $key (sort keys %linux_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$linux_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $linux_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $linux_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $linux_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $linux_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT "  <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SSH status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $linux_hosts{$key}{ssh} eq "OK" );
      $bgcolor = "red"   if ( $linux_hosts{$key}{ssh} ne "OK" );
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{ssh} \n";
      #
      # print NTP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $linux_hosts{$key}{ntp} eq "OK" );
      $bgcolor = "red"   if ( $linux_hosts{$key}{ntp} ne "OK" );
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{ntp} \n";
      #
      # print root password age in table row (OK=not expired)
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if ( $linux_hosts{$key}{root_password_age} eq "OK" );
      $bgcolor = "red"    if ( $linux_hosts{$key}{root_password_age} ne "OK" );
      $bgcolor = "orange" if ( ($linux_hosts{$key}{root_password_age_days} > 160) && ($linux_hosts{$key}{root_password_age_days} <= 180) );  #orange for warning when password age is getting close to 180
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{root_password_age_days} \n";  #note that we check root_password_age for "OK", then get number of days from root_password_age_days
      #
      # print all other accounts (non-root) password age in table row (OK=not expired)
      # 
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $linux_hosts{$key}{unix_password_age} =~ /OK/ );
      $bgcolor = "orange" if ( $linux_hosts{$key}{unix_password_age} =~ /WARN/ );
      $bgcolor = "red"    if ( $linux_hosts{$key}{unix_password_age} =~ /CRITICAL/ );
      $bgcolor = "red"    if ( $linux_hosts{$key}{unix_password_age} =~ /UNKNOWN/ );
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{unix_password_age} \n"; 
      #
      # print status of linux daemons in table row 
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $linux_hosts{$key}{daemons} eq "OK" );
      $bgcolor = "red"    if ( $linux_hosts{$key}{daemons} ne "OK" );
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{daemons} \n";  
      #
      # print status of oracle databases in table row 
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $linux_hosts{$key}{oracle_databases} eq "OK" );
      $bgcolor = "red"    if ( $linux_hosts{$key}{oracle_databases} ne "OK" );
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{oracle_databases} \n";  
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $linux_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $linux_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $linux_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print CPU status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $linux_hosts{$key}{cpu_load} <= 50);
      $bgcolor = "orange" if ( ($linux_hosts{$key}{cpu_load} > 50) && ($linux_hosts{$key}{cpu_load} <= 80) );
      $bgcolor = "red"    if (  $linux_hosts{$key}{cpu_load} > 80);
      print OUT "    <td bgcolor=$bgcolor> $linux_hosts{$key}{cpu_load}\% \n";
      #
      # print RAM status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $linux_hosts{$key}{ram}{hrStorageUsed_pct} <= 99.9);
      $bgcolor = "orange" if ( ($linux_hosts{$key}{ram}{hrStorageUsed_pct} > 99.9) && ($linux_hosts{$key}{ram}{hrStorageUsed_pct} <= 100) );
      $bgcolor = "red"    if (  $linux_hosts{$key}{ram}{hrStorageUsed_pct} > 101);
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{ram}{hrStorageUsed_pct}\% \n";
      #
      # print paging space utilization in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $linux_hosts{$key}{paging}{hrStorageUsed_pct} <= 50);
      $bgcolor = "orange" if ( ($linux_hosts{$key}{paging}{hrStorageUsed_pct} > 50) && ($linux_hosts{$key}{paging}{hrStorageUsed_pct} <= 75) );
      $bgcolor = "red"    if (  $linux_hosts{$key}{paging}{hrStorageUsed_pct} > 75);
      print OUT "    <td bgcolor=$bgcolor> $linux_hosts{$key}{paging}{hrStorageUsed_pct}\% \n";
      #
      # print Linux / root filesystem space utilization in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "    <td bgcolor=$bgcolor> \n" if ($linux_hosts{$key}{os} eq "Linux");	#start the HTML table data for Linux hosts
      for $mount_point (@mount_points) {						#loop through for each drive letter a..z  
         next unless ( defined($linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_pct}) );			#only run this section if the required hash element exists
         $fontcolor = "black";								#initialize variable
         $fontcolor = "green"  if (  $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_pct} <= 80 );
         $fontcolor = "orange" if ( ($linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_pct}  > 80 ) && ($linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_pct} <= 90) );
         $fontcolor = "red"    if (  $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_pct}  > 90 );
         print OUT "    <br><font color=$fontcolor> $linux_hosts{$key}{linux_fs}{$mount_point}{mount_point}    $linux_hosts{$key}{linux_fs}{$mount_point}{hrStorageUsed_pct}\% \n";
      } 										#end of if block
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine



sub generate_html_report_san_multipath_linux_hosts {
   #
   print "running generate_html_report_san_multipath_linux_hosts subroutine \n" if ($verbose eq "yes");
   #
   #
   return unless (@san_multipath_linux_hostnames);					#break out of subroutine if no hostnames are defined
   # Create the HTML table for bare-metal Linux hosts with iSCSI and/or Fibre Channel SAN paths
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=7> Bare-metal Linux Hosts with iSCSI and/or Fibre Channel SAN paths\n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> Multipath Health <td> active<td> passive <td> faulty <td> shaky\n";
   foreach $key (sort keys %san_multipath_linux_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$san_multipath_linux_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $san_multipath_linux_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $san_multipath_linux_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $san_multipath_linux_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $linux_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $san_multipath_linux_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print health status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $san_multipath_linux_hosts{$key}{health} eq "OK");
      $bgcolor = "red"    if (  $san_multipath_linux_hosts{$key}{health} ne "OK");
      print OUT "    <td bgcolor=$bgcolor> $san_multipath_linux_hosts{$key}{health} \n";
      #
      # print the number of active SAN paths in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "   <td bgcolor=$bgcolor> $san_multipath_linux_hosts{$key}{active} \n";
      #
      # print the number of passive SAN paths in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "   <td bgcolor=$bgcolor> $san_multipath_linux_hosts{$key}{passive} \n";
      #
      # print the number of faulty SAN paths in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $san_multipath_linux_hosts{$key}{faulty} == 0);
      $bgcolor = "red"    if (  $san_multipath_linux_hosts{$key}{faulty} >  0);
      print OUT "   <td bgcolor=$bgcolor> $san_multipath_linux_hosts{$key}{faulty} \n";
      #
      # print the number of shaky SAN paths in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $san_multipath_linux_hosts{$key}{shaky} == 0);
      $bgcolor = "red"    if (  $san_multipath_linux_hosts{$key}{shaky} >  0);
      print OUT "   <td bgcolor=$bgcolor> $san_multipath_linux_hosts{$key}{shaky} \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine






sub generate_html_report_windows_hosts {
   #
   print "running generate_html_report_windows_hosts subroutine \n" if ($verbose eq "yes");
   #
   #
   #
   return unless (@windows_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for Windows hosts
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=7> Windows Hosts \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SNMP <td> CPU util <td> RAM util<td> Paging Space util <td> Disk util\n";
   foreach $key (sort keys %windows_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$windows_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $windows_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $windows_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $windows_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $windows_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $windows_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $windows_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $windows_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $windows_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $windows_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print CPU status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $windows_hosts{$key}{cpu_load} <= 50);
      $bgcolor = "orange" if ( ($windows_hosts{$key}{cpu_load} > 50) && ($windows_hosts{$key}{cpu_load} <= 80) );
      $bgcolor = "red"    if (  $windows_hosts{$key}{cpu_load} > 80);
      print OUT "    <td bgcolor=$bgcolor> $windows_hosts{$key}{cpu_load}\% \n";
      #
      # print RAM status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $windows_hosts{$key}{ram}{hrStorageUsed_pct} <= 99.9);
      $bgcolor = "orange" if ( ($windows_hosts{$key}{ram}{hrStorageUsed_pct} > 99.9) && ($windows_hosts{$key}{ram}{hrStorageUsed_pct} <= 100) );
      $bgcolor = "red"    if (  $windows_hosts{$key}{ram}{hrStorageUsed_pct} > 101);
      print OUT "   <td bgcolor=$bgcolor> $windows_hosts{$key}{ram}{hrStorageUsed_pct}\% \n";
      #
      # print paging space utilization in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $windows_hosts{$key}{paging}{hrStorageUsed_pct} <= 50);
      $bgcolor = "orange" if ( ($windows_hosts{$key}{paging}{hrStorageUsed_pct} > 50) && ($windows_hosts{$key}{paging}{hrStorageUsed_pct} <= 75) );
      $bgcolor = "red"    if (  $windows_hosts{$key}{paging}{hrStorageUsed_pct} > 75);
      print OUT "    <td bgcolor=$bgcolor> $windows_hosts{$key}{paging}{hrStorageUsed_pct}\% \n";
      #
      # print Windows drive letter space utilization in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "    <td bgcolor=$bgcolor> \n" if ($windows_hosts{$key}{os} eq "Windows");	#start the HTML table data for Windows hosts
      for $drive_letter (@drive_letters) {						#loop through for each drive letter a..z  
         next unless ( defined($windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_pct}) ) ;		#skip if this drive letter does not exist
         $fontcolor = "black";								#initialize variable
         $fontcolor = "green"  if (  $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_pct} <= 80 );
         $fontcolor = "orange" if ( ($windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_pct}  > 80 ) && ($windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_pct} <= 90) );
         $fontcolor = "red"    if (  $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_pct}  > 90 );
         print OUT "    <br><font color=$fontcolor> drive $windows_hosts{$key}{windows_drive}{$drive_letter}{drive_letter}: $windows_hosts{$key}{windows_drive}{$drive_letter}{hrStorageUsed_pct}\% \n";
      } 										#end of for loop
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine





sub generate_html_report_idrac9_hosts {
   #
   print "running generate_html_report_idrac9_hosts subroutine \n" if ($verbose eq "yes");
   #
   #
   #
   #
   return unless (@idrac9_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for Dell iDRAC9 service processor hosts
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=7> Dell iDRAC9 Service Processors \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SNMP <td> Model <td> Service Tag <td> System Status <td> Storage Status \n";
   foreach $key (sort keys %idrac9_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$idrac9_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $idrac9_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $idrac9_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $idrac9_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $idrac9_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $idrac9_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $idrac9_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $idrac9_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $idrac9_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $idrac9_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print Model  in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "    <td bgcolor=$bgcolor> $idrac9_hosts{$key}{Model} \n";
      #
      # print Service Tag status in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "   <td bgcolor=$bgcolor> $idrac9_hosts{$key}{ServiceTag} \n";
      #
      # print Global System Status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $idrac9_hosts{$key}{GlobalSystemStatus} eq "ok");
      $bgcolor = "red"    if (  $idrac9_hosts{$key}{GlobalSystemStatus} ne "ok");
      print OUT "    <td bgcolor=$bgcolor> $idrac9_hosts{$key}{GlobalSystemStatus} \n";
      #
      # print Global Storage Status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $idrac9_hosts{$key}{GlobalStorageStatus} eq "ok");
      $bgcolor = "red"    if (  $idrac9_hosts{$key}{GlobalStorageStatus} ne "ok");
      print OUT "    <td bgcolor=$bgcolor> $idrac9_hosts{$key}{GlobalStorageStatus} \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine





sub generate_html_report_idrac8_hosts {
   #
   print "running generate_html_report_idrac8_hosts subroutine \n" if ($verbose eq "yes");
   #
   #
   #
   #
   return unless (@idrac8_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for Dell iDRAC8 service processor hosts
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=6> Dell iDRAC8 Service Processors \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> Model <td> Service Tag <td> System Status <td> Storage Status \n";
   foreach $key (sort keys %idrac8_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$idrac8_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $idrac8_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $idrac8_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $idrac8_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $idrac8_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $idrac8_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor>";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print Model  in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "    <td bgcolor=$bgcolor> $idrac8_hosts{$key}{Model} \n";
      #
      # print Service Tag status in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "   <td bgcolor=$bgcolor> $idrac8_hosts{$key}{ServiceTag} \n";
      #
      # print Global System Status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $idrac8_hosts{$key}{GlobalSystemStatus} eq "ok");
      $bgcolor = "red"    if (  $idrac8_hosts{$key}{GlobalSystemStatus} ne "ok");
      print OUT "    <td bgcolor=$bgcolor> $idrac8_hosts{$key}{GlobalSystemStatus} \n";
      #
      # print Global Storage Status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $idrac8_hosts{$key}{GlobalStorageStatus} eq "ok");
      $bgcolor = "red"    if (  $idrac8_hosts{$key}{GlobalStorageStatus} ne "ok");
      print OUT "    <td bgcolor=$bgcolor> $idrac8_hosts{$key}{GlobalStorageStatus} \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine




sub generate_html_report_unisphere_hosts {
   #
   print "running generate_html_report_unisphere_hosts subroutine \n" if ($verbose eq "yes");
   #
   #
   #
   #
   return unless (@unisphere_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for DellEMC UniSphere hosts
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=5> DellEMC UniSphere Storage Manager Hosts \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SNMP <td> Service Tag <td> System Status  \n";
   foreach $key (sort keys %unisphere_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$unisphere_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $unisphere_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $unisphere_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $unisphere_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $unisphere_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $unisphere_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $unisphere_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $unisphere_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $unisphere_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $unisphere_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print Service Tag status in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "   <td bgcolor=$bgcolor> $unisphere_hosts{$key}{ServiceTag} \n";
      #
      # print productIDGlobalStatus in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $unisphere_hosts{$key}{productIDGlobalStatus} eq "ok");
      $bgcolor = "red"    if (  $unisphere_hosts{$key}{productIDGlobalStatus} ne "ok");
      print OUT "    <td bgcolor=$bgcolor> $unisphere_hosts{$key}{productIDGlobalStatus} \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine



sub generate_html_report_ibm_imm2_hosts {
   #
   print "running generate_html_report_ibm_imm2_hosts subroutine \n" if ($verbose eq "yes");
   #
   #
   #
   #
   return unless (@ibm_imm2_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for Lenovo xClarity Service Processor hosts
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=7> IBM xSeries IMM2 Service Processors  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> Model <td> Serial <td> System Health <td> Power Status <td> Ambient Temperature \n";
   foreach $key (sort keys %ibm_imm2_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$ibm_imm2_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $ibm_imm2_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $ibm_imm2_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $ibm_imm2_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $ibm_imm2_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $ibm_imm2_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor>  <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print Model number in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "   <td bgcolor=$bgcolor> $ibm_imm2_hosts{$key}{Model_Number} \n";
      #
      # print Serial number in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "   <td bgcolor=$bgcolor> $ibm_imm2_hosts{$key}{Serial_Number} \n";
      #
      # print System Health in table row
      #
      $bgcolor = "green";								#initialize variable
      $bgcolor = "red"   if ( $ibm_imm2_hosts{$key}{System_Health} ne "normal" );
      print OUT "   <td bgcolor=$bgcolor> $ibm_imm2_hosts{$key}{System_Health} \n";
      #
      # print Power Status in table row
      #
      $bgcolor = "green";								#initialize variable
      $bgcolor = "red"   if ( $ibm_imm2_hosts{$key}{Power_Status} ne "poweredOn" );
      print OUT "   <td bgcolor=$bgcolor> $ibm_imm2_hosts{$key}{Power_Status} \n";
      #
      # print Ambient Temperature in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $ibm_imm2_hosts{$key}{Ambient_Temperature} <= 25 );
      $bgcolor = "red"    if ( $ibm_imm2_hosts{$key}{Ambient_Temperature} >  25 );
      $bgcolor = "orange" if ( $ibm_imm2_hosts{$key}{Ambient_Temperature} == 9999 );
      $ibm_imm2_hosts{$key}{Ambient_Temperature} = "unknown" if ( $ibm_imm2_hosts{$key}{Ambient_Temperature} == 9999 );  #detect dummy value used as default
      print OUT "    <td bgcolor=$bgcolor> $ibm_imm2_hosts{$key}{Ambient_Temperature}C \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine




sub generate_html_report_xclarity_hosts {
   #
   print "running generate_html_report_xclarity_hosts subroutine \n" if ($verbose eq "yes");
   #
   #
   #
   #
   return unless (@xclarity_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for Lenovo xClarity Service Processor hosts
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=12> Lenovo xClarity Service Processors  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SSH <td> Model <td> Serial <td> Cooling Devices <td> Ambient Temperature <td> Power Modules <td> Local Storage <td> Processors <td> Memory <td> System Health \n";
   foreach $key (sort keys %xclarity_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$xclarity_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $xclarity_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $xclarity_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $xclarity_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $xclarity_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $xclarity_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor>  <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor>  <td bgcolor=$bgcolor> <td bgcolor=$bgcolor>  <td bgcolor=$bgcolor>";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SSH status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $xclarity_hosts{$key}{ssh} eq "ok" );
      $bgcolor = "red"   if ( $xclarity_hosts{$key}{ssh} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $xclarity_hosts{$key}{ssh} \n";
      #
      # if host did not respond to SSH queries, just put blanks in for the rest of the line
      #
      if ( $xclarity_hosts{$key}{ssh} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor>  <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor>  <td bgcolor=$bgcolor> <td bgcolor=$bgcolor>  <td bgcolor=$bgcolor>";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print Model number in table row
      #
      $bgcolor = "green";								#initialize variable
      $bgcolor = "red"   if ( $xclarity_hosts{$key}{vpd}{sys}{Model} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $xclarity_hosts{$key}{vpd}{sys}{Model} \n";
      #
      #
      # print Serial number in table row
      #
      $bgcolor = "green";								#initialize variable
      $bgcolor = "red"   if ( $xclarity_hosts{$key}{vpd}{sys}{Serial} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $xclarity_hosts{$key}{vpd}{sys}{Serial} \n";
      #
      # print status of Cooling Devices (fans) in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $xclarity_hosts{$key}{syshealth}{summary}{Cooling_Devices} eq "Normal");
      $bgcolor = "red"    if ( $xclarity_hosts{$key}{syshealth}{summary}{Cooling_Devices} ne "Normal");
      print OUT "    <td bgcolor=$bgcolor> $xclarity_hosts{$key}{syshealth}{summary}{Cooling_Devices} \n";
      #
      # print Ambient Temperature in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $xclarity_hosts{$key}{temperature}{ambient} <= 25 );
      $bgcolor = "red"    if ( $xclarity_hosts{$key}{temperature}{ambient} >  25 );
      $bgcolor = "orange" if ( $xclarity_hosts{$key}{temperature}{ambient} == 9999 );
      $xclarity_hosts{$key}{temperature}{ambient} = "unknown" if ( $xclarity_hosts{$key}{temperature}{ambient} == 9999 );  #detect dummy value used as default
      print OUT "    <td bgcolor=$bgcolor> $xclarity_hosts{$key}{temperature}{ambient}C \n";
      #
      # print status of Power Modules in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $xclarity_hosts{$key}{syshealth}{summary}{Power_Modules} eq "Normal");
      $bgcolor = "red"    if (  $xclarity_hosts{$key}{syshealth}{summary}{Power_Modules} ne "Normal");
      print OUT "    <td bgcolor=$bgcolor> $xclarity_hosts{$key}{syshealth}{summary}{Power_Modules} \n";
      #
      # print status of Local Storage (internal RAID arrays) in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $xclarity_hosts{$key}{syshealth}{summary}{Local_Storage} eq "Normal");
      $bgcolor = "red"    if (  $xclarity_hosts{$key}{syshealth}{summary}{Local_Storage} ne "Normal");
      print OUT "    <td bgcolor=$bgcolor> $xclarity_hosts{$key}{syshealth}{summary}{Local_Storage} \n";
      #
      # print status of Processors in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $xclarity_hosts{$key}{syshealth}{summary}{Processors} eq "Normal");
      $bgcolor = "red"    if (  $xclarity_hosts{$key}{syshealth}{summary}{Processors} ne "Normal");
      print OUT "    <td bgcolor=$bgcolor> $xclarity_hosts{$key}{syshealth}{summary}{Processors} \n";
      #
      # print status of Memory in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $xclarity_hosts{$key}{syshealth}{summary}{Memory} eq "Normal");
      $bgcolor = "red"    if (  $xclarity_hosts{$key}{syshealth}{summary}{Memory} ne "Normal");
      print OUT "    <td bgcolor=$bgcolor> $xclarity_hosts{$key}{syshealth}{summary}{Memory} \n";
      #
      # print overall system health in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $xclarity_hosts{$key}{syshealth}{summary}{System} eq "Normal");
      $bgcolor = "red"    if (  $xclarity_hosts{$key}{syshealth}{summary}{System} ne "Normal");
      print OUT "    <td bgcolor=$bgcolor> $xclarity_hosts{$key}{syshealth}{summary}{System} \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine




sub generate_html_report_brocade_hosts {
   #
   print "running generate_html_report_brocade_hosts subroutine \n" if ($verbose eq "yes");
   #
   #
   #
   #
   return unless (@brocade_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for Brocae fibre channel switch hosts
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=5> Brocade fibre switches  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SNMP <td> Model <td> Health  \n";
   foreach $key (sort keys %brocade_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$brocade_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $brocade_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $brocade_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $brocade_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $brocade_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $brocade_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT "  <td bgcolor=$bgcolor>  <td bgcolor=$bgcolor>  <td bgcolor=$bgcolor>";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $brocade_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $brocade_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $brocade_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $brocade_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print Model number in table row
      #
      $bgcolor = "green";								#initialize variable
      $bgcolor = "red"   if ( $brocade_hosts{$key}{switch_type} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $brocade_hosts{$key}{switch_type} \n";
      #
      #
      # print overall system health in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $brocade_hosts{$key}{switch_status} eq "OK");
      $bgcolor = "red"    if (  $brocade_hosts{$key}{switch_status} ne "OK");
      print OUT "    <td bgcolor=$bgcolor> $brocade_hosts{$key}{switch_status} \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine



sub generate_html_report_flashsystem_hosts {
   #
   print "running generate_html_report_flashsystem_hosts subroutine \n" if ($verbose eq "yes");
   #
   return unless (@flashsystem_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for IBM FlashSystem storage systems
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=7> IBM FlashSystem storage  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Cluster <td> Ping <td> Health <td>CPU <td>Read latency <td> Write latency  \n";
   foreach $key (sort keys %flashsystem_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$flashsystem_hosts{$key}{hostname} \n" ;
      #
      # print cluster name in table row
      #
      $bgcolor = "white";								#initialize variable
      print OUT "    <td bgcolor=$bgcolor> $flashsystem_hosts{$key}{cluster_name} \n";
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $flashsystem_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $flashsystem_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $flashsystem_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $flashsystem_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $flashsystem_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print overall system health in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $flashsystem_hosts{$key}{health} eq "OK");
      $bgcolor = "red"    if (  $flashsystem_hosts{$key}{health} ne "OK");
      print OUT "    <td bgcolor=$bgcolor> $flashsystem_hosts{$key}{health} \n";
      #
      # print CPU utilization in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $flashsystem_hosts{$key}{cpu_util} <= 50);
      $bgcolor = "red"    if (  $flashsystem_hosts{$key}{cpu_util} >  50);
      print OUT "    <td bgcolor=$bgcolor> $flashsystem_hosts{$key}{cpu_util}\% \n";
      #
      # print read latency in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $flashsystem_hosts{$key}{vdisk_read_latency_ms} <= 50);
      $bgcolor = "red"    if (  $flashsystem_hosts{$key}{vdisk_read_latency_ms} >  50);
      print OUT "    <td bgcolor=$bgcolor> $flashsystem_hosts{$key}{vdisk_read_latency_ms}ms \n";
      #
      # print write latency in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $flashsystem_hosts{$key}{vdisk_write_latency_ms} <= 50);
      $bgcolor = "red"    if (  $flashsystem_hosts{$key}{vdisk_write_latency_ms} >  50);
      print OUT "    <td bgcolor=$bgcolor> $flashsystem_hosts{$key}{vdisk_write_latency_ms}ms \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine




sub generate_html_report_ciscoios_hosts {
   #
   print "running generate_html_report_ciscoios_hosts subroutine \n" if ($verbose eq "yes");
   #
   return unless (@ciscoios_hostnames);                                                 #break out of subroutine if no hostnames are defined
   # Create the HTML table for FortiGate firewalls
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=4> Cisco IOS Devices  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SNMP <td> CPU util \n";
   foreach $key (sort keys %ciscoios_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white";
      print OUT "<tr><td>$ciscoios_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if ( $ciscoios_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $ciscoios_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $ciscoios_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $ciscoios_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $brocade_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $ciscoios_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $ciscoios_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $ciscoios_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $brocade_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print CPU utilization in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if (  $ciscoios_hosts{$key}{cpu_util} <= 75 );
      $bgcolor = "red"    if (  $ciscoios_hosts{$key}{cpu_util} >  75 );
      print OUT "    <td bgcolor=$bgcolor> $ciscoios_hosts{$key}{cpu_util}\% \n";
   }                                                                                    #end of foreach loop
   # print HTML table footer
   print OUT "</table><p>\&nbsp\;</p> \n";
}                                                                                       #end of subroutine



sub generate_html_report_qnap_hosts {
   #
   print "running generate_html_report_qnap_hosts subroutine \n" if ($verbose eq "yes");
   #
   return unless (@qnap_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for QNAP storage systems
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=3> QNAP NAS storage  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> Health  \n";
   foreach $key (sort keys %qnap_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$qnap_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $qnap_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $qnap_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $qnap_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $qnap_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $qnap_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print overall system health in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $qnap_hosts{$key}{health} =~ /QNAP NAS Health OK/);
      $bgcolor = "red"    if (  $qnap_hosts{$key}{health} !~ /QNAP NAS Health OK/);
      print OUT "    <td bgcolor=$bgcolor> $qnap_hosts{$key}{health} \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine




sub generate_html_report_fortigate_hosts {
   #
   print "running generate_html_report_fortigate_hosts subroutine \n" if ($verbose eq "yes");
   #
   return unless (@fortigate_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for FortiGate firewalls
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=6> FortiGate firewalls  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SNMP <td> CPU util <td> RAM util<td> Bandwidth util \n";
   foreach $key (sort keys %fortigate_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$fortigate_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $fortigate_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $fortigate_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $fortigate_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $fortigate_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $fortigate_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $fortigate_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $fortigate_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $fortigate_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $fortigate_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print CPU utilization in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $fortigate_hosts{$key}{cpu_util} <= 75 );
      $bgcolor = "red"    if (  $fortigate_hosts{$key}{cpu_util} >  75 );
      print OUT "    <td bgcolor=$bgcolor> $fortigate_hosts{$key}{cpu_util}\% \n";
      #
      # print RAM utilization in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $fortigate_hosts{$key}{ram_util} <= 75 );
      $bgcolor = "red"    if (  $fortigate_hosts{$key}{ram_util} >  75 );
      print OUT "    <td bgcolor=$bgcolor> $fortigate_hosts{$key}{ram_util}\% \n";
      #
      # print bandwidth utilization in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $fortigate_hosts{$key}{bandwidth_mbps} <= 1000 );	#arbitrary decision to be ok with less than 1000Mbit/sec bandwidth
      $bgcolor = "red"    if (  $fortigate_hosts{$key}{bandwidth_mbps} >  1000 );		
      print OUT "    <td bgcolor=$bgcolor> $fortigate_hosts{$key}{bandwidth_mbps} Mbps \n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine




sub generate_html_report_hpilo4_hosts {
   #
   print "running generate_html_report_hpilo4_hosts subroutine \n" if ($verbose eq "yes");
   #
   return unless (@hpilo4_hostnames);							#break out of subroutine if no hostnames are defined
   # Create the HTML table for FortiGate firewalls
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=11> Hewlett Packard ILO4 Service Processors  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SNMP <td> Power Redundancy <td> Fans <td> Ambient Temperature <td> Physical Disks <td> Logical Disks <td> RAID controller <td> Processors <td> Memory Modules \n";
   foreach $key (sort keys %hpilo4_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white"; 
      print OUT "<tr><td>$hpilo4_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $hpilo4_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $hpilo4_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $hpilo4_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $hpilo4_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $hpilo4_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $hpilo4_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $hpilo4_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print Power Supply redundancy status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} eq "ok" );
      $bgcolor = "red"    if ( $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} ne "ok" );
      print OUT "    <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{cpqHeFltTolPwrSupplyCondition} \n";
      #
      # print fan status table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $hpilo4_hosts{$key}{fans}{count} == $hpilo4_hosts{$key}{fans}{ok} );
      $bgcolor = "red"    if ( $hpilo4_hosts{$key}{fans}{count} != $hpilo4_hosts{$key}{fans}{ok} );
      print OUT "    <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{fans}{ok}/$hpilo4_hosts{$key}{fans}{count} fans ok\n";
      #
      # print ambient temperature in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if ( $hpilo4_hosts{$key}{ChassisInletTemperatureC} <= 25   );
      $bgcolor = "red"    if ( $hpilo4_hosts{$key}{ChassisInletTemperatureC} >  25   );
      $bgcolor = "orange" if ( $hpilo4_hosts{$key}{ChassisInletTemperatureC} == 9999 );  #detect dummy value used as default
      $hpilo4_hosts{$key}{ChassisInletTemperatureC} = "unknown" if ( $hpilo4_hosts{$key}{ChassisInletTemperatureC} == 9999 );  #detect dummy value used as default
      print OUT "    <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{ChassisInletTemperatureC} C \n";
      #
      # print physical disk status table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $hpilo4_hosts{$key}{physical_disks}{count} == $hpilo4_hosts{$key}{physical_disks}{ok} );
      $bgcolor = "red"    if (  $hpilo4_hosts{$key}{physical_disks}{count} != $hpilo4_hosts{$key}{physical_disks}{ok} );
      print OUT "    <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{physical_disks}{ok}/$hpilo4_hosts{$key}{physical_disks}{count} disks ok\n";
      #
      # print logical disk status table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $hpilo4_hosts{$key}{logical_disks}{count} == $hpilo4_hosts{$key}{logical_disks}{ok} );
      $bgcolor = "red"    if (  $hpilo4_hosts{$key}{logical_disks}{count} != $hpilo4_hosts{$key}{logical_disks}{ok} );
      print OUT "    <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{logical_disks}{ok}/$hpilo4_hosts{$key}{logical_disks}{count} disks ok\n";
      #
      # print RAID controller status table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $hpilo4_hosts{$key}{raid_controller}{count} == $hpilo4_hosts{$key}{raid_controller}{ok} );
      $bgcolor = "red"    if (  $hpilo4_hosts{$key}{raid_controller}{count} != $hpilo4_hosts{$key}{raid_controller}{ok} );
      print OUT "    <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{raid_controller}{ok}/$hpilo4_hosts{$key}{raid_controller}{count} ok\n";
      #
      # print processor module status table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $hpilo4_hosts{$key}{processor_status}{count} == $hpilo4_hosts{$key}{processor_status}{ok} );
      $bgcolor = "red"    if (  $hpilo4_hosts{$key}{processor_status}{count} != $hpilo4_hosts{$key}{processor_status}{ok} );
      print OUT "    <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{processor_status}{ok}/$hpilo4_hosts{$key}{processor_status}{count} ok\n";
      #
      # print memory module status table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green"  if (  $hpilo4_hosts{$key}{memory_module_status}{count} == $hpilo4_hosts{$key}{memory_module_status}{ok} );
      $bgcolor = "red"    if (  $hpilo4_hosts{$key}{memory_module_status}{count} != $hpilo4_hosts{$key}{memory_module_status}{ok} );
      print OUT "    <td bgcolor=$bgcolor> $hpilo4_hosts{$key}{memory_module_status}{ok}/$hpilo4_hosts{$key}{memory_module_status}{count} ok\n";
   } 											#end of foreach loop
   # print HTML table footer 
   print OUT "</table><p>\&nbsp\;</p> \n";
}											#end of subroutine 



sub generate_html_report_aix_hosts {
   #
   print "running generate_html_report_aix_hosts subroutine \n" if ($verbose eq "yes");
   #
   return unless (@aix_hostnames);                                                      #break out of subroutine if no hostnames are defined
   # Create the HTML table for IBM AIX hosts
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=5> AIX hosts  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> CPU <td> paging <td> errpt \n";
   foreach $key (sort keys %aix_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white";
      print OUT "<tr><td>$aix_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if ( $aix_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $aix_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $aix_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $aix_hosts{$key}{ping} \n";
      #
      # print CPU utilization status in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green" if (  $aix_hosts{$key}{cpu} eq "OK" );
      $bgcolor = "red"   if (  $aix_hosts{$key}{cpu} ne "OK" );
      print OUT "   <td bgcolor=$bgcolor> $aix_hosts{$key}{cpu} \n";
      #
      # print paging space utilization status in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green" if (  $aix_hosts{$key}{paging} eq "OK" );
      $bgcolor = "red"   if (  $aix_hosts{$key}{paging} ne "OK" );
      print OUT "   <td bgcolor=$bgcolor> $aix_hosts{$key}{paging} \n";
      #
      # print AIX error report status in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green" if (  $aix_hosts{$key}{errpt} eq "OK" );
      $bgcolor = "red"   if (  $aix_hosts{$key}{errpt} ne "OK" );
      print OUT "   <td bgcolor=$bgcolor> $aix_hosts{$key}{errpt} \n";
   }                                                                                    #end of foreach loop
   # print HTML table footer
   print OUT "</table><p>\&nbsp\;</p> \n";
}                                                                                       #end of subroutine



sub generate_html_report_hmc_hosts {
   #
   print "running generate_html_report_hmc_hosts subroutine \n" if ($verbose eq "yes");
   #
   return unless (@hmc_hostnames);                                                      #break out of subroutine if no hostnames are defined
   # Create the HTML table for IBM Hardware Management Consoles
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=3> IBM Hardware Management Consoles  \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> Health  \n";
   foreach $key (sort keys %hmc_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white";
      print OUT "<tr><td>$hmc_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if ( $hmc_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $hmc_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $hmc_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $hmc_hosts{$key}{ping} \n";
      #
      # print overall system health in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if ( $hmc_hosts{$key}{health} eq "OK" );
      $bgcolor = "red"    if ( $hmc_hosts{$key}{health} ne "OK" );
      print OUT "    <td bgcolor=$bgcolor> $hmc_hosts{$key}{health} \n";
   }                                                                                    #end of foreach loop
   # print HTML table footer
   print OUT "</table><p>\&nbsp\;</p> \n";
}                                                                                       #end of subroutine


sub generate_html_report_mikrotik_swos_hosts {
   #
   print "running generate_html_report_mikrotik_swos_hosts subroutine \n" if ($verbose eq "yes");
   #
   return unless (@mikrotik_swos_hostnames);                                                    #break out of subroutine if no hostnames are defined
   # Create the HTML table for MikroTik SwOS devices
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=4> MikroTik SwOS hosts \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> Ping <td> SNMP <td> Health  \n";
   foreach $key (sort keys %mikrotik_swos_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white";
      print OUT "<tr><td>$mikrotik_swos_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if ( $mikrotik_swos_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $mikrotik_swos_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $mikrotik_swos_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $mikrotik_swos_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $mikrotik_swos_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $mikrotik_swos_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $mikrotik_swos_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $mikrotik_swos_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $mikrotik_swos_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print overall system health in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if ( $mikrotik_swos_hosts{$key}{health} eq "OK" );
      $bgcolor = "red"    if ( $mikrotik_swos_hosts{$key}{health} ne "OK" );
      print OUT "    <td bgcolor=$bgcolor> $mikrotik_swos_hosts{$key}{health} \n";
   }                                                                                    #end of foreach loop
   # print HTML table footer
   print OUT "</table><p>\&nbsp\;</p> \n";
}                                                                                       #end of subroutine



sub generate_html_report_netapp_hosts {
   #
   print "running generate_html_report_netapp_hosts subroutine \n" if ($verbose eq "yes");
   #
   return unless (@netapp_hostnames);                                                   #break out of subroutine if no hostnames are defined
   # Create the HTML table for NetApp ONTAP storage systems
   #
   print OUT "<table border=1> \n";
   print OUT "<tr bgcolor=gray><td colspan=5> NetApp ONTAP storage systems \n";
   print OUT "<tr bgcolor=gray><td> Hostname <td> ping <td> SNMP <td> ONTAP <td> Health  \n";
   foreach $key (sort keys %netapp_hosts) {
      #
      # print hostname field in table row
      #
      $bgcolor = "white";
      print OUT "<tr><td>$netapp_hosts{$key}{hostname} \n" ;
      #
      # print ping status in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if ( $netapp_hosts{$key}{ping} eq "up" );
      $bgcolor = "red"    if ( $netapp_hosts{$key}{ping} eq "down" );
      $bgcolor = "orange" if ( $netapp_hosts{$key}{ping} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $netapp_hosts{$key}{ping} \n";
      #
      # if host did not respond to ping, just put blanks in for the rest of the line
      #
      if ( $netapp_hosts{$key}{ping} ne "up" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print SNMP status in table row
      #
      $bgcolor = "white";								#initialize variable
      $bgcolor = "green" if ( $netapp_hosts{$key}{snmp} eq "ok" );
      $bgcolor = "red"   if ( $netapp_hosts{$key}{snmp} eq "unknown" );
      print OUT "   <td bgcolor=$bgcolor> $netapp_hosts{$key}{snmp} \n";
      #
      # if host did not respond to SNMP queries, just put blanks in for the rest of the line
      #
      if ( $netapp_hosts{$key}{snmp} ne "ok" ) { 
         $bgcolor = "white";
         print OUT " <td bgcolor=$bgcolor> <td bgcolor=$bgcolor> ";
         next;   									#skip the rest of this for loop iteration
      }
      #
      # print ONTAP version field in table row
      #
      $bgcolor = "white";
      print OUT "    <td>$netapp_hosts{$key}{ontap_version} \n" ;
      #
      # print overall system health in table row
      #
      $bgcolor = "white";                                                               #initialize variable
      $bgcolor = "green"  if ( $netapp_hosts{$key}{miscGlobalStatus} eq "OK" );
      $bgcolor = "red"    if ( $netapp_hosts{$key}{miscGlobalStatus} ne "OK" );
      print OUT "    <td bgcolor=$bgcolor> $netapp_hosts{$key}{miscGlobalStatus} \n";
   }                                                                                    #end of foreach loop
   # print HTML table footer
   print OUT "</table><p>\&nbsp\;</p> \n";
}                                                                                       #end of subroutine




sub generate_html_report_footer {
   #
   print "running generate_html_report_footer subroutine \n" if ($verbose eq "yes");
   #
   print OUT "<hr> \n";
   print OUT "<br><b>How to use this report</b> \n";
   print OUT "<br><ul><li>If everything is <font color=green> green</font>, all is good, and no further action is needed. \n";
   print OUT "<br><li>If you see any <font color=red>red</font> or yellow warnings, please check the monitoring system for additional detail: $monitoring_system_url \n";
   print OUT "<br><li>This report shows performance metrics like CPU/RAM/paging at a single moment in time.  If this report is reporting something like high CPU, go check that machine to see if it was just a brief spike in high CPU, or is indicative of a long-running problem. \n";
   print OUT "<br><li>This report is intentionally a very high level snapshot of system health at a specific point in time.  It is not a substitute for a monitoring system like nagios, PRTG, etc.  For additional detail, please check the monitoring system at $monitoring_system_url  \n";
   print OUT "</ul></body></html> \n";
   close OUT;										#close filehandle
} 											#end of subroutine







sub send_report_via_email {
   #
   print "running send_report_via_email subroutine \n" if ($verbose eq "yes");
   #
   open(MAIL,"|$sendmail -t");
   ## Mail Header
   print MAIL "To: $to\n";
   print MAIL "From: $from\n";
   print MAIL "Subject: $subject\n";
   ## Mail Body
   print MAIL "Content-Type: text/html; charset=ISO-8859-1\n\n";
   open (IN,"$output_file") or warn "Cannot open $output_file for reading: $! \n";
   while (<IN>) { 				#read a line from the filehandle
      print MAIL $_;				#print to email message
   } 						#end of while loop
   close IN;					#close filehandle
   close MAIL;					#close filehandle
} 						#end of subroutine



# ---------------- main body of script --------------
sanity_checks;
read_config_file;
get_date;
define_hosts;
ping_hosts;
#
# check operating systems
#
verify_os_linux;
verify_os_windows;
get_cpu_util_linux;
get_cpu_util_windows;
get_ram_util_linux;
get_ram_util_windows;
get_paging_space_util_linux;
get_paging_space_util_windows;
get_windows_drive_util;
get_linux_fs_util;
get_san_multipath_linux_status;
get_linux_status;   #miscellaneous SSH-based checks
get_aix_status;
#
# check service processors
#
get_dell_idrac8_status;
get_dell_idrac9_status;
get_hpilo4_status;
get_ibm_imm2_status;
get_lenovo_xclarity_status;
get_hmc_status;
#
# check SAN storage
#
get_brocade_status;
get_emc_unisphere_status;
get_flashsystem_status;
get_qnap_status;
get_netapp_status;
#
# check networking devices
#
get_ciscoios_status;
get_fortigate_status;
get_mikrotik_swos_status;
#
# generate HTML report of all devices that were found
#
generate_html_report_header;			#just create the initial HTML header for the report
generate_html_report_linux_hosts;		#if any linux       hosts exist, add them to the report 
generate_html_report_san_multipath_linux_hosts;	#if any bare-metal linux hosts exist, add them to the report 
generate_html_report_aix_hosts;         	#if any aix              hosts exist, add them to the report
generate_html_report_windows_hosts;		#if any windows          hosts exist, add them to the report 
generate_html_report_idrac9_hosts;		#if any idrac9           hosts exist, add them to the report 
generate_html_report_idrac8_hosts;		#if any idrac8           hosts exist, add them to the report 
generate_html_report_hpilo4_hosts;		#if any hpilo4           hosts exist, add them to the report 
generate_html_report_ibm_imm2_hosts;		#if any IBM IMM2         hosts exist, add them to the report 
generate_html_report_xclarity_hosts;		#if any xclarity         hosts exist, add them to the report 
generate_html_report_hmc_hosts;        	 	#if any hmc              hosts exist, add them to the report
generate_html_report_brocade_hosts;		#if any brocade          hosts exist, add them to the report 
generate_html_report_unisphere_hosts;		#if any unisphere        hosts exist, add them to the report 
generate_html_report_flashsystem_hosts;		#if any flashsystem      hosts exist, add them to the report 
generate_html_report_netapp_hosts;      	#if any netapp           hosts exist, add them to the report
generate_html_report_qnap_hosts;		#if any qnap             hosts exist, add them to the report 
generate_html_report_ciscoios_hosts;    	#if any ciscoios         hosts exist, add them to the report
generate_html_report_fortigate_hosts;		#if any fortigate        hosts exist, add them to the report 
generate_html_report_mikrotik_swos_hosts;       #if any hmc              hosts exist, add them to the report
generate_html_report_footer;			#now that all hosts have been added to the report, add the HTML footer
send_report_via_email;

