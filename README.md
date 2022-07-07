# daily_status_report
daily email report of IT infrastructure status
This report piggybacks off data already collected via nagios, and sends out a point-in-time status via email.

# Assumptions
It is assumed you already have a working nagios environment in place, which provides SSH key pair auth to monitored devices

# Installation
Copy the .pl and .cfg files to the nagios user home directory
Create a cron job similar to the following:
```
    5 * * * * /home/nagios/daily_status_report.pl >/dev/null 2>&1 #generate daily report of host health
```
