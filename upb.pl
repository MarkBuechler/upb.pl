#!/usr/bin/perl
my $Version  = 'UPB Interface v1.1';

# UPB Interface
#
# Written by Mark Buechler 10/21/16
# Portions ported from Echo Python Client http://fabricate.io

sub usage
  {
    die <<"EndUsage";
$Version

Usage:
     -config <config> : Use alternate config file <config>.
     -server          : Run in server mode
       -listen <port> : Listen for commands on port <port>.
     -monitor         : Run in monitor mode
     -wemo            : Emulate Belkin WeMo devices

     -set <state>     : Set a device state
       -pim <pim>
       -network <network>
       -device <device>
       -arg <arg>

     -state           : Return the current state
       -pim <pim>
       -network <network>
       -device <device>

     -debug           : Place in debug mode.

VALID STATES:
     ON    : Set a device level 100%.
     OFF   : Set a device level 0%.
     TOGGLE: Toggle ON/OFF state.
     LEVEL : Set a light device level to <arg>%.
     BLINK : Set a device to blink at rate <arg>.

EndUsage
  }

use Getopt::Long;
use IO::Socket;
use IO::Socket::Multicast;
use IO::Select;
use IO::File;
use Net::Address::IP::Local;
use Time::Local;
use FileHandle;
use IPC::Shareable qw(:lock);
use Time::HiRes qw(time alarm sleep);
use UUID::Tiny ':std';
use Data::Dumper;
use UUID::Tiny;
use POSIX;
use strict;

use constant {
	TRUE			=> 1,
	FALSE			=> 0,

	UPB_ACCEPT		=> 0x00,
	UPB_ACK			=> 0x01,
	UPB_NO_ACK		=> 0x02,
	UPB_BUSY		=> 0x03,
	UPB_ERROR		=> 0x04,
	UPB_INCOMING		=> 0x05,
	UPB_REGISTER		=> 0x06,

	ACK_TYPE_ACK_PULSE	=> 0x01,
	ACK_TYPE_ID_PULSE	=> 0x02,
	ACK_TYPE_MESSAGE	=> 0x04,

	REPEATER_NON		=> 0x00,
	REPEATER_LOW		=> 0x01,
	REPEATER_MEDIUM		=> 0x02,
	REPEATER_HIGH		=> 0x03,

	LINK_TYPE_DIRECT	=> 0x00,
	LINK_TYPE_LINK		=> 0x01,
	LINK_TYPE_DEVICE	=> 0x02, # Undocumented, device to device

	MSG_TYPE_CORE_CMD	=> 0x00,
	MSG_TYPE_DEVICE		=> 0x01,
	MSG_TYPE_CORE_RPT	=> 0x04,
	MSG_TYPE_EXTENDED	=> 0x07,

	# Core commands
	CORE_CMD_NULL		=> 0x00,
	CORE_CMD_WRITE_ENABLE	=> 0x01,
	CORE_CMD_WRITE_PROTECT	=> 0x02,
	CORE_CMD_START_SETUP	=> 0x03,
	CORE_CMD_STOP_SETUP	=> 0x04,
	CORE_CMD_SETUP_TIME	=> 0x05,
	CORE_CMD_AUTO_ADDRESS	=> 0x06,
	CORE_CMD_DEVICE_STATUS	=> 0x07,
	CORE_CMD_DEVICE_CONTROL	=> 0x08,
	CORE_CMD_ADD_LINK	=> 0x0b,
	CORE_CMD_DELETE_LINK	=> 0x0c,
	CORE_CMD_TRANSMIT_MSG	=> 0x0d,
	CORE_CMD_RESET		=> 0x0e,
	CORE_CMD_DEVICE_SIG	=> 0x0f,
	CORE_CMD_GET_REGISTER	=> 0x10,
	CORE_CMD_SET_REGISTER	=> 0x11,

	# Device commands
	DEV_ACTIVATE_LINK	=> 0x00,
	DEV_DEACTIVATE_LINK	=> 0x01,
	DEV_GOTO		=> 0x02,
	DEV_FADE_START		=> 0x03,
	DEV_FADE_STOP		=> 0x04,
	DEV_BLINK		=> 0x05,
	DEV_INDICATE		=> 0x06,
	DEV_TOGGLE		=> 0x07,
	DEV_REPORT_STATE	=> 0x10,
	DEV_STORE_STATE		=> 0x11,

	# Device reports
	RPT_ACKNOWLEDGE		=> 0x00,
	RPT_SETUP_TIME		=> 0x05,
	RPT_DEVICE_STATE	=> 0x06,
	RPT_DEVICE_STATUS	=> 0x07,
	RPT_DEV_SIGNATURE	=> 0x0f,
	RPT_REGISTERS		=> 0x10,
	RPT_RAM			=> 0x11,
	RPT_RAW			=> 0x12,
	RPT_HEARTBEAT		=> 0x13,
};

my @UPB_CODES = (
	'ACCEPT',
	'ACKNOWLEDGE',
	'NO ACKNOWLEDGE',
	'BUSY',
	'ERROR',
	'INCOMING',
	'REGISTER'
);

my %serverOpts = (
	create    => 1,
	exclusive => 0,
	mode      => 0644,
	destroy   => 1
);

my %pollerOpts = (
	create    => 0,
	exclusive => 0,
	mode      => 0644,
	destroy   => 0
);

my %REGISTERS;
my %POLLERS;
my %IN_QUEUE;
my %OUT_QUEUE;
my %PENDING_QUEUE;
my %DEV_STATES;
my %DEV_SETS;
my $CONFIG;
my %CTS;
my %CLIENTS;
my $TOPLEVEL = FALSE;
my $UPNP_CHILD;

my $LAST_PACKET;

my $UPNP_VENDOR = "Belkin\:device";
my @UPNP_DEV_SOCKETS;
my %UPNP_SOCKET_NAME;

%IN_QUEUE = ();
%OUT_QUEUE = ();
%DEV_STATES = ();
%DEV_SETS = ();
%CTS = ();

# Debug stuff
my $_DEBUG_;

# Default config file location
my $DEF_CONFIG = '/etc/upb.conf';

STDOUT->autoflush(1);
STDIN->autoflush(1);

main();

sub getArgs {
	my $config;
	my $pim;
	my $network;
	my $device;
	my $state;
	my $set;
	my $argument;
	my $server;
	my $listen;
	my $monitor;
	my $wemo;
	my $decode;

	my $p = new Getopt::Long::Parser;

	if (!$p->getoptions('config=s'		=> \$config,
			    'server'		=> \$server,
			    'listen=i'		=> \$listen,
			    'monitor'		=> \$monitor,
			    'wemo'		=> \$wemo,
			    'pim=s'		=> \$pim,
			    'network=i' 	=> \$network,
			    'device=i'  	=> \$device,
			    'set=s'		=> \$set,
			    'state'		=> \$state,
			    'argument=s'	=> \$argument,
			    'decode=s'		=> \$decode,
			    'debug'		=> \$_DEBUG_)) {
		print "Invalid parameters given.\n";
		usage();
	}

	$_DEBUG_ = TRUE if (defined($_DEBUG_));
	$config = $DEF_CONFIG if (!$config);
	$server = TRUE if (defined($server));
	$monitor = TRUE if (defined($monitor));
	$wemo = TRUE if (defined($wemo));

	my $args = (defined($server) + defined($monitor) +
		    defined($state) + defined($set) + defined($decode));

	if (!$args || ($args > 1)) {
		print "Please specify one of -server -monitor -set -state.\n";
		usage();
	}

	if ($listen && !$server) {
		print "Please specify -server with -listen.\n";
		usage();
	}

	if ($set && (!$pim || !$network || !$device)) {
		print "Please specify -pim -network and -device with -set.\n";
		usage();
	}

	if ($state && (!$pim || !$network || !$device)) {
		print "Please specify -pim -network and -device with -state.\n";
		usage();
	}

	if ($set =~ /BLINK/i) {
		if (!$argument) {
			print "State BLINK requires -argument.\n";
		}
	}

	if ($set =~ /LEVEL/i) {
		if (!$argument) {
			print "State LEVEL requires -argument.\n";
		}
	}

	return ($config, $server, $listen, $monitor, $wemo, $pim, $network,
	  $device, $set, $state, $argument, $decode);
}

sub main {
	my ($configFile, $server, $listen, $monitor, $wemo, $pim, $network,
	  $device, $set, $state, $argument, $decode) = getArgs();

	readConfigFile($configFile);

	if ($decode) {
		my $packet = decodeUPBPacket($decode);
		print Dumper($packet);
		exit;
	}

	if ($server) {
		startServer($listen, $wemo);
	} elsif ($monitor) {
		tie %DEV_STATES, 'IPC::Shareable', 'upbs', \%serverOpts;
		tie %DEV_SETS, 'IPC::Shareable', 'upbd', \%serverOpts;

		startMonitor(\*STDIN);
	} elsif ($set) {
		tie %DEV_STATES, 'IPC::Shareable', 'upbs', \%serverOpts;
		tie %DEV_SETS, 'IPC::Shareable', 'upbd', \%serverOpts;

		setDeviceState($pim, $network, $device, $set, $argument);
	} elsif ($state) {
		tie %DEV_STATES, 'IPC::Shareable', 'upbs', \%serverOpts;

		print reportDeviceState($pim, $network, $device, $state, $argument)."\n";
	}
}

sub startServer {
	my $listen = shift;
	my $wemo = shift;

	$SIG{INT}  = \&commitSuicide;
	$SIG{TERM} = \&commitSuicide;
	$SIG{CHLD} = \&childDied;

	tie %IN_QUEUE, 'IPC::Shareable', 'upbi', \%serverOpts;
	tie %OUT_QUEUE, 'IPC::Shareable', 'upbo', \%serverOpts;
	tie %CTS, 'IPC::Shareable', 'upbc', \%serverOpts;

	my $pims = $$CONFIG{'PIMS'}->{'PIM'};

	foreach my $pim (keys %{$pims}) {
		my $network = popkey($$pims{$pim}->{'NETWORK'});
		my $device = popkey($$pims{$pim}->{'DEVICE'});
		my $password = popkey($$pims{$pim}->{'PASSWORD'});

		my $host = popkey($$pims{$pim}->{'HOST'});
		my $port = popkey($$pims{$pim}->{'PORT'});

		spawnPoller($pim, $host, $port);

		setClearToSend($pim, TRUE);

		setMessageMode($pim);
		getRegisters($pim, 0, 0xff);

		setupPIM($pim, $network, $password, $device);
	}

	tie %DEV_STATES, 'IPC::Shareable', 'upbs', \%serverOpts;
	tie %DEV_SETS, 'IPC::Shareable', 'upbd', \%serverOpts;

	checkDeviceStates();

	if ($wemo) {
		logEvent("Emulating WeMo devices.");
		my $upnp_socket;
		$upnp_socket = openUPnPListenSocket();
		startUPnPBroadcastMonitor($upnp_socket);
		openUPnPDeviceSockets();
	}

	logEvent("Opening listening port on $listen.");

	my $host_ip = Net::Address::IP::Local->public;
	my $listener = openListenSocket($host_ip, $listen);

	$0 = "upb.pl (Server)";
	$TOPLEVEL = TRUE;

	logEvent("Initialization complete.");

	while(TRUE) {
		checkForUPnPConnection();

		foreach my $pim (keys %{$pims}) {
			checkDeviceSets($pim);
			parseResponse($pim, popResponseQueue($pim));
			checkPendingQueue($pim);
			checkForConnection($listener);
		}

		sleep .1;
	}
}

sub checkForConnection {
	my $listener = shift;
	my $child;

	my $socket = $listener->accept();

	if (defined($socket)) {
		my $addr = $socket->peerhost();
		my $port = $socket->peerport();

		logEvent("Opening upb client connection for $addr.");

		logEvent("can't fork: $!") unless defined($child = fork());

		if ($child) {
			$CLIENTS{$child} = $socket;
		} else {
			POSIX::setsid();

			$TOPLEVEL = FALSE;

			$socket->sockopt(SO_KEEPALIVE, 1);

			$0 = "upb.pl (Servicing $addr:$port)";

			startMonitor($socket);

			logEvent("Connection to $addr closed.");

			$socket->close();

			exit;
		}
	}
}

sub checkForUPnPConnection {
	my $child;

	foreach my $listener (@UPNP_DEV_SOCKETS) {
		my $socket = $listener->accept();

		if (defined($socket)) {
			my $addr = $socket->peerhost;
			my $port = $socket->peerport;
			my $name = $UPNP_SOCKET_NAME{$listener}->{'NAME'};

			logEvent("Opening UPnP client connection for '$name' at $addr.");

			logEvent("can't fork: $!") unless defined($child = fork());

			if ($child) {
				$CLIENTS{$child} = $socket;
			} else {
				POSIX::setsid();

				$TOPLEVEL = FALSE;

				$socket->sockopt(SO_KEEPALIVE, 1);

				$0 = "upb.pl (Servicing UPnP $addr:$port)";

				startUPnPMonitor($socket, $listener);

				logEvent("UPnP connection to $addr closed.");

				$socket->close();

				exit;
			}
		}
	}
}

sub openListenSocket {
	my $addr = shift;
	my $port = shift;

	my $socket = IO::Socket::INET->new(LocalHost => $addr,
					   LocalPort => $port,
					   Proto => 'tcp',
					   Listen => 1,
					   Reuse => 1);

	if (!$socket) {
		logEvent("Unable to open listening socket on port $port: $!");
		commitSuicide();
	}

	fcntl($socket, F_SETFL(), O_NONBLOCK());

	return $socket;
}

sub openUPnPListenSocket {
	my $ip = popkey($$CONFIG{'WEMO'}->{'UPNP_LISTEN_IP'});
	my $port = popkey($$CONFIG{'WEMO'}->{'UPNP_LISTEN_PORT'});
	my $interface = popkey($$CONFIG{'WEMO'}->{'UPNP_LISTEN_INTERFACE'});

	if (!$ip || !$port || !$interface) {
		logEvent("FATAL: WEMO improperly configured, cannot continue!");
		commitSuicide();
	}

	logEvent("Opening UPnP Broadcast listener on $ip:$port using interface $interface.");

	my $socket = IO::Socket::Multicast->new(LocalPort => $port,
						ReuseAddr => 1,
						Blocking => 0);
	if (!$socket) {
		logEvent("Unable to open uPnP listening socket on port $port: $!");
		commitSuicide();
	}

	$socket->mcast_loopback(0);
	$socket->mcast_add($ip, $interface);

	fcntl($socket, F_SETFL(), O_NONBLOCK());

	return $socket;
}	

sub openUPnPDeviceSockets {
	my $ip = popkey($$CONFIG{'WEMO'}->{'UPNP_BIND_IP'});

	my $pims = $$CONFIG{'NETWORKS'}->{'PIM'};

	foreach my $pim (keys %{$pims}) {
		foreach my $network (sort keys %{$$pims{$pim}->{'NETWORK'}}) {
			my $devices = $$pims{$pim}->{'NETWORK'}->{$network}->{'DEVICE'};

			foreach my $device (sort keys %{$devices}) {
				my $name = popkey($$devices{$device}->{'WEMO_NAME'});
				my $upnp_port = popkey($$devices{$device}->{'UPNP_PORT'});

				logEvent("Opening UPnP Device listener for device \"$name\" on port $upnp_port.");

				my $socket = IO::Socket::INET->new(LocalHost => $ip,
					 			   LocalPort => $upnp_port,
								   Proto => 'tcp',
								   Listen => 1,
					  			   Reuse => 1);

				if (!$socket) {
					logEvent("FATAL: Unable to open UPnP Device listening socket on port $upnp_port, aborting.");
					commitSuicide();
				}

				fcntl($socket, F_SETFL(), O_NONBLOCK());

				push @UPNP_DEV_SOCKETS, $socket;
				$UPNP_SOCKET_NAME{$socket}->{'NAME'}    = $name;
				$UPNP_SOCKET_NAME{$socket}->{'PIM'}     = $pim;
				$UPNP_SOCKET_NAME{$socket}->{'NETWORK'} = $network;
				$UPNP_SOCKET_NAME{$socket}->{'DEVICE'}  = $device;
			}
		}
	}
}

sub startMonitor {
	my $socket = shift;
	my %current_states;

	my $handle = $socket;
	$handle = \*STDOUT if (ref($handle) eq 'GLOB');

	while (TRUE) {
		checkStateDifferences($handle, \%current_states);
		checkMonitorInput($socket);

		sleep .2;
	}
}

sub startUPnPMonitor {
	my $socket = shift;
	my $listener = shift;

	while (TRUE) {
		checkUPnPInput($socket, $listener);

		sleep .2;
	}
}

sub startUPnPBroadcastMonitor {
	my $socket = shift;

	my $child = fork();

	if (!defined($child)) {
		logEvent("FATAL: Can't fork: $!");
		commitSuicide();
	}

	if (!$child) {
		POSIX::setsid();

		$0 = "upb.pl (UPnP Broadcast Listener)";

		while (TRUE) {
			checkUPnPInput($socket);

			sleep .2;
		}
	} else {
		$UPNP_CHILD = $child;
	}
}

sub setupPIM {
	my $pim = shift;
	my $networkid = shift;
	my $password = shift;
	my $deviceid = shift;

	logEvent("Setting up PIM '$pim'.");

	my $o_networkid = hex($REGISTERS{$pim}->{'NETWORK_ID'});
	my $o_password = hex($REGISTERS{$pim}->{'NETWORK_PASS'});
	my $o_deviceid = hex($REGISTERS{$pim}->{'MODULE_ID'});

	if ($o_networkid != $networkid) {
		logEvent(sprintf("PIM '$pim': Current networkid is %02x, setting to %02x.",
		  $o_networkid, $networkid));
		setNetworkId($pim, $networkid);
	}

	if ($o_password != $password) {
		logEvent(sprintf("PIM '$pim': Current network password is %04x, setting to %04x.",
		  $o_password, $password));
		setNetworkPassword($pim, $password);
	}

	if ($o_deviceid ne $deviceid) {
		logEvent(sprintf("PIM '$pim': Current device id is %02x, setting to %02x.",
		  $o_deviceid, $deviceid));
		setDeviceId($pim, $deviceid);
	}

	logEvent("PIM '$pim' setup complete.");
}

sub spawnPoller {
	my $pim = shift;
	my $host = shift;
	my $port = shift;

	logEvent("PIM '$pim': Poller starting up.");

	my $sock = createSocket($host, $port);

	my $child = fork();

	if (!defined($child)) {
		logEvent("FATAL: Can't fork: $!");
		commitSuicide();
	}

	if (!$child) {
		POSIX::setsid();

		$0 = "upb.pl (Poller for $pim)";

		tie %IN_QUEUE, 'IPC::Shareable', 'upbi', \%pollerOpts;
		tie %OUT_QUEUE, 'IPC::Shareable', 'upbo', \%pollerOpts;
		tie %CTS, 'IPC::Shareable', 'upbc', \%pollerOpts;

		# Notify our main process..
		(tied %IN_QUEUE)->shlock;
		push @{$IN_QUEUE{$pim}}, '__POLLER_STARTED__';
		(tied %IN_QUEUE)->shunlock;

		while (TRUE) {
			checkIncomingData($pim, $sock);
			checkCommandQueue($pim, $sock);
			checkClearToSend($pim);
			sleep .5;
		}
	} else {
		$POLLERS{$child} = $pim;

		# Wait for the poller to start
		my $started;
		while (!$started) {
			$started = popResponseQueue($pim);
			sleep 0.1 if (!$started);
			undef $started if ($started ne '__POLLER_STARTED__');
		}

		logEvent("PIM '$pim': Poller started");
	}
}

sub checkCommandQueue {
	my $pim = shift;
	my $sock = shift;

	if (!isClearToSend($pim)) {
		return;
	}

	(tied %OUT_QUEUE)->shlock;
	if ($#{$OUT_QUEUE{$pim}} > -1) {
		my $command = @{$OUT_QUEUE{$pim}}[0];
		sendRemote($pim, $sock, $command);
		setClearToSend($pim, FALSE);
	}
	(tied %OUT_QUEUE)->shunlock;
}

sub deQueueCommand {
	my $pim = shift;

	(tied %OUT_QUEUE)->shlock;
	shift @{$OUT_QUEUE{$pim}};
	(tied %OUT_QUEUE)->shunlock;
}	

sub checkIncomingData {
	my $pim = shift;
	my $sock = shift;

	my $response = readUPB($sock);

	if (!defined($response)) {
		logEvent("PIM '$pim': Remote closed connection, exiting!");
		commitSuicide();
	}

	if ($response) {
		foreach my $single (split(/\x0d/, $response)) {
			(tied %IN_QUEUE)->shlock;
			push @{$IN_QUEUE{$pim}}, $single;
			(tied %IN_QUEUE)->shunlock;
		}
	}
}

sub pushCommandQueue {
	my $pim = shift;
	my $command = shift;

	if ($command) {
		(tied %OUT_QUEUE)->shlock;
		push @{$OUT_QUEUE{$pim}}, $command;
		(tied %OUT_QUEUE)->shunlock;
	}
}

sub popResponseQueue {
	my $pim = shift;
	my $response;

	(tied %IN_QUEUE)->shlock;
	if ($#{$IN_QUEUE{$pim}} > -1) {
		$response = shift @{$IN_QUEUE{$pim}};
	}
	(tied %IN_QUEUE)->shunlock;

	return $response;
}

sub sendCommand {
	my $pim = shift;
	my $command = shift;
	my $response;

	pushCommandQueue($pim, $command);

	while (!$response) {
		$response = popResponseQueue($pim);
		sleep 0.5 if (!$response);
	}

	return $response;
}

sub sendUPBCommand {
	my $pim = shift;
	my $command = shift;
	my $prefix = "\x14";

	$command .= getChecksumHex($command);
	$command  = $prefix . $command;

	return sendCommand($pim, $command);
}

sub sendPIMReadCommand {
	my $pim = shift;
	my $command = shift;
	my $prefix = "\x12";
	my $expected_responses = 1;

	$command .= getChecksumHex($command);
	$command  = $prefix . $command;

	return sendCommand($pim, $command);
}

sub sendPIMWriteCommand {
	my $pim = shift;
	my $command = shift;
	my $prefix = "\x17";

	$command .= getChecksumHex($command);
	$command  = $prefix . $command;

	return sendCommand($pim, $command);
}

sub setMessageMode {
	my $pim = shift;
	my $response;

	my $raw = sendCommand($pim, "\x1770028E");
	my $response = parseResponse($pim, $raw);

	if ($response != UPB_ACCEPT) {
		$response = $UPB_CODES[$response];
		logEvent("PIM '$pim': FATAL: Invalid response '$response' received.");
		commitSuicide();
	}
}

sub getDeviceRegisters {
	my $pim = shift;
	my $network = shift;
	my $device = shift;
	my $start = shift;
	my $end = shift;

	my $pims = $$CONFIG{'PIMS'}->{'PIM'};
	my $source = popkey($$pims{$pim}->{'DEVICE'});

	return setCore($pim, $network, $source, $device, RPT_REGISTERS, $start, $end);
}

sub getRegisters {
	my $pim = shift;
	my $start = shift;
	my $end = shift;

	logEvent("PIM '$pim': Getting registers.");

	my $command = sprintf("%02X%02X", $start, $end);

	my $raw = sendPIMReadCommand($pim, $command);
	my $response = parseResponse($pim, $raw);

	if ($response != UPB_REGISTER) {
		$response = $UPB_CODES[$response];
		logEvent("FATAL: PIM '$pim': Invalid register response '$response' received.");
		commitSuicide();
	}
}

sub setRegister {
	my $pim = shift;
	my $register = shift;
	my $value = shift;

	return if !defined($register);

	my $command = sprintf("%02X%02X", $register, $value);

	my $raw = sendPIMWriteCommand($pim, $command);
	my $response = parseResponse($pim, $raw);

	return FALSE if ($response == UPB_ACK);
	return $response;
}

sub setNetworkId {
	my $pim = shift;
	my $networkid = shift;                               

	return undef if (!$networkid);

	my $response = setRegister($pim, 0, $networkid);

	if ($response) {
		$response = $UPB_CODES[$response];
		logEvent("FATAL: PIM '$pim': Failed to set network id, response was '$response'.");
		commitSuicide();
	}
}

sub setDeviceId {
	my $pim = shift;
	my $deviceid = shift;                               

	return undef if (!$deviceid);

	my $result = setRegister($pim, 1, $deviceid);

	if ($result) {
		$result = $UPB_CODES[$result];
		logEvent("FATAL: PIM '$pim': Failed to set device id, response was '$result'.");
		commitSuicide();
	}
}

sub setNetworkPassword {
	my $pim = shift;
	my $password = shift;                               

	return undef if (!$password);

	my $result = setRegister($pim, 2, $password);

	if ($result) {
		$result = $UPB_CODES[$result];
		logEvent("FATAL: PIM '$pim': Failed to set network password, ".
		  "response was '$result'.");
		commitSuicide();
	}
}

sub readUPB {
	my $socket = shift;
	my $buff = '';

	my $select = new IO::Select;
	$select->add($socket);

	while((my @ready = $select->can_read(.1))) {
		foreach my $fh (@ready) {
			next if ($fh != $socket);

			my $_buff;
			my $ret = sysread($socket, $_buff, 4096);

			if (!defined($ret)) {
				logEvent("Received an error while reading remote socket: $!");
				commitSuicide();
			} elsif (!$ret) {
				logEvent("Remote has closed connection.");
				return undef;
			}

			$buff .= $_buff;
		}
	}

	$buff =~ s/\x0d$//;

	if ($_DEBUG_) {
		foreach my $response (split(/\x0d/, $buff)) {
			logEvent("RECEIVED: $response");
		}
	}

	return $buff;
}

sub readRemote {
	my $socket = shift;
	my $buff = '';

	my $select = new IO::Select;
	$select->add($socket);

	while((my @ready = $select->can_read(.1))) {
		foreach my $fh (@ready) {
			next if ($fh != $socket);

			my $_buff;
			$socket->recv($_buff, 4096);

			if (!defined($_buff)) {
				logEvent("Received an error while reading remote socket: $!");
				commitSuicide();
			} elsif (!$_buff) {
				logEvent("Remote has closed connection.");
				return undef;
			}

			$buff .= $_buff;
		}
	}

	return $buff;
}

sub sendRemote {
	my $pim = shift;
	my $sock = shift;
	my $cmd = shift;

	$cmd .= "\x0d";

	print $sock $cmd;

	logEvent("PIM '$pim': SENT: $cmd") if ($_DEBUG_);
}

sub checkDeviceStates {
	logEvent("Checking current device states.");

	my $pims = $$CONFIG{'NETWORKS'}->{'PIM'};

	foreach my $pim (keys %{$pims}) {
		foreach my $network (sort keys %{$$pims{$pim}->{'NETWORK'}}) {
			my $devices = $$pims{$pim}->{'NETWORK'}->{$network}->{'DEVICE'};

			foreach my $device (sort keys %{$devices}) {
 				my $dev_type = popkey($$devices{$device}->{'TYPE'});
 				next if ($dev_type =~ /Virtual/i);
				getDeviceState($pim, $network, $device);
				#getDeviceRegisters($pim, $network, $device, 0x00, 0x10);
			}
		}
	}
}

sub checkStateDifferences {
	my $handle = shift;
	my $current = shift;

	(tied %DEV_STATES)->shlock;

	foreach my $pim (keys %DEV_STATES) {
		foreach my $network (keys %{$DEV_STATES{$pim}}) {
			foreach my $device (keys %{$DEV_STATES{$pim}->{$network}}) {
				my $devices = $$CONFIG{'NETWORKS'}->{'PIM'}->{$pim}->{'NETWORK'}->{$network}->{'DEVICE'};
				my $level = $DEV_STATES{$pim}->{$network}->{$device};
				if (!defined($$current{$pim}->{$network}->{$device}) ||
				    ($$current{$pim}->{$network}->{$device} != $level)) {
 					my $type = popkey($$devices{$device}->{'TYPE'});
 					next if ($type =~ /Virtual/i);
					$$current{$pim}->{$network}->{$device} = $level;
					my $friendly = popkey($$devices{$device}->{'FRIENDLY'});
					my $name = popkey($$devices{$device}->{'NAME'});
					my $dimmable = popkey($$devices{$device}->{'DIMMER'});
					$dimmable = ($dimmable =~ /Yes/i) ? 1 : 0;
					$level = 0 if ($level =~ /Off/i);
					$level = 100 if ($level =~ /On/i);
					print $handle "DEVICE:$dimmable:$name:$friendly:$level\n";
				}
			}
		}
	}

	foreach my $scene (keys %{$$CONFIG{'SCENES'}->{'SCENE'}}) {
		my $scene_state;
		my $found = 0;
		my $found_on = 0;

		foreach my $name (keys %{$$CONFIG{'SCENES'}->{'SCENE'}->{$scene}->{'NAME'}}) {
			my($pim, $network, $device) = findDeviceByName($name);
			$found_on += ($$current{$pim}->{$network}->{$device} > 0);
			$found++;

		}

		if (!$found_on) {
			$scene_state = 'off';
		} elsif ($found != $found_on) {
			$scene_state = 'partial';
		} elsif ($found == $found_on) {
			$scene_state = 'on';
		}

		if ($$current{'scenes'}->{$scene} ne $scene_state) {
			my $friendly = popkey($$CONFIG{'SCENES'}->{'SCENE'}->{$scene}->{'FRIENDLY'});
			print $handle "SCENE:$scene:$friendly:".$scene_state."\n";
			$$current{'scenes'}->{$scene} = $scene_state;
		}
	}

	(tied %DEV_STATES)->shunlock;
}

sub findDevice {
	my $pim = shift;
	my $network = shift;
	my $device = shift;

	my $pims = $$CONFIG{'NETWORKS'}->{'PIM'};
	if (defined($$pims{$pim}->{'NETWORK'}->{$network}->{'DEVICE'}->{$device})) {
		return popkey($$pims{$pim}->{'NETWORK'}->{$network}->{'DEVICE'}->{$device}->{'NAME'});
	}

	return undef;
}

sub findDeviceByName {
	my $name = shift;

	my $pims = $$CONFIG{'NETWORKS'}->{'PIM'};

	foreach my $pim (keys %{$pims}) {
		my $networks = $$pims{$pim}->{'NETWORK'};

		foreach my $network (keys %{$networks}) {
			my $devices = $$networks{$network}->{'DEVICE'};

			foreach my $device (keys %{$devices}) {
				my $_name = popkey($$devices{$device}->{'NAME'});

				if ($_name eq $name) {
					return ($pim, $network, $device);
				}
			}
		}
	}
}

sub checkMonitorInput {
	my $handle = shift;

	my $buff = readRemote($handle);

	if (!defined($buff) && (ref($handle) ne 'GLOB')) {
		my $addr = $handle->peerhost;
		logEvent("Client at $addr disconnected.");
		$handle->close();
		exit;
	}

	return if (!$buff);

	$buff =~ s/\n$//;

	my ($command, $rest) = split(/\s+/, $buff);

	return if (!$command);

	SWITCH: {
		($command =~ /set/i) && do {
			my($name, $set, $argument) =
	 		 split(/:/, $rest, 3);

			my $type = 'DEVICE';
			if ($name =~ /\./) {
				($type, $name) = split(/\./, $name, 2);
			}

			if ($type =~ /DEVICE/i) {
	                        my($pim, $network, $device) = findDeviceByName($name);
				return setDeviceState($pim, $network, $device, $set, $argument);
			} elsif ($type =~ /SCENE/i) {
				return setSceneState($name, $set, $argument);
			}
		};
		($command =~ /state/i) && do {
			my %empty;
			return checkStateDifferences(\*STDOUT, \%empty);
		};
		(($command =~ /exit/i) || ($command =~ /quit/i)) && do {
			if (ref($handle) ne 'GLOB') {
				my $addr = $handle->peerhost;
				logEvent("Client $addr exiting.");
				$handle->close();
			}
			exit;
		};
	}
}

sub checkUPnPInput {
	my $handle = shift;
	my $listener = shift;

	my $buff = readRemote($handle);

	if (!defined($buff)) {
		my $addr = $handle->peerhost;
		logEvent("Client at $addr disconnected.");
		$handle->close();
		exit;
	}

	return if (!$buff);

	$buff =~ s/\n$//;

	logEvent("DEBUG: Received UPnP command: $buff") if ($_DEBUG_);

	SWITCH: {
		(($buff =~ /M-SEARCH/i) && ($buff =~ /$UPNP_VENDOR/)) && do {
			logEvent("Received UPnP search command.");
			sleep .5;

			handleUPnPSearch($handle);
		};
		($buff =~ /GET \/setup.xml HTTP\/1.1/) && do {
			logEvent("Received UPnP setup command.");
			sleep .5;

			handleUPnPSetup($handle, $UPNP_SOCKET_NAME{$listener}->{'NAME'});
		};
		($buff =~ /SOAPACTION\: \"urn\:Belkin\:service\:basicevent\:1\#SetBinaryState\"/) && do {
			logEvent("Received UPnP basic event");
			handleUPnPEvent($handle, $buff, \$UPNP_SOCKET_NAME{$listener});
		};
	}
}

sub handleUPnPSearch {
	my $handle = shift;

	my $host_ip = Net::Address::IP::Local->public;

	my $pims = $$CONFIG{'NETWORKS'}->{'PIM'};

	foreach my $pim (keys %{$pims}) {
		foreach my $network (sort keys %{$$pims{$pim}->{'NETWORK'}}) {
			my $devices = $$pims{$pim}->{'NETWORK'}->{$network}->{'DEVICE'};

			foreach my $device (sort keys %{$devices}) {
				my $name = popkey($$devices{$device}->{'WEMO_NAME'});
				my $upnp_port = popkey($$devices{$device}->{'UPNP_PORT'});
				my $serial = makeSerial($name);
				my $p_uuid = "Socket-1_0-".$serial;
				my $uuid   = uuid_to_string(create_uuid(UUID_V4));
		
				my $message = "HTTP/1.1 200 OK\r\n".
					      "CACHE-CONTROL: max-age=86400\r\n".
				 	      "DATE: ".gmtime()." GMT\r\n".
					      "EXT:\r\n".
					      "LOCATION: http://".$host_ip.":".$upnp_port."/setup.xml\r\n".
					      "OPT: \"http://schemas.upnp.org/upnp/1/0/\"; ns=01\r\n".
					      "01-NLS: ".$uuid."\r\n".
					      "SERVER: Unspecified, UPnP/1.0, Unspecified\r\n".
					      "ST: urn:".$UPNP_VENDOR.":**\r\n".
					      "USN: uuid:".$p_uuid."::urn:".$UPNP_VENDOR.":**\r\n".
					      "X-User-Agent: redsonic\r\n\r\n";

				my $peer_host = $handle->peerhost();
				my $peer_port = $handle->peerport();

				$handle->mcast_send($message, $peer_host.":".$peer_port);

				sleep .2;
			}
		}
	}
}

sub handleUPnPSetup {
	my $handle = shift;
	my $name = shift;;

	my $serial = makeSerial($name);
	my $p_uuid = "Socket-1_0-".$serial;

	my $xml = "<?xml version=\"1.0\"?>\r\n".
		  "<root>\r\n".
		  "  <device>\r\n".
		  "    <deviceType>urn:Mentasm:device:controllee:1</deviceType>\r\n".
		  "    <friendlyName>".$name."</friendlyName>\r\n".
		  "    <manufacturer>Belkin International Inc.</manufacturer>\r\n".
		  "    <modelName>Emulated Socket</modelName>\r\n".
		  "    <modelNumber>3.1415</modelNumber>\r\n".
		  "    <UDN>uuid:".$p_uuid."</UDN>\r\n".
		  "  </device>\r\n".
		  "</root>\r\n";

	my $message = "HTTP/1.1 200 OK\r\n".
		      "CONTENT-LENGTH: ".length($xml)."\r\n".
		      "DATE: ".gmtime()." GMT\r\n".
		      "LAST-MODIFIED: Sat, 01 Jan 2000 00:01:15 GMT\r\n".
		      "SERVER: Unspecified, UPnP/1.0, Unspecified\r\n".
		      "X-User-Agent: redsonic\r\n".
		      "CONNECTION: close\r\n\r\n";

	print $handle $message.$xml;
}

sub handleUPnPEvent {
	my $handle = shift;
	my $buff = shift;
	my $parms = shift;

	if ($buff =~ /\<BinaryState\>1\<\/BinaryState\>/) {
		logEvent("Received UPnP ON event.");
		setDeviceState($$parms->{'PIM'}, $$parms->{'NETWORK'}, $$parms->{'DEVICE'}, 'ON');
	} elsif ($buff =~ /\<BinaryState\>0\<\/BinaryState\>/) {
		logEvent("Received UPnP OFF event.");
		setDeviceState($$parms->{'PIM'}, $$parms->{'NETWORK'}, $$parms->{'DEVICE'}, 'OFF');
	}

	my $soap = "";

	my $message = "HTTP/1.1 200 OK\r\n".
		      "CONTENT-LENGTH: ".length($soap)."\r\n".
		      "CONTENT-TYPE: text/xml charset=\"utf-8\"\r\n".
		      "DATE: ".gmtime()." GMT\r\n".
		      "EXT:\r\n".
		      "SERVER: Unspecified, UPnP/1.0, Unspecified\r\n".
		      "X-User-Agent: redsonic\r\n".
		      "CONNECTION: close\r\n\r\n";

	print $handle $message.$soap;
}

sub getDeviceState {
	my $pim = shift;
	my $network = shift;
	my $device = shift;
	my %data;

	logEvent("PIM '$pim': Getting device state on network $network device $device.")
	  if ($_DEBUG_);

	my $pims = $$CONFIG{'PIMS'}->{'PIM'};
	my $source = popkey($$pims{$pim}->{'DEVICE'});

	my $response = setDevice($pim, $network, $source, $device, DEV_REPORT_STATE);
}

sub storeDeviceState {
	my $pim = shift;
	my $network_id = shift;
	my $device_id = shift;
	my $level = shift;

	logEvent("PIM '$pim': Device $device_id on network $network_id ".
	  "changed level to $level.");

	(tied %DEV_STATES)->shlock;
	$DEV_STATES{$pim}->{$network_id}->{$device_id} = $level;
	(tied %DEV_STATES)->shunlock;
}

sub reportDeviceState {
	my $pim = shift;
	my $network_id = shift;
	my $device_id = shift;

	(tied %DEV_STATES)->shlock;
	my $level = $DEV_STATES{$pim}->{$network_id}->{$device_id};
	(tied %DEV_STATES)->shunlock;

	return $level;
}

sub setClearToSend {
	my $pim = shift;
	my $clear = shift;

	$clear = time() if (!$clear);

	(tied %CTS)->shlock;
	$CTS{$pim} = $clear;
	(tied %CTS)->shunlock;
}

sub isClearToSend {
	my $pim = shift;
	my $clear = shift;

	(tied %CTS)->shlock;
	$clear = $CTS{$pim};
	(tied %CTS)->shunlock;

	return FALSE if ($clear > 1);

	return $clear;
}

sub checkClearToSend {
	my $pim = shift;

	(tied %CTS)->shlock;
	my $clear = $CTS{$pim};

	if ($clear > 1) {
		if (time() > ($clear + 5)) {
			logEvent("Timing out clear to send.");
			$CTS{$pim} = TRUE;
		}
	} 
	(tied %CTS)->shunlock;
}

sub setDeviceState {
	my $pim = shift;
	my $network = shift;
	my $device = shift;
	my $state = shift;
	my $argument = shift;
	my $dimmer_type = TRUE;

	my $devices = $$CONFIG{'NETWORKS'}->{'PIM'}->{$pim}->{'NETWORK'}->{$network}->{'DEVICE'};

	my $dev_type = popkey($$devices{$device}->{'TYPE'});

	if ($dev_type =~ /Virtual/i) {
		my $exec_on = popkey($$devices{$device}->{'EXEC_ON'});
		my $exec_off = popkey($$devices{$device}->{'EXEC_OFF'});
		my $exec;

		SWITCH: {
			($state =~ /ON/i) && do {
				$exec = $exec_on;
			};
			($state =~ /OFF/i) && do {
				$exec = $exec_off;
			};
		}

		my $rc = system($exec);
		logEvent("Run of '$exec' return $rc.");

		return;
	}

	if (popkey($$devices{$device}->{'DIMMER'}) =~ /no|false/i) {
		$dimmer_type = FALSE;
	}

	SWITCH: {
		($state =~ /ON/i) && do {
			$state = DEV_GOTO;
			$argument = 100;
			last SWITCH;
		};
		($state =~ /OFF/i) && do {
			$state = DEV_GOTO;
			$argument = 0;
			last SWITCH;
		};
		($state =~ /TOGGLE/i) && do {
			$state = DEV_GOTO;
			my $current = reportDeviceState($pim, $network, $device);
			if ($current > 0) {
				$argument = 0;
			} else {
				$argument = 100;
			}
			last SWITCH;
		};
		($state =~ /LEVEL/i) && do {
			if (!$dimmer_type) {
				logEvent("WARNING: This device is not set for dimming, ignoring.");
				return;
			}
			$state = DEV_GOTO;
			last SWITCH;
		};
		($state =~ /BLINK/i) && do {
			$state = DEV_BLINK;
			last SWITCH;
		};
	}

	my $pims = $$CONFIG{'PIMS'}->{'PIM'};
	my $source = popkey($$pims{$pim}->{'DEVICE'});

	queueDeviceSet($pim, $network, $source, $device, $state, $argument);
}

sub setSceneState {
	my $scene = shift;
	my $set = shift;
	my $argument = shift;

	if (defined($$CONFIG{'SCENES'}->{'SCENE'}->{$scene})) {
		foreach my $name (keys %{$$CONFIG{'SCENES'}->{'SCENE'}->{$scene}->{'NAME'}}) {
			my($pim, $network, $device) = findDeviceByName($name);
			setDeviceState($pim, $network, $device, $set, $argument);
		}
	}
}

sub retryPending {
	my $pim = shift;
	my $pending = shift;

	return FALSE if (!defined($pending));

	my $network   = $$pending{'network'};
	my $source    = $$pending{'source'};
	my $device    = $$pending{'device'};
	my $command   = $$pending{'command'};
	my $argument1 = $$pending{'argument1'};
	my $argument2 = $$pending{'argument2'};

	logEvent("PIM '$pim': Retrying first pending command $device:$command:$argument1.");

	return setDevice($pim, $network, $source, $device, $command, $argument1, $argument2);
}

sub acknowledgePending {
	my $pim = shift;

	my $pending = popPendingQueue($pim);

	return FALSE if (!defined($pending));

	my $network  = $$pending{'network'};
	my $device   = $$pending{'device'};
	my $command  = $$pending{'command'};
	my $argument = $$pending{'argument1'};

	logEvent("PIM '$pim': Acknowledging first pending command $device:$command:$argument.")
	  if ($_DEBUG_);

	if ($command == DEV_GOTO) {
		storeDeviceState($pim, $network, $device, $argument);
	}

	return FALSE;
}

sub addPendingQueue {
	my $pim = shift;
	my $network = shift;
	my $source = shift;
	my $device = shift;
	my $command = shift;
	my $argument1 = shift;
	my $argument2 = shift;
	my %pending;

	logEvent("PIM '$pim': Adding pending command $command on network $network for device $device.")
	  if ($_DEBUG_);

	$pending{'network'}   = $network;
	$pending{'source'}    = $source;
	$pending{'device'}    = $device;
	$pending{'command'}   = $command;
	$pending{'argument1'} = $argument1;
	$pending{'argument2'} = $argument2;
	$pending{'timestamp'} = time();

	push @{$PENDING_QUEUE{$pim}}, \%pending;
}

sub checkPendingQueue {
	my $pim = shift;

	for (my $x = 0; $x < $#{$PENDING_QUEUE{$pim}}; $x++) {
		my $pending = @{$PENDING_QUEUE{$pim}}[$x];
		if (time() > ($$pending{'timestamp'} + 10)) {
			splice(@{$PENDING_QUEUE{$pim}}, $x, 1);
			retryPending($pim, $pending);
		}
	}
}

sub popPendingQueue {
	my $pim = shift;

	my $pending = shift @{$PENDING_QUEUE{$pim}};

	return $pending;
}

sub checkDeviceSets {
	my $pim = shift;
	my $set;

	(tied %DEV_SETS)->shlock;
	if ($#{$DEV_SETS{$pim}} > -1) {
		$set = shift @{$DEV_SETS{$pim}};
	}
	(tied %DEV_SETS)->shunlock;

	return if (!$set);

	my $network  = $$set{'network'};
	my $source   = $$set{'source'};
	my $device   = $$set{'device'};
	my $state    = $$set{'state'};
	my $argument = $$set{'argument'};

	setDevice($pim, $network, $source, $device, $state, $argument);
}

sub queueDeviceSet {
	my $pim = shift;
	my $network = shift;
	my $source = shift;
	my $device = shift;
	my $state = shift;
	my $argument = shift;
	my %set;

	$set{'network'}  = $network;
	$set{'source'}   = $source;
	$set{'device'}   = $device;
	$set{'state'}    = $state;
	$set{'argument'} = $argument;

	(tied %DEV_SETS)->shlock;
	push @{$DEV_SETS{$pim}}, \%set;
	(tied %DEV_SETS)->shunlock;
}

sub setDevice {
	my $pim = shift;
	my $network_id = shift;
	my $source_id = shift;
	my $device_id = shift;
	my $command = shift;
	my $argument1 = shift;
	my $argument2 = shift;

	return set($pim, $network_id, $source_id, $device_id,
	  MSG_TYPE_DEVICE, $command, $argument1, $argument2);
}

sub setCore {
	my $pim = shift;
	my $network_id = shift;
	my $source_id = shift;
	my $device_id = shift;
	my $command = shift;
	my $argument1 = shift;
	my $argument2 = shift;

	return set($pim, $network_id, $source_id, $device_id,
	  MSG_TYPE_CORE_CMD, $command, $argument1, $argument2);
}

sub set {
	my $pim = shift;
	my $network_id = shift;
	my $source_id = shift;
	my $device_id = shift;
	my $msg_type = shift;
	my $command = shift;
	my $argument1 = shift;
	my $argument2 = shift;
	my %data;

	$data{'sequence'} = 0;
	$data{'count'} = 0;
	$data{'acknowledge'} = ACK_TYPE_ACK_PULSE;
	$data{'repeater'} = REPEATER_NON;
	$data{'link'} = LINK_TYPE_DIRECT;
	$data{'msg_set_id'} = $msg_type;
	$data{'msg_id'} = $command;
	$data{'msg_argument1'} = $argument1;
	$data{'msg_argument2'} = $argument2;
	$data{'network_id'} = $network_id;
	$data{'destination_id'} = $device_id;
	$data{'source_id'} = $source_id;

	my $packet = createUPBPacket(\%data);

	my $raw = sendUPBCommand($pim, $packet);
	my $response = parseResponse($pim, $raw);

	addPendingQueue($pim, $network_id, $source_id, $device_id, $command, $argument1, $argument2);

	return FALSE if ($response == UPB_ACK);
	return $response;
}

sub parseResponse {
	my $pim = shift;
	my $string = shift;
	my $response;

	return undef if (!$string);

	my($pre, $type, $data) = unpack("A1 A1 A*", $string);

	if ($pre eq 'P') {
		if ($type eq 'A') {
			$response = UPB_ACCEPT;
			$data = undef;
			deQueueCommand($pim);
			setClearToSend($pim, TRUE);
		} elsif ($type eq 'B') {
			$response = UPB_BUSY;
			$data = undef;
			logEvent("PIM '$pim': Received BUSY message, sleeping 1 second.");
			sleep 1; # Give it some time..
		} elsif ($type eq 'E') {
			$response = UPB_ERROR;
			$data = undef;
			logEvent("PIM '$pim': Received ERROR message.");
		} elsif ($type eq 'K') {
			$response = UPB_ACK;
			$data = undef;
			acknowledgePending($pim);
		} elsif ($type eq 'N') {
			$response = UPB_NO_ACK;
			$data = undef;
			retryPending($pim, popPendingQueue($pim));
		} elsif ($type eq 'U') {
			$response = UPB_INCOMING;
			parseUPBMessage($pim, $data);
		} elsif ($type eq 'R') {
			$response = UPB_REGISTER;
			$REGISTERS{$pim} = parseRegisters($data);
			deQueueCommand($pim);
			setClearToSend($pim, TRUE);
		}
	}

	return $response;
}

sub parseUPBMessage {
	my $pim = shift;
	my $data = shift;

	my $decoded = decodeUPBPacket($data);

	return if (!defined($decoded));

	if ($$decoded{'msg_set_id'} == MSG_TYPE_CORE_RPT) {
		if ($$decoded{'msg_id'} == RPT_DEVICE_STATE) {
			my $network_id = $$decoded{'network_id'};
			my $device_id = $$decoded{'source_id'};
			my $level = @{$$decoded{'msg_arguments'}}[0];
			storeDeviceState($pim, $network_id, $device_id, $level);
		}
	} elsif ($$decoded{'msg_set_id'} == MSG_TYPE_DEVICE) {
		if ($$decoded{'link'} == LINK_TYPE_DEVICE) {
			my $source_id = $$decoded{'source_id'};
			my $device_id = $$decoded{'destination_id'};
			my $network_id = $$decoded{'network_id'};
			my $command = $$decoded{'msg_id'};
			checkLink($pim, $network_id, $source_id, $device_id, $command);
		}
	}
}

sub checkLink {
	my $pim = shift;
	my $network = shift;
	my $source = shift;
	my $device = shift;
	my $command = shift;

	logEvent(sprintf("PIM '%s': Device link message on network 0x%02x ".
	  "from device 0x%02x to device 0x%02x, command 0x%02x.",
	  $pim, $network, $source, $device, $command));

	my $links = $$CONFIG{'LINKS'}->{'NETWORK'};

	my $from = findDevice($pim, $network, $source);
	my $to = findDevice($pim, $network, $device);

	return if (defined($from) || !defined($to));

	if (defined($$CONFIG{'LINKS'}->{'FROM'}->{$from}->{'TO'}->{$to})) {
		my $actions = $$CONFIG{'LINKS'}->{'FROM'}->{$from}->{'TO'}->{$to};
		if (defined($$actions{'COMMAND'}->{$command}->{'EXEC'})) {
			my $exec = popkey($$actions{'COMMAND'}->{$command}->{'EXEC'});
			my $rc = system($exec);
			logEvent("Run of '$exec' return $rc.");
		}
	}
}

sub parseRegisters {
	my $data = shift;
	my %registers;
	my $pos = 0;
	my @reg_a;

	my $_registers = pack("H*", substr($data, 0, length($data)));
	@reg_a = unpack("C*", $_registers);

	# Return code of the previous register write command
	$registers{'PREV_WRITE'}      = shift @reg_a;

	$registers{'NETWORK_ID'}      = range(\@reg_a, 0, 1);
	$registers{'MODULE_ID'}       = range(\@reg_a, 1, 1);
	$registers{'NETWORK_PASS'}    = range(\@reg_a, 2, 2);
	$registers{'UPB_OPTIONS'}     = range(\@reg_a, 4, 1);
	$registers{'UPB_VERSION'}     = range(\@reg_a, 5, 1);
	$registers{'MANUFACTURER_ID'} = range(\@reg_a, 6, 2);
	$registers{'PRODUCT_ID'}      = range(\@reg_a, 8, 2);
	$registers{'FIRMWARE_VER'}    = range(\@reg_a, 10, 2);
	$registers{'SERIAL_NUMBER'}   = range(\@reg_a, 12, 4);
	$registers{'RESERVED1'}       = range(\@reg_a, 16, 96);
	$registers{'PIM_OPTIONS'}     = range(\@reg_a, 112, 1);
	$registers{'RESERVED2'}       = range(\@reg_a, 113, 136);
	$registers{'SIGNAL_STRENGTH'} = range(\@reg_a, 249, 1);
	$registers{'NOISE_FLOOR'}     = range(\@reg_a, 250, 1);
	$registers{'NOISE_COUNTS'}    = range(\@reg_a, 251, 5);

	return \%registers;
}

sub range {
	my $buf = shift;              
	my $start = shift;
	my $len = shift;
	my $string;

	for (my $i = $start; $i < ($start + $len); $i++) {
		$string .= sprintf("%02x", $$buf[$i]);
	}

	return $string;
}

sub range_array {
	my $buf = shift;              
	my $start = shift;
	my $len = shift;
	my @range;

	for (my $i = $start; $i < ($start + $len); $i++) {
		push @range, $$buf[$i];
	}

	return \@range;
}

sub createUPBPacket {
	my $data = shift;

	my $length = 9;

	my $control_word = $$data{'sequence'} +
			   ($$data{'count'} << 2) +
			   ($$data{'acknowledge'} << 4) +
			   ($length << 8) +
			   ($$data{'repeater'} << 13) +
			   ($$data{'link'} << 15);

	my $message = ($$data{'msg_set_id'} << 5) +
		$$data{'msg_id'};

	my $packet = sprintf("%04x%02x%02x%02x%02x%02x%02x",
		$control_word,
		$$data{'network_id'},
		$$data{'destination_id'},
		$$data{'source_id'},
		$message,
		$$data{'msg_argument1'},
		$$data{'msg_argument2'});

	return $packet;
}

sub decodeUPBPacket {
	my $packet = shift;
	my %data;

	my $packed = pack("H*",substr($packet, 0, length($packet)));
	my @reg_a = unpack("C*", $packed);

	my $control_word = hex(range(\@reg_a, 0, 2));
	$data{'network_id'} = hex(range(\@reg_a, 2, 1));
	$data{'destination_id'} = hex(range(\@reg_a, 3, 1));
	$data{'source_id'} = hex(range(\@reg_a, 4, 1));
	my $message = hex(range(\@reg_a, 5, 1));
	$data{'msg_arguments'} = range_array(\@reg_a, 6, ($#reg_a - 6));
	$data{'checksum'} = hex(range(\@reg_a, $#reg_a, 1));

	# Decode the control word
	$data{'sequence'} = $control_word & 0x03;
	$data{'count'} = ($control_word & 0x0c) >> 0x02;
	$data{'acknowledge'} = ($control_word & 0x70) >> 0x04;
	$data{'length'} = ($control_word & 0x1f00) >> 0x08;
	$data{'repeater'} = ($control_word & 0x6000) >> 0x0d;
	$data{'link'} = ($control_word & 0xc000) >> 0x0e;

	# Decode the payload
	$data{'msg_set_id'} = ($message & 0xe0) >> 0x05;

	if ($data{'msg_set_id'} == MSG_TYPE_EXTENDED) {
		$data{'extended_set_id'} = $message & 0x1f;
	} else {
		$data{'msg_id'} = $message & 0x1f;
	}

	my $seen = FALSE;

	if (($data{'count'} > 0) && ($data{'sequence'} > 0)) {
		$seen = comparePackets(\%data);
		logEvent("Duplicate packet, ignoring.")
		  if ($seen && $_DEBUG_);
	}

	$LAST_PACKET = \%data;

	return undef if ($seen);
	return \%data;
}

sub comparePackets {
	my $packet = shift;

	foreach my $key (keys %{$packet}) {
		next if (($key eq 'sequence') || ($key eq 'checksum'));
		if ($key eq 'msg_arguments') {
			for (my $x = 0; $x <= $#{$$packet{$key}}; $x++) {
				return FALSE if (@{$$LAST_PACKET{$key}}[$x] !=
				  @{$$packet{$key}}[$x]);
			}
		} else {
			return FALSE if ($$LAST_PACKET{$key} != $$packet{$key});
		}
	}

	return TRUE;
}

sub createSocket {
	my $host = shift;
	my $port = shift;
	my $child;

	logEvent("Connecting to $host:$port.");

	my $sock = new IO::Socket::INET (PeerAddr => $host,
					 PeerPort => $port,
					 Proto    => 'tcp');

	if (!$sock) {
		logEvent("Could not create socket: $!");
		commitSuicide();
	}

	fcntl($sock, F_SETFL(), O_NONBLOCK());

	return $sock;
}

sub getChecksumHex {
	my $msg = shift;

	my $bmsg = pack("H*", $msg);
	my @bytes = unpack 'C*', $bmsg;
	my $checksum = 0;

	foreach (@bytes[0..$#bytes]) {
		$checksum += $_;
	}

	$checksum = ~$checksum;
	$checksum++;
	$checksum &= 0xff;
	$checksum = sprintf("%02X",$checksum);

	return $checksum;
}

sub makeSerial {
	my $name = shift;
	my $serial;

	foreach my $letter (split(//, $name)) {
		$serial .= ord($letter);
	}

	return $serial;
}

###############################################################
# Config stuff
###############################################################

sub readConfigFile {
	my $file = shift;
	my $buffer;
	my @stanza;
	my $level;

	my $io = new IO::File $file, O_RDONLY;

	die("Unable to open configuration file '$file': $!\n")
	  if (!$io);

	while (my $line = <$io>) {
		my($test, undef) = split(/\#/, $line, 2);
		$buffer .= $line;
	}

	my @buff_a;
	@buff_a = split(//, $buffer);

	$CONFIG = parseStanza(\@buff_a);

	return FALSE;
}

sub parseStanza {
	my $buffer = shift;
	my $line;
	my %hash;
	my $attribute;
	my $value;
	my $value2;
	my $quoted;

	while ($#{$buffer} > -1) {
		my $char = shift @{$buffer};

		if ($char eq '{') {
			my $child = parseStanza($buffer);

			if ($line) {
				parseLine($line, \%hash, $child);
				$line = undef;
			}

			next;
		}

		return \%hash if ($char eq '}');

		if ($char eq "\n") {
			my %empty;
			parseLine($line, \%hash, \%empty);
			$line = undef;
		} else {
			$line .= $char;
		}
	}

	return \%hash;
}

sub parseLine {
	my $line = shift;
	my $hash = shift;
	my $child = shift;

	($line, undef) = split(/\#/, $line, 2);
	return if ($line =~ /^\s*$/);

	$line =~ s/^\s+//; $line =~ s/\s+$//;

	my @elements;
	while ($line =~ m/"([^"\\]*(\\.[^"\\]*)*)"|([^\s]+)/g) {
		push @elements, defined($1) ? $1:$3;
	}

	my $attribute = @elements[0];
	my $value     = @elements[1];
	my $value2    = @elements[2];

	if (defined($attribute) && defined($value) && defined($value2)) {
		$$hash{$attribute}->{$value}->{$value2} = $child;
	} elsif (defined($attribute) && defined($value)) {
		$$hash{$attribute}->{$value} = $child;
	} elsif (defined($attribute)) {
		$$hash{$attribute} = $child;
	}
}

sub popkey {
	my $hash = shift;

	my @keys = keys %{$hash};

	return pop @keys;
}

##################################################################
# Logging
##################################################################

sub logEvent {
	my $event = shift;
	my $when = localtime();

	print "$when upb.pl($$): $event\n";
}

##################################################################
# Exit routines
##################################################################

sub commitSuicide {
	if (!keys %POLLERS && !$TOPLEVEL) {
		logEvent("Poller exiting!");
		exit;
	} elsif (!keys %CLIENTS && !$TOPLEVEL) {
		logEvent("Client servicer exiting!");
		exit;
	} else {
		kill 'TERM', $UPNP_CHILD if ($UPNP_CHILD);

		foreach my $child (keys %POLLERS) {
			kill 'TERM', $child if ($child);
		}

		foreach my $child (keys %CLIENTS) {
			kill 'TERM', $child if ($child);
		}
	}
}

sub childDied {
	my $child = waitpid(-1, &WNOHANG);

	if (defined($POLLERS{$child})) {
		# Uh oh, can't work without a poller
		(tied %IN_QUEUE)->remove;
		(tied %OUT_QUEUE)->remove;
		(tied %CTS)->remove;
		(tied %DEV_STATES)->remove;
		(tied %DEV_SETS)->remove;

		IPC::Shareable->clean_up_all;

		logEvent("Main exiting!");
		exit;
	}

	if (defined($CLIENTS{$child})) {
		logEvent("Removing client PID $child.");
		delete $CLIENTS{$child};
	}
}

