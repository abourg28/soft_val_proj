int TIMEOUT = 10;
mtype = {SYN, ACK, SYN_ACK, RST, SEND, FIN, IDLE, TIMEOUT};
chan toServer = [1] of {mtype};
chan toClient = [1] of {mtype};
int Seq = 0;
int Ack = 0;
byte data;

proctype client(int x) {

  CLOSED:
  printf("CLIENT: CLOSED\n");
  if
  :: /* connect */
    Seq = x;
    toServer!SYN;
    goto SYN_SENT;
  :: /* do nothing */
    goto CLOSED;
  fi;

  SYN_SENT:
  printf("CLIENT: SYN SENT\n");
  toClient?SYN_ACK;
  if
  :: (Ack == x + 1) ->
    /* The right Ack was received */
    printf("CLIENT: Received correct SYN\n");
    Ack = Seq + 1;
    Seq = Ack;
    toServer!SYN;
    goto ESTABLISHED_CONNECTION;
  :: else ->
    /* The wrong Ack was received */
    printf("CLIENT: Received incorrect SYN\n");
    goto SYN_RCVD;
  fi;

  SYN_RCVD:
  printf("CLIENT: SYN RECEIVED\n");
  Seq = x;
  toServer!SYN;
  printf("CLIENT: Restarting SYN\n");
  goto SYN_SENT;

  ESTABLISHED_CONNECTION:
  printf("CLIENT: ESTABLISHED CONNECTION\n");
  mtype sig = IDLE;
  do
  ::
    if
    :: (sig == SEND) ->
      /* Server is sending data */
      if
      :: /* Simulate lost packet */
        printf("CLIENT: Simulating lost packet\n");
        toServer!TIMEOUT;
      :: /* Read packet */
        printf("CLIENT: Received data %d\n", data);
        toServer!ACK;
      fi;
    :: (sig == FIN) ->
      /* Server wants to close connection */
      printf("CLIENT: Server initiated closing sequence\n");
      toServer!ACK;
      goto CLOSE_WAIT;
    :: (sig == IDLE) ->
      if
      :: /* Stay idle */
        toServer!IDLE;
      :: /* Start closing sequence */
        printf("CLIENT: Starting closing sequence\n");
        toServer!FIN;
        goto FIN_WAIT_1;
      :: /* Send data */
        if
        :: data = 0;
        :: data = 1;
        fi;
        printf("CLIENT: Sending data %d\n", data);

        TRANSMIT:
        toServer!SEND;
        printf("CLIENT: Waiting...\n");
        toClient?sig;
        if
        :: (sig == ACK) ->
          /* Data packet was successfully received */
          printf("CLIENT: Data ACK was received from server\n");
          toServer!IDLE;
        :: (sig == TIMEOUT) ->
          /* Timeout, must retransmit data */
          printf("CLIENT: Timeout, retransmitting data.\n");
          goto TRANSMIT;
        :: else -> assert(false);
        fi;
      fi;
    :: else -> assert(false);
    fi;
    toClient?sig;
  od;

  /* This should be unreachable code */
  assert(false);

  FIN_WAIT_1:
  printf("CLIENT: FIN WAIT 1\n");
  sig;
  toClient?sig;
  if
  :: (sig == FIN) ->
    /* Both sides have tried to close the connection */
    toServer!ACK;
    goto CLOSING;
  :: (sig == ACK) ->
    /* Server received close request */
    goto  FIN_WAIT_2;
  :: else -> goto FIN_WAIT_1;
  fi;

  CLOSING:
  printf("CLIENT: CLOSING\n");
  toClient?ACK;
  goto TIME_WAIT;

  FIN_WAIT_2:
  printf("CLIENT: FIN WAIT 2\n");
  toClient?FIN;
  toServer!ACK;
  goto TIME_WAIT;

  TIME_WAIT:
  printf("CLIENT: TIME WAIT\n");
  /* Wait for all packets to terminate? */
  toServer!ACK;
  /* Should be goto CLOSED; */
  goto FINISHED;

  CLOSE_WAIT:
  printf("CLIENT: CLOSE WAIT\n");
  toServer!FIN;
  goto LAST_ACK;

  LAST_ACK:
  printf("CLIENT: LAST ACK\n");
  toClient?ACK;
  /* Should be goto CLOSED; */
  goto FINISHED;

  FINISHED:
  printf("CLIENT: FINISHED\n");
}

proctype server(int y) {

  CLOSED:
  printf("SERVER: CLOSED\n");
  if
  :: /* listen */
    toServer?SYN;
    goto LISTEN;
  :: /* do nothing */
    goto CLOSED;
  fi;
LISTEN:
  printf("SERVER: LISTEN\n");
  if
  :: /* Send correct packet */
    printf("SERVER: Sending correct SYN\n");
    Ack = Seq + 1;
    Seq = y;
    toClient!SYN_ACK;
    goto SYN_RCVD;
  :: /* Send incorrect packet */
    printf("SERVER: Sending incorrect SYN\n");
    Ack = Seq + 11;
    Seq = y;
    toClient!SYN_ACK;
    goto SYN_RCVD;
  fi;

  SYN_RCVD:
  printf("SERVER: SYN RECEIVED\n");
  toServer?SYN;
  if
  :: (Ack == y + 1) ->
    goto ESTABLISHED_CONNECTION;
  :: else ->
    /* Client reset */
    printf("SERVER: Client restarted SYN\n");
    goto LISTEN;
  fi;

  ESTABLISHED_CONNECTION:
  printf("SERVER: ESTABLISHED CONNECTION\n");
  mtype sig;
  do
  ::
    toServer?sig;
    if
    :: (sig == SEND) ->
      /* Client is sending data */
      if
      :: /* Simulate lost packet */
        printf("SERVER: Simulating lost packet\n");
        toClient!TIMEOUT;
      :: /* Read packet */
        printf("SERVER: Received data %d\n", data);
        toClient!ACK;
      fi;
    :: (sig == FIN) ->
      /* Client wants to close connection */
      printf("SERVER: Client initiated closing sequence\n");
      toClient!ACK;
      goto CLOSE_WAIT;
    :: (sig == IDLE) ->
      if
      :: /* Stay idle */
        toClient!IDLE;
      :: /* Start closing sequence */
        printf("SERVER: Starting closing sequence\n");
        toClient!FIN;
        goto FIN_WAIT_1;
      :: /* Send data */
        if
        :: data = 0;
        :: data = 1;
        fi;
        printf("SERVER: Sending data %d\n", data);

        TRANSMIT:
        toClient!SEND;
        printf("SERVER: Waiting...\n");
        toServer?sig;
        if
        :: (sig == ACK) ->
          /* Data packet was successfully received */
          printf("SERVER: Data ACK was received from client\n");
          toClient!IDLE;
        :: (sig == TIMEOUT) ->
          /* Timeout, must retransmit data */
          printf("SERVER: Timeout, retransmitting data.\n");
          goto TRANSMIT;
        :: else -> assert(false);
        fi;
      fi;
    :: else -> assert(false);
    fi;
  od;

  /* This should be unreachable code */
  assert(false);

  FIN_WAIT_1:
  printf("SERVER: FIN WAIT 1\n");
  toServer?sig;
  if
  :: (sig == FIN) ->
    /* Both sides have tried to close the connection */
    toClient!ACK;
    goto CLOSING;
  :: (sig == ACK) ->
    /* Server received close request */
    goto  FIN_WAIT_2;
  :: else -> goto FIN_WAIT_1;
  fi;

  CLOSING:
  printf("SERVER: CLOSING\n");
  toServer?ACK;
  goto TIME_WAIT;

  FIN_WAIT_2:
  printf("SERVER: FIN WAIT 2\n");
  toServer?FIN;
  toClient!ACK;
  goto TIME_WAIT;

  TIME_WAIT:
  printf("SERVER: TIME WAIT\n");
  /* Wait for all packets to terminate? */
  toClient!ACK;
  /* Should be goto CLOSED; */
  goto FINISHED;

  CLOSE_WAIT:
  printf("SERVER: CLOSE WAIT\n");
  toClient!FIN;
  goto LAST_ACK;

  LAST_ACK:
  printf("SERVER: LAST ACK\n");
  toServer?ACK;
  /* Should be goto CLOSED; */
  goto FINISHED;

  FINISHED:
  printf("SERVER: FINISHED\n");
}

init {
  run client(23);
  run server(12);
}
