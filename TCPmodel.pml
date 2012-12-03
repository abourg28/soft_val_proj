int TIMEOUT = 10;
mtype = {SYN, ACK, SYN_ACK, RST, SEND, FIN};
chan toServer = [1] of {mtype};
chan toClient = [1] of {mtype};
int Seq = 0;
int Ack = 0;
int dataAck = 0;
byte data;
byte serverFIN = 0;

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
  if
  :: /* Send packet */
    if
    :: data = 0;
    :: data = 1;
    fi;
    TRANSMIT:
    dataAck = 0;
    toServer!SEND;
    int time = 0;
    do
    :: (dataAck == 1) ->
      /* Data packet was successfully received */
      goto ESTABLISHED_CONNECTION;
    :: (serverFIN == 1) ->
      toClient?FIN;
      printf("CLIENT: Server initiated closing sequence\n");
      /* Server is initiating closing sequence */
      toServer!ACK;
      goto CLOSE_WAIT;
    :: (time > TIMEOUT) ->
      /* Timeout: retransmit */
      printf("CLIENT: RETRANSMITTING\n");
      goto TRANSMIT;
    :: else -> printf("CLIENT: Waiting...\n"); time++; skip;
    od;
  :: /* Close connection */
    toServer!FIN;
    goto FIN_WAIT_1;
  fi;

  /* This should be unreachable code */
  assert(false);

  FIN_WAIT_1:
  printf("CLIENT: FIN WAIT 1\n");
  mtype sig;
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
  if
  :: /* Wait for packets from client */
    mtype sig;
    toServer?sig;
    if
    :: (sig == SEND) ->
      if
      :: /* Simulate lost packet */
        printf("SERVER: Simulating lost packet\n");
        goto ESTABLISHED_CONNECTION;
      :: /* Read packet */
        dataAck = 1;
        printf("SERVER: Received data %d\n", data);
        goto ESTABLISHED_CONNECTION;
      fi;
    :: (sig == FIN) ->
      /* Client wants to close connection */
      toClient!ACK;
      goto CLOSE_WAIT;
    :: else -> assert(false);
    fi;
  :: /* Close connection */
    serverFIN = 1;
    toClient!FIN;
    goto FIN_WAIT_1;
  fi;

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
