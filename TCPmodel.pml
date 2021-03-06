int TIMEOUT = 10;
mtype = {SYN, ACK, SYN_ACK, RST, SEND, FIN, IDLE, TIMEOUT,
         CLOSED_STATE, LISTEN_STATE, SYN_SENT_STATE, SYN_RCVD_STATE,
         ESTABLISHED_CONNECTION_STATE, FIN_WAIT_1_STATE, FIN_WAIT_2_STATE,
         CLOSING_STATE, TIME_WAIT_STATE, CLOSE_WAIT_STATE, LAST_ACK_STATE};
chan toServer = [1] of {mtype};
chan toClient = [1] of {mtype};
mtype cstate;
mtype sstate;
int Seq = 0;
int Ack = 0;
byte data;

proctype client(int x) {

  CLOSED:
  cstate = CLOSED_STATE;
  printf("CLIENT: CLOSED\n");
  if
  :: /* connect */
    Seq = x;
    toServer!SYN;
    goto SYN_SENT;
  :: /* do nothing */
    goto CLOSED; /* MUTANT_5: Replace goto CLOSED with goto CLOSING*/
  fi;

  SYN_SENT:
  cstate = SYN_SENT_STATE;
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
    goto SYN_RCVD; /* MUTANT_6: Replace goto SYN_RCVD with goto FIN_WAIT_1 */
  fi;

  SYN_RCVD:
  cstate = SYN_RCVD_STATE;
  printf("CLIENT: SYN RECEIVED\n");
  Seq = x;
  toServer!SYN;
  printf("CLIENT: Restarting SYN\n");
  goto SYN_SENT;

  ESTABLISHED_CONNECTION:
  cstate = ESTABLISHED_CONNECTION_STATE;
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
        goto FIN_WAIT_1; /* MUTANT_7: Replace goto FIN_WAIT_1 with goto CLOSED */
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
        :: else -> /* IMM_1 */ assert(false);
        fi;
      fi;
    :: else -> /* IMM_2 */ assert(false);
    fi;
    toClient?sig;
  od;

  /* IMM_3 */
  assert(false);

  FIN_WAIT_1:
  cstate = FIN_WAIT_1_STATE;
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
  :: else -> /* IMM_4 */ assert(false);
  fi;

  CLOSING:
  cstate = CLOSING_STATE;
  printf("CLIENT: CLOSING\n");
  toClient?ACK;
  goto TIME_WAIT;

  FIN_WAIT_2:
  cstate = FIN_WAIT_2_STATE;
  printf("CLIENT: FIN WAIT 2\n");
  toClient?FIN;
  toServer!ACK;
  goto TIME_WAIT;

  TIME_WAIT:
  cstate = TIME_WAIT_STATE;
  printf("CLIENT: TIME WAIT\n");
  /* Wait for all packets to terminate? */
  toServer!ACK;
  goto FINISHED; /* Change to FINISHED if you want the model to stop */

  CLOSE_WAIT:
  cstate = CLOSE_WAIT_STATE;
  printf("CLIENT: CLOSE WAIT\n");
  toServer!FIN;
  goto LAST_ACK;

  LAST_ACK:
  cstate = LAST_ACK_STATE;
  printf("CLIENT: LAST ACK\n");
  toClient?ACK;
  goto CLOSED; /* Change to FINISHED if you want the model to stop */

  FINISHED:
  cstate = CLOSED_STATE;
  printf("CLIENT: FINISHED\n");
}

proctype server(int y) {

  CLOSED:
  sstate = CLOSED_STATE;
  printf("SERVER: CLOSED\n");
  if
  :: /* listen */
    toServer?SYN;
    goto LISTEN;
  :: /* do nothing */
    goto CLOSED;
  fi;

  LISTEN:
  sstate = LISTEN_STATE;
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
  sstate = SYN_RCVD_STATE;
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
  sstate = ESTABLISHED_CONNECTION_STATE;
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
        toClient!TIMEOUT; /* MUTANT_1: Replace with toClient!SYN */
      :: /* Read packet */
        printf("SERVER: Received data %d\n", data);
        toClient!ACK;
      fi;
    :: (sig == FIN) ->
      /* Client wants to close connection */
      printf("SERVER: Client initiated closing sequence\n");
      toClient!ACK; /* MUTANT_3: Replace with toClient!SYN */
      goto CLOSE_WAIT;
    :: (sig == IDLE) ->
      if
      :: /* Stay idle */
        toClient!IDLE;
      :: /* Start closing sequence */
        printf("SERVER: Starting closing sequence\n");
        toClient!FIN;
        goto FIN_WAIT_1; /* MUTANT_10: Replace goto FIN_WAIT_1 with goto FIN_WAIT_2 */
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
        /* MUTANT_4: Uncomment, break; */
        if
        :: (sig == ACK) ->
          /* Data packet was successfully received */
          printf("SERVER: Data ACK was received from client\n");
          toClient!IDLE;
        :: (sig == TIMEOUT) -> /* MUTANT_2: Replace condition with sig == SYN */
          /* Timeout, must retransmit data */
          printf("SERVER: Timeout, retransmitting data.\n");
          goto TRANSMIT;
        :: else -> /* IMM_1 */ assert(false);
        fi;
      fi;
    :: else -> /* IMM_2 */ assert(false);
    fi;
  od;

  /* IMM_3 */
  assert(false);

  FIN_WAIT_1:
  sstate = FIN_WAIT_1_STATE;
  printf("SERVER: FIN WAIT 1\n");
  toServer?sig;
  if
  :: (sig == FIN) ->
    /* Both sides have tried to close the connection */
    toClient!ACK;
    goto CLOSING; /* MUTANT_8: Replace goto CLOSING with goto CLOSED */
  :: (sig == ACK) ->
    /* Server received close request */
    goto  FIN_WAIT_2;
  :: else -> /* IMM_4 */ assert(false);
  fi;

  CLOSING:
  sstate = CLOSING_STATE;
  printf("SERVER: CLOSING\n");
  toServer?ACK;
  goto TIME_WAIT; /* MUTANT_9: Replace goto TIME_WAIT with goto CLOSED */

  FIN_WAIT_2:
  sstate = FIN_WAIT_2_STATE;
  printf("SERVER: FIN WAIT 2\n");
  toServer?FIN;
  toClient!ACK;
  goto TIME_WAIT;

  TIME_WAIT:
  sstate = TIME_WAIT_STATE;
  printf("SERVER: TIME WAIT\n");
  /* Wait for all packets to terminate? */
  toClient!ACK;
  goto CLOSED; /* Change to FINISHED if you want the model to stop */

  CLOSE_WAIT:
  sstate = CLOSE_WAIT_STATE;
  printf("SERVER: CLOSE WAIT\n");
  toClient!FIN;
  goto LAST_ACK;

  LAST_ACK:
  sstate = LAST_ACK_STATE;
  printf("SERVER: LAST ACK\n");
  toServer?ACK;
  goto CLOSED; /* Change to FINISHED if you want the model to stop */

  FINISHED:
  sstate = CLOSED_STATE;
  printf("SERVER: FINISHED\n");
}

init {
  run client(23);
  run server(12);
}
