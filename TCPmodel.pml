mtype = {SYN, ACK, SYN_ACK, RST, FIN};
chan toServer = [1] of {mtype};
chan toClient = [1] of {mtype};
int Seq = 0;
int Ack = 0;

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
  printf("CLIENT: SYN_SENT\n");
  toClient?SYN_ACK;
  if
  :: (Ack == x + 1) ->
    /* The right Ack was received */
    printf("CLIENT: Received correct packet\n");
    Ack = Seq + 1;
    Seq = Ack;
    toServer!SYN;
    goto ESTABLISHED_CONNECTION;
  :: else ->
    /* The wrong Ack was received */
    printf("CLIENT: Received incorrect packet\n");
    goto SYN_RCVD;
  fi;

  SYN_RCVD:
  printf("CLIENT: SYN RECEIVED\n");
  Seq = x;
  toServer!SYN;
  goto SYN_SENT;

  ESTABLISHED_CONNECTION:
  printf("CLIENT: ESTABLISHED CONNECTION\n");

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
    printf("SERVER: Sending correct packet\n");
    Ack = Seq + 1;
    Seq = y;
    toClient!SYN_ACK;
    goto SYN_RCVD;
  :: /* Send incorrect packet */
    printf("SERVER: Sending incorrect packet\n");
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
    goto CONNECTION_ESTABLISHED;
  :: else ->
    /* Client reset */
    goto LISTEN;
  fi;

  CONNECTION_ESTABLISHED:
  printf("SERVER: CONNECTION ESTABLISHED\n");

  FINISHED:
  printf("SERVER: FINISHED\n");
}

init {
  run client(23);
  run server(12);
}
