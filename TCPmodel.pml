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
  assert(Ack == x + 1);
  Ack = Seq + 1;
  Seq = Ack;
  toServer!SYN_ACK;
  goto SYN_RCVD;

  SYN_RCVD:
  printf("CLIENT: SYN RECEIVED\n");

  FINISHED:
  printf("CLIENT: FINISHED\n");
}

proctype server(int y) {

  CLOSED:
  printf("SERVER: CLOSED\n");
  if
  :: /* listen */
    goto LISTEN;
  :: /* do nothing */
    goto CLOSED;
  fi;

  LISTEN:
  printf("SERVER: LISTEN\n");
  toServer?SYN;
  Ack = Seq + 1;
  Seq = y;
  toClient!SYN_ACK;
  goto SYN_RCVD;

  SYN_RCVD:
  printf("SERVER: SYN RECEIVED\n");

  FINISHED:
  printf("SERVER: FINISHED\n");
}

init {
  run client(23);
  run server(12);
}
