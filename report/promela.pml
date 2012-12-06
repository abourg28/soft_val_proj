
  #define p (cstate == closed_state)
  #define q (cstate == closed_state || cstate == syn_sent_state)
  never  {    /* ![]<>(p -> xq) */
  t0_init:
    if
    :: ((p)) -> goto accept_s4
    :: (1) -> goto t0_init
    fi;
  accept_s4:
    if
    :: (! ((q)) && (p)) -> goto accept_s4
    fi;
  }
