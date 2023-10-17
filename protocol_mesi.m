-- Coherence Protocol Lab
-- Protocol Framework

-- See the lines marked TODO in file below.
-- NOTE: this file will not compile until you fill in some minimal
-- additional states and messages.  Try adding support for just a 
-- read request first (comment out other starting rules).

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  -- TODO: start with this number at 1, then increase to 2 and eventually 3
  ProcCount:  2;         -- number processors
  ValueCount: 2;         -- number of data values.
  DomainCount: 2;        -- number of security domains
  VC0: 0;                -- low priority -- requests in the home directory
  VC1: 1;		 -- acks in the home directory, resp in the processors
  VC2: 2;                -- high priority
  VC3: 3;
  VC4: 4;
  NumVCs: VC4 - VC0 + 1;
  QMax: 2;
  NetMax: ProcCount+16;

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount);
  Groups: scalarset(DomainCount);
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: VC0..NumVCs-1;

  -- Message enumeration: you must support the first three, but will need to
  -- add more message types (e.g., various ACKs)
  MessageType: enum {  ReadReq,         -- request for shared state
		                   WriteReq,        -- write request
		                   WBReq,            -- writeback request (w/ or wo/ data)
				   ReadResp,
				   WriteResp,
				   ReadAck,
				   WriteAck,
				   InvReq,
				   EInvReq,
				   EInvDowngradeReq,
				   InvResp,
				   InvRespClean,
				   WBResp,
				   WBAck,
 				   MarkRW,
				   EvictReq,
				   EvictResp,
				   MarkRWRespRetry,
				   MarkRWRespSetRW
                       -- TODO: add more messages here!
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- don't need a destination for verification
      vc: VCType;
      aux: Node;  -- participating node (used when forwarding msgs)
      cnt: 0..ProcCount;
      val: Value;
      isE: boolean;
      isRW: boolean;
    End;

  HomeState:
    Record
      -- home node state: you have three stable states (M,S,I) but need to
      -- add transient states during races
      state: enum { HM, HS, HI, HIM, HIS, HMMA, HMMW, HMW, HMA, HSM, HSMA, HMSA, HMSW, HSW, HSA, HMWW, HSEV, HMEV, HMEVWB, HE, HIE, HEEV, HEEVWB, HESA, HEA, HEMA, HEWE 
  };  -- TODO: add transient states here!
      owner: Node;	
      sharers: multiset [ProcCount] of Node; 
      pending_node: Node;
      pending_owner: Node;
      val: Value;
      IDCP_RW: boolean;
      needsResponse: boolean; --needs to send eviction response
    End;

  ProcState:
    Record
      -- processor state: again, three stable states (M,S,I) but you need to
      -- add transient states to support races
      state: enum { PM, PS, PI, PIS, PIM, PSM, PMI, PE, PMBlocked };
      val: Value;
      IDCP_RW: boolean;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;
  ProcGroups: multiset [DomainCount] of multiset [ProcCount] of ProcState;
  -- maybe the above can be done in a future life --
  msg_processed: boolean;
  rw_bit: boolean;
  LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

-- var --
  HomeNode_D1: HomeState;
  Procs_D1: array [Proc] of ProcState;
  Net_D1:   array [Node] of multiset [NetMax] of Message;
  msg_processed_D1: boolean;
  LastWrite_D1: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware
  LastWriteGlobal: Value;

----------------------------------------------------------------------
-- Procedures for the first domain --
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	             dst:Node;
	             src:Node;
               vc:VCType;
	             aux:Node;
               cnt:0..ProcCount;
               val:Value;
               isE:boolean;
	       isRW:boolean;);
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.aux   := aux;
  msg.cnt   := cnt;
  msg.val   := val;
  msg.isE   := isE;
  msg.isRW  := isRW;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure Send_D1(mtype:MessageType;
	             dst:Node;
	             src:Node;
               vc:VCType;
	             aux:Node;
               cnt:0..ProcCount;
               val:Value;
               isE:boolean;
 	       isRW:boolean;);
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net_D1[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.aux   := aux;
  msg.cnt   := cnt;
  msg.val   := val;
  msg.isE   := isE;
  msg.isRW  := isRW;
  MultiSetAdd(msg, Net_D1[dst]);
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers_D1();
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode_D1.sharers, HomeNode_D1.sharers[i] = n) != 0)
    then
      		Send_D1(InvReq, n, HomeType, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    endif;
  endfor;
End;

Procedure SendEInvReqToSharers_D1();
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode_D1.sharers, HomeNode_D1.sharers[i] = n) != 0)
    then
      		Send_D1(EInvReq, n, HomeType, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    endif;
  endfor;
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  switch msg.mtype
  case WriteReq, ReadReq, WBReq, ReadResp, WriteResp, ReadAck, WriteAck:
    msg_processed := false;  -- we can receive a raw request any time
  else
    error "Unhandled message type!";
  endswitch;
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers();
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      		Send(InvReq, n, HomeType, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    endif;
  endfor;
End;

Procedure SendEInvReqToSharers();
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      		Send(EInvReq, n, HomeType, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    endif;
  endfor;
End;

Procedure SendEInvDowngradeReqToSharers();
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      		Send(EInvDowngradeReq, n, HomeType, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    endif;
  endfor;
End;

Procedure SendReadRespToSharer(val: Value);
var cnt:0..ProcCount;
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
     	Send(ReadResp, n, HomeType, VC0, UNDEFINED, UNDEFINED, val, false, HomeNode.IDCP_RW);
    endif;
  endfor;
End;

Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;
var cnt1:0..ProcCount;
var cnt_D1:0..ProcCount;
var isSharer:boolean;
Begin
  -- compiler barfs if we put this inside the switch
  cnt := MultiSetCount(i:HomeNode.sharers, true);
  isSharer := (MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = msg.src) != 0);
  cnt_D1 := MultiSetCount(i:HomeNode_D1.sharers, true);

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

    if msg.mtype = MarkRW then
      -- check whether the other domain has a cache line that is evictable 
      Assert(HomeNode.IDCP_RW = false);
      switch HomeNode_D1.state
          case HE: 
        	if (cnt_D1 >= 1) then
		   Assert(cnt_D1 = 1);
        	   HomeNode_D1.state := HEEV;
        	   SendEInvReqToSharers_D1();
      	           Send(MarkRWRespRetry, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
        	else
			Assert(cnt_D1 = 0);
        		HomeNode_D1.state := HI;
        		HomeNode_D1.IDCP_RW := false;
      	                Send(MarkRWRespSetRW, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
        		HomeNode.IDCP_RW := true;
        	endif
          case HS:
                HomeNode_D1.state := HSEV;
                SendInvReqToSharers_D1();
      	        Send(MarkRWRespRetry, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
          case HM:
                if (cnt_D1 >= 1) then
                	HomeNode_D1.state := HMEV;
                	SendInvReqToSharers_D1();
      	                Send(MarkRWRespRetry, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
                else
                	HomeNode_D1.state := HI;
			HomeNode.val := HomeNode_D1.val;
                	HomeNode_D1.IDCP_RW := false;
      	                Send(MarkRWRespSetRW, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
                	HomeNode.IDCP_RW := true;
                endif
          case HI:
                Assert(HomeNode.state != HI);
                HomeNode.IDCP_RW := true;
      	        Send(MarkRWRespSetRW, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
          else
            Send(MarkRWRespRetry, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
      endswitch;
  else 
  switch HomeNode.state
  case HI:
    Assert(cnt = 0) "Sharers list non-empty, but line is Invalid";
    Assert(HomeNode.IDCP_RW = false);
    switch msg.mtype
    case ReadReq:
      if (HomeNode_D1.IDCP_RW = false) then
      	HomeNode.state := HIE;
      	AddToSharersList(msg.src);
	--HomeNode.val := HomeNode_D1.val;
      	Send(ReadResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, true, HomeNode.IDCP_RW);
      else
	Assert(HomeNode_D1.state != HI);
        switch HomeNode_D1.state
            case HE: 
          	if (cnt_D1 >= 1) then
          	   Assert(cnt_D1 = 1);
          	   HomeNode_D1.state := HEEV;
          	   SendEInvReqToSharers_D1();
          	else
          		Assert(cnt_D1 = 0);
          		HomeNode_D1.state := HI;
          		HomeNode_D1.IDCP_RW := false;
          	endif
            case HS:
                  HomeNode_D1.state := HSEV;
                  SendInvReqToSharers_D1();
            case HM:
                  if (cnt_D1 >= 1) then
                  	HomeNode_D1.state := HMEV;
                  	SendInvReqToSharers_D1();
                  else
                  	HomeNode_D1.state := HI;
			HomeNode.val := HomeNode_D1.val;
                  	HomeNode_D1.IDCP_RW := false;
                  endif
            else
		msg_processed := false;
        endswitch;
	msg_processed := false;
      endif

    case WriteReq:
      if (HomeNode_D1.state = HI) then
      	HomeNode.state := HIM;
      	AddToSharersList(msg.src);
	--HomeNode.val := HomeNode_D1.val;
      	Send(WriteResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, false, HomeNode.IDCP_RW);
      	HomeNode.pending_owner := msg.src;
      else
	Assert(HomeNode_D1.state != HI);
        switch HomeNode_D1.state
            case HE: 
          	if (cnt_D1 >= 1) then
          	   Assert(cnt_D1 = 1);
          	   HomeNode_D1.state := HEEV;
          	   SendEInvReqToSharers_D1();
          	else
          		Assert(cnt_D1 = 0);
          		HomeNode_D1.state := HI;
          		HomeNode_D1.IDCP_RW := false;
          	endif
            case HS:
                  HomeNode_D1.state := HSEV;
                  SendInvReqToSharers_D1();
            case HM:
                  if (cnt_D1 >= 1) then
                  	HomeNode_D1.state := HMEV;
                  	SendInvReqToSharers_D1();
                  else
                  	HomeNode_D1.state := HI;
			HomeNode.val := HomeNode_D1.val;
                  	HomeNode_D1.IDCP_RW := false;
                  endif
            else
		msg_processed := false;
        endswitch;
        msg_processed := false;
      endif

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HIE:
        switch msg.mtype
        case ReadAck:
      		HomeNode.state := HE;
        else 
      		ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HIS:
        switch msg.mtype
        case ReadAck:
      		HomeNode.state := HS;
        else 
      		ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HIM:
        switch msg.mtype
        case WriteAck:
      		HomeNode.state := HM;
		HomeNode.owner := HomeNode.pending_owner;
		HomeNode.val := msg.val;
        else 
      		ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HE:
    switch msg.mtype
    case ReadReq:
      HomeNode.pending_node := msg.src; 
      if (cnt > 0) then
         Assert(cnt = 1);
         SendEInvDowngradeReqToSharers();
         HomeNode.state := HESA; -- waiting for inv resp, and wb ack and read ack
      else
      	 AddToSharersList(msg.src);
         Send(ReadResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, false, HomeNode.IDCP_RW);
         HomeNode.state := HEA;  -- waiting for only read ack
      endif

    case WriteReq:
      HomeNode.pending_owner := msg.src;
      if (cnt > 0) then
        Assert(cnt = 1);
      	SendEInvReqToSharers();
      	HomeNode.state := HEMA; -- waiting for inv resp, and wb ack and read ack
      else
      	AddToSharersList(msg.src);
        Send(WriteResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, false, HomeNode.IDCP_RW);
        HomeNode.state := HMA; -- waiting only for write ack
      endif

    case WBReq:
      HomeNode.owner := msg.src; -- only know now due to silent write in private cache
      RemoveFromSharersList(msg.src);
      Send(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
      HomeNode.state := HMWW; -- writeback has been accepted, now waiting for a WBAck
      HomeNode.val := msg.val;


    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;


  case HM:
    Assert (IsUndefined(HomeNode.owner) = false)
       "HomeNode has no owner, but line is Modified";

    switch msg.mtype

    case ReadReq:
      if (cnt > 0) then
         SendInvReqToSharers();
         AddToSharersList(msg.src);
         HomeNode.state := HMSA; -- waiting for inv ack, and wb ack too
      else
      	 AddToSharersList(msg.src);
         Send(ReadResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, false, HomeNode.IDCP_RW);
         HomeNode.state := HSA;  -- waiting for read ack
      endif

    case WriteReq:
      HomeNode.pending_owner := msg.src;
      if (cnt > 0) then
      	SendInvReqToSharers();
      	AddToSharersList(msg.src);
      	HomeNode.state := HMMA; -- waiting for inv ack, and wb ack too
      else
      	AddToSharersList(msg.src);
        Send(WriteResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, false, HomeNode.IDCP_RW);
        HomeNode.state := HMA;
      endif

    case WBReq:
      RemoveFromSharersList(msg.src);
      Send(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
      HomeNode.state := HMWW; -- writeback has been accepted, now waiting for a WBAck
      HomeNode.val := msg.val;

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HMWW:
     switch msg.mtype
        case WBAck:
             HomeNode.state := HM;
	     HomeNode.val := msg.val;
        else 
             ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HMMA:
     switch msg.mtype
        case InvResp: 
   	      HomeNode.state := HMMW;
        else 	
      	     ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HEMA:
     switch msg.mtype
        case InvResp: 
   	      HomeNode.state := HMMW;
        case InvRespClean:
      	      RemoveFromSharersList(msg.src);
              Send(WriteResp, HomeNode.pending_owner, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, false, HomeNode.IDCP_RW);
      	      AddToSharersList(HomeNode.pending_owner);
	      HomeNode.state := HMA;
        else 	
      	     ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HMMW:
     switch msg.mtype
        case WBReq:
      	      RemoveFromSharersList(msg.src);
      	      AddToSharersList(HomeNode.pending_owner);
      	      Send(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
   	      HomeNode.state := HMW;
	      HomeNode.val := msg.val;
        else 	
      	     ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HMW:
     switch msg.mtype
        case WBAck:
             Send(WriteResp, HomeNode.pending_owner, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, false, HomeNode.IDCP_RW);
             HomeNode.state := HMA; -- back to HM because we accessed the cache lines accordingly
        else 
             ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HMA:
     switch msg.mtype
        case WriteAck:
        	HomeNode.state := HM;
		HomeNode.owner := HomeNode.pending_owner;
		HomeNode.val := msg.val;
        else
                ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HMSA:
     switch msg.mtype
        case InvResp: 
   	      HomeNode.state := HMSW;
        else 	
      	     ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HESA:
     switch msg.mtype
        case InvResp:
   	      HomeNode.state := HMSW;
              AddToSharersList(HomeNode.pending_node);
        case InvRespClean:
      	      RemoveFromSharersList(msg.src);
              AddToSharersList(HomeNode.pending_node);
   	      SendReadRespToSharer(HomeNode.val);
              AddToSharersList(msg.src);
   	      HomeNode.state := HSA;
        else 	
      	     ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HMSW:
     switch msg.mtype
        case WBReq:
      	      RemoveFromSharersList(msg.src);
      	      Send(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
   	      HomeNode.state := HSW;
	      HomeNode.val := msg.val;
        else 	
      	     ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HSW:
     switch msg.mtype
        case WBAck:
  	     Assert(cnt = 1);
   	     SendReadRespToSharer(HomeNode.val);
             HomeNode.state := HSA; -- back to HM because we accessed the cache lines accordingly
        else 
             ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HSA:
     switch msg.mtype
        case ReadAck:
        	HomeNode.state := HS;
        else
                ErrorUnhandledMsg(msg, HomeType);
     endswitch;

  case HEA:
     switch msg.mtype
        case ReadAck:
        	HomeNode.state := HE;
        else
                ErrorUnhandledMsg(msg, HomeType);
     endswitch;


  case HS:
    Assert(cnt != 0) "sharers list empty, but line is shared";
    switch msg.mtype
    case ReadReq:
      AddToSharersList(msg.src);
      Send(ReadResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, false, HomeNode.IDCP_RW);
      HomeNode.state := HIS;

    case WriteReq:
      HomeNode.pending_owner := msg.src;
      if (cnt >= 1) then
      	SendInvReqToSharers();
      	HomeNode.state := HSM;
      else
      	HomeNode.state := HSMA;
      endif
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HSM:
    switch msg.mtype
    case InvResp:
	RemoveFromSharersList(msg.src);
        if cnt = 1
        then
      		HomeNode.state := HSMA;
      		Send(WriteResp, HomeNode.pending_owner, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode.val, false, HomeNode.IDCP_RW);
	else
		HomeNode.state := HSM;
        endif
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HSMA:
    switch msg.mtype
    case WriteAck:
	Assert(cnt = 0);
	HomeNode.owner := HomeNode.pending_owner;
      	AddToSharersList(msg.src);
       	HomeNode.state := HM;
	HomeNode.val := msg.val; 
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HSEV:
     switch msg.mtype
     case InvResp:
	RemoveFromSharersList(msg.src);
        if cnt = 1
	then
		HomeNode.state := HI;
		HomeNode.IDCP_RW := false;
	else
		HomeNode.state := HSEV;
	endif
      else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HMEV:
     switch msg.mtype
     case InvResp:
	RemoveFromSharersList(msg.src);
        if cnt = 1
	then
		HomeNode.state := HMEVWB;
	else
		HomeNode.state := HMEV;
	endif
      else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HEEV:
     Assert(cnt = 1);
     switch msg.mtype
     case InvResp:
	RemoveFromSharersList(msg.src);
	HomeNode.state := HEEVWB;
      case InvRespClean:
	RemoveFromSharersList(msg.src);
	HomeNode.state := HI;
	HomeNode.IDCP_RW := false;
      else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HMEVWB:
     switch msg.mtype
     case WBReq:
      	Send(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
        HomeNode.val := msg.val;
     case WBAck:
        HomeNode.state := HI;
	HomeNode_D1.val := HomeNode.val;
	HomeNode.IDCP_RW := false;
      else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HEEVWB:
     switch msg.mtype
     case WBReq:
      	Send(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode.IDCP_RW);
        HomeNode.val := msg.val;
     case WBAck:
        HomeNode.state := HI;
	HomeNode_D1.val := HomeNode.val;
	HomeNode.IDCP_RW := false;
      else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  else
    ErrorUnhandledState();
  endswitch;

  endif;
End;

Procedure ProcReceive(msg:Message; p:Proc);
Begin
  -- default to 'processing' message. set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias v:Procs[p].val do
  alias rw:Procs[p].IDCP_RW do

  switch ps
  case PI:
	switch msg.mtype	
		case InvReq:
			ps := PI;
    			Send(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
		case EInvReq, EInvDowngradeReq:
			ps := PI;
    			Send(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
		else
      			ErrorUnhandledMsg(msg, p);
    		endswitch;

  case PIM:
    switch msg.mtype
	case WriteResp:
		ps := PM;
    		Send(WriteAck, msg.src, p, VC1, UNDEFINED, UNDEFINED, v, false, false);
		v := msg.val;
		rw := msg.isRW;
	case InvReq:
		ps := PIM;
		Send(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
        case EInvReq, EInvDowngradeReq:
		ps := PIM;
		Send(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    	else
    	  	ErrorUnhandledMsg(msg, p);
    	endswitch;

  case PM:
    switch msg.mtype
	case InvReq, EInvReq, EInvDowngradeReq:
		Send(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
		Send(WBReq, msg.src, p, VC3, UNDEFINED, UNDEFINED, v, false, false);
		ps := PMI;
    	else
    	  	ErrorUnhandledMsg(msg, p);
    	endswitch;

  case PMI: 
    switch msg.mtype
	case EInvReq,InvReq, EInvDowngradeReq:
		ps := PMI;
		Send(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
	case WBResp:
		ps := PI;
		Send(WBAck, msg.src, p, VC4, UNDEFINED, UNDEFINED, v, false, false);
    	else
    	  	ErrorUnhandledMsg(msg, p);
    	endswitch;


  case PSM:
    switch msg.mtype
	case InvReq:
		ps := PIM;
		Send(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
	case WriteResp:
		ps := PM;
		Send(WriteAck, msg.src, p, VC1, UNDEFINED, UNDEFINED, v, false, false);
		v := msg.val;
		rw := msg.isRW;
    	else
    	  	ErrorUnhandledMsg(msg, p);
    	endswitch;

  case PIS:
    switch msg.mtype
	case ReadResp:
    		Send(ReadAck, msg.src, p, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
		v := msg.val;
		rw := msg.isRW;
		if (msg.isE = true) then 
		    ps := PE;
                else
		    ps := PS;
                endif
	case InvReq:
		ps := PIS;
		Send(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
	case EInvReq, EInvDowngradeReq:
		ps := PIS;
		Send(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    	else
    	  	ErrorUnhandledMsg(msg, p);
    	endswitch;

  case PS:
  switch msg.mtype
  case InvReq:
  	ps := PI;
  	Send(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
  else
  	ErrorUnhandledMsg(msg, p);
  endswitch;

  case PE:
  switch msg.mtype
      case InvReq:
      	ps := PI;
      	Send(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
      case EInvReq:
	ps := PI;
      	Send(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
      case EInvDowngradeReq:
	ps := PS;
      	Send(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
  	else
  	  	ErrorUnhandledMsg(msg, p);
  	endswitch;

  case PMBlocked:
  switch msg.mtype
      case MarkRWRespRetry:
	 Assert(rw = false);
	 ps := PM;
      case MarkRWRespSetRW:
	 Assert(rw = false);
	 rw := true;
	 ps := PM;
      else
	 msg_processed := false;
      endswitch;
  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;

  endalias;
  endalias;
  endalias;
End;

---------------- Procedures for the second domain -------------------
Procedure ErrorUnhandledMsg_D1(msg:Message; n:Node);
Begin
  switch msg.mtype
  case WriteReq, ReadReq, WBReq, ReadResp, WriteResp, ReadAck, WriteAck, EvictReq:
    msg_processed_D1 := false;  -- we can receive a raw request any time
  else
    error "Unhandled message type!";
  endswitch;
End;


Procedure SendEInvDowngradeReqToSharers_D1();
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode_D1.sharers, HomeNode_D1.sharers[i] = n) != 0)
    then
      		Send_D1(EInvDowngradeReq, n, HomeType, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    endif;
  endfor;
End;

Procedure SendReadRespToSharer_D1(val: Value);
var cnt:0..ProcCount;
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode_D1.sharers, HomeNode_D1.sharers[i] = n) != 0)
    then
     	Send_D1(ReadResp, n, HomeType, VC0, UNDEFINED, UNDEFINED, val, false, HomeNode_D1.IDCP_RW);
    endif;
  endfor;
End;

Procedure AddToSharersList_D1(n:Node);
Begin
  if MultiSetCount(i:HomeNode_D1.sharers, HomeNode_D1.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode_D1.sharers);
  endif;
End;

Procedure RemoveFromSharersList_D1(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode_D1.sharers, HomeNode_D1.sharers[i] = n);
End;

Procedure HomeReceive_D1(msg:Message);
var cnt:0..ProcCount;
var cnt1:0..ProcCount;
var cnt_D0:0..ProcCount;
var isSharer:boolean;
Begin
  -- compiler barfs if we put this inside the switch
  cnt := MultiSetCount(i:HomeNode_D1.sharers, true);
  isSharer := (MultiSetCount(i:HomeNode_D1.sharers, HomeNode_D1.sharers[i] = msg.src) != 0);
  cnt_D0 := MultiSetCount(i:HomeNode.sharers, true);

  -- default to 'processing' message.  set to false otherwise
  msg_processed_D1 := true;
  
-------
    if msg.mtype = MarkRW then
      -- check whether the other domain has a cache line that is evictable 
      Assert(HomeNode_D1.IDCP_RW = false);
      switch HomeNode.state
          case HE: 
        	if (cnt_D0 >= 1) then
        	   HomeNode.state := HEEV;
        	   SendEInvReqToSharers();
      	           Send_D1(MarkRWRespRetry, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
        	else
        		HomeNode.state := HI;
        		HomeNode.IDCP_RW := false;
      	                Send_D1(MarkRWRespSetRW, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
        		HomeNode_D1.IDCP_RW := true;
        	endif
          case HS:
        	HomeNode.state := HSEV;
        	SendInvReqToSharers();
      	        Send_D1(MarkRWRespRetry, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
          case HM:
        	if (cnt_D0 >= 1) then
        		HomeNode.state := HMEV;
        		SendInvReqToSharers();
      	                Send_D1(MarkRWRespRetry, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
        	else
        		HomeNode.state := HI;
			HomeNode_D1.val := HomeNode.val;
        		HomeNode.IDCP_RW := false;
      	                Send_D1(MarkRWRespSetRW, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
        		HomeNode_D1.IDCP_RW := true;
        	endif
          case HI:
        	Assert(HomeNode.IDCP_RW = false);
        	Assert(HomeNode_D1.state != HI);
        	HomeNode_D1.IDCP_RW := true;
      	        Send_D1(MarkRWRespSetRW, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
          else
      	        Send_D1(MarkRWRespRetry, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
      endswitch;
  else 
  switch HomeNode_D1.state
  case HI:
    Assert(cnt = 0) "Sharers list non-empty, but line is Invalid";
    switch msg.mtype
    case ReadReq:
      if (HomeNode.IDCP_RW = false ) then
         HomeNode_D1.state := HIE;
         AddToSharersList_D1(msg.src);
	 --HomeNode_D1.val := HomeNode.val;
         Send_D1(ReadResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, true, HomeNode_D1.IDCP_RW);
      else
		Assert(HomeNode.state != HI);
      		switch HomeNode.state
      		    case HE: 
      		  	if (cnt_D0 >= 1) then
      		  	   HomeNode.state := HEEV;
      		  	   SendEInvReqToSharers();
      		  	else
      		  		HomeNode.state := HI;
      		  		HomeNode.IDCP_RW := false;
      		  	endif
      		    case HS:
      		  	HomeNode.state := HSEV;
      		  	SendInvReqToSharers();
      		    case HM:
      		  	if (cnt_D0 >= 1) then
      		  		HomeNode.state := HMEV;
      		  		SendInvReqToSharers();
      		  	else
      		  		HomeNode.state := HI;
				HomeNode_D1.val := HomeNode.val;
      		  		HomeNode.IDCP_RW := false;
      		  	endif
      		    else
			msg_processed := false;	
      		endswitch;
		msg_processed := false;	
      endif
    case WriteReq:
      if (HomeNode.state = HI) then
	Assert(HomeNode.IDCP_RW = false);
      	HomeNode_D1.state := HIM;
      	AddToSharersList_D1(msg.src);
	--HomeNode_D1.val := HomeNode.val;
      	Send_D1(WriteResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, false, HomeNode_D1.IDCP_RW);
      	HomeNode_D1.pending_owner := msg.src;
      else
		Assert(HomeNode.state != HI);
      		switch HomeNode.state
      		    case HE: 
      		  	if (cnt_D0 >= 1) then
      		  	   HomeNode.state := HEEV;
      		  	   SendEInvReqToSharers();
      		  	else
      		  		HomeNode.state := HI;
      		  		HomeNode.IDCP_RW := false;
      		  	endif
      		    case HS:
      		  	HomeNode.state := HSEV;
      		  	SendInvReqToSharers();
      		    case HM:
      		  	if (cnt_D0 >= 1) then
      		  		HomeNode.state := HMEV;
      		  		SendInvReqToSharers();
      		  	else
      		  		HomeNode.state := HI;
				HomeNode_D1.val := HomeNode.val;
      		  		HomeNode.IDCP_RW := false;
      		  	endif
      		    else
			msg_processed := false;	
      		endswitch;
		msg_processed := false;	
      endif
    else
      ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HIE:
        switch msg.mtype
        case ReadAck:
      		HomeNode_D1.state := HE;
        else 
      		ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HIS:
        switch msg.mtype
        case ReadAck:
      		HomeNode_D1.state := HS;
        else 
      		ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HIM:
        switch msg.mtype
        case WriteAck:
      		HomeNode_D1.state := HM;
		HomeNode_D1.owner := HomeNode_D1.pending_owner;
		HomeNode_D1.val := msg.val;
        else 
      		ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HE:
    switch msg.mtype
    case ReadReq:
      HomeNode_D1.pending_node := msg.src; 
      if (cnt > 0) then
         Assert(cnt = 1);
         SendEInvDowngradeReqToSharers_D1();
         HomeNode_D1.state := HESA; -- waiting for inv resp, and wb ack and read ack
      else
      	 AddToSharersList_D1(msg.src);
         Send_D1(ReadResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, false, HomeNode_D1.IDCP_RW );
         HomeNode_D1.state := HEA;  -- waiting for only read ack
      endif

    case WriteReq:
      HomeNode_D1.pending_owner := msg.src;
      if (cnt > 0) then
        Assert(cnt = 1);
      	SendEInvReqToSharers_D1();
      	HomeNode_D1.state := HEMA; -- waiting for inv resp, and wb ack and read ack
      else
      	AddToSharersList_D1(msg.src);
        Send_D1(WriteResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, false, HomeNode_D1.IDCP_RW);
        HomeNode_D1.state := HMA; -- waiting only for write ack
      endif

    case WBReq:
      HomeNode_D1.owner := msg.src; -- only know now due to silent write in private cache
      RemoveFromSharersList_D1(msg.src);
      Send_D1(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
      HomeNode_D1.state := HMWW; -- writeback has been accepted, now waiting for a WBAck
      HomeNode_D1.val := msg.val;

    else
      ErrorUnhandledMsg_D1(msg, HomeType);

    endswitch;

  case HM:
    Assert (IsUndefined(HomeNode_D1.owner) = false)
       "HomeNode_D1 has no owner, but line is Modified";

    switch msg.mtype

    case ReadReq:
      if (cnt > 0) then
         SendInvReqToSharers_D1();
         AddToSharersList_D1(msg.src);
         HomeNode_D1.state := HMSA; -- waiting for inv ack, and wb ack too
      else
      	 AddToSharersList_D1(msg.src);
         Send_D1(ReadResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, false, HomeNode_D1.IDCP_RW);
         HomeNode_D1.state := HSA;  -- waiting for read ack
      endif

    case WriteReq:
      HomeNode_D1.pending_owner := msg.src;
      if (cnt > 0) then
      	SendInvReqToSharers_D1();
      	AddToSharersList_D1(msg.src);
      	HomeNode_D1.state := HMMA; -- waiting for inv ack, and wb ack too
      else
      	AddToSharersList_D1(msg.src);
        Send_D1(WriteResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, false, HomeNode_D1.IDCP_RW);
        HomeNode_D1.state := HMA;
      endif

    case WBReq:
      RemoveFromSharersList_D1(msg.src);
      Send_D1(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
      HomeNode_D1.state := HMWW; -- writeback has been accepted, now waiting for a WBAck
      HomeNode_D1.val := msg.val;

    else
      ErrorUnhandledMsg_D1(msg, HomeType);

    endswitch;

  case HMWW:
     switch msg.mtype
        case WBAck:
             HomeNode_D1.state := HM;
	     HomeNode_D1.val := msg.val;
        else 
             ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HMMA:
     switch msg.mtype
        case InvResp: 
   	      HomeNode_D1.state := HMMW;
        else 	
      	     ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HEMA:
     switch msg.mtype
        case InvResp: 
   	      HomeNode_D1.state := HMMW;
        case InvRespClean:
      	      RemoveFromSharersList_D1(msg.src);
              Send_D1(WriteResp, HomeNode_D1.pending_owner, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, false, HomeNode_D1.IDCP_RW);
      	      AddToSharersList_D1(HomeNode_D1.pending_owner);
	      HomeNode_D1.state := HMA;
        else 	
      	     ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HMMW:
     switch msg.mtype
        case WBReq:
      	      RemoveFromSharersList_D1(msg.src);
      	      AddToSharersList_D1(HomeNode_D1.pending_owner);
      	      Send_D1(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
   	      HomeNode_D1.state := HMW;
	      HomeNode_D1.val := msg.val;
        else 	
      	     ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HMW:
     switch msg.mtype
        case WBAck:
             Send_D1(WriteResp, HomeNode_D1.pending_owner, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, false, HomeNode_D1.IDCP_RW);
             HomeNode_D1.state := HMA; -- back to HM because we accessed the cache lines accordingly
        else 
             ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HMA:
     switch msg.mtype
        case WriteAck:
        	HomeNode_D1.state := HM;
		HomeNode_D1.owner := HomeNode_D1.pending_owner;
		HomeNode_D1.val := msg.val;
        else
                ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HMSA:
     switch msg.mtype
        case InvResp: 
   	      HomeNode_D1.state := HMSW;
        else 	
      	     ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HESA:
     switch msg.mtype
        case InvResp:
   	      HomeNode_D1.state := HMSW;
              AddToSharersList_D1(HomeNode_D1.pending_node);
        case InvRespClean:
      	      RemoveFromSharersList_D1(msg.src);
              AddToSharersList_D1(HomeNode_D1.pending_node);
   	      SendReadRespToSharer_D1(HomeNode_D1.val);
              AddToSharersList_D1(msg.src);
   	      HomeNode_D1.state := HSA;
        else 	
      	     ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HMSW:
     switch msg.mtype
        case WBReq:
      	      RemoveFromSharersList_D1(msg.src);
      	      Send_D1(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
   	      HomeNode_D1.state := HSW;
	      HomeNode_D1.val := msg.val;
        else 	
      	     ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HSW:
     switch msg.mtype
        case WBAck:
  	     Assert(cnt = 1);
   	     SendReadRespToSharer_D1(HomeNode_D1.val);
             HomeNode_D1.state := HSA; -- back to HM because we accessed the cache lines accordingly
        else 
             ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HSA:
     switch msg.mtype
        case ReadAck:
        	HomeNode_D1.state := HS;
        else
                ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;

  case HEA:
     switch msg.mtype
        case ReadAck:
        	HomeNode_D1.state := HE;
        else
                ErrorUnhandledMsg_D1(msg, HomeType);
     endswitch;


  case HS:
    Assert(cnt != 0) "sharers list empty, but line is shared";
    switch msg.mtype
    case ReadReq:
      AddToSharersList_D1(msg.src);
      Send_D1(ReadResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, false, HomeNode_D1.IDCP_RW);
      HomeNode_D1.state := HIS;

    case WriteReq:
      HomeNode_D1.pending_owner := msg.src;
      if (cnt >= 1) then
      	SendInvReqToSharers_D1();
      	HomeNode_D1.state := HSM;
      else
      	HomeNode_D1.state := HSMA;
      endif
    else
      ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HSM:
    switch msg.mtype
    case InvResp:
	RemoveFromSharersList_D1(msg.src);
        if cnt = 1
        then
      		HomeNode_D1.state := HSMA;
      		Send_D1(WriteResp, HomeNode_D1.pending_owner, HomeType, VC0, UNDEFINED, UNDEFINED, HomeNode_D1.val, false, HomeNode_D1.IDCP_RW);
	else
		HomeNode_D1.state := HSM;
        endif
    else
      ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HSMA:
    switch msg.mtype
    case WriteAck:
	Assert(cnt = 0);
	HomeNode_D1.owner := HomeNode_D1.pending_owner;
      	AddToSharersList_D1(msg.src);
       	HomeNode_D1.state := HM;
	HomeNode_D1.val := msg.val; 
    else
      ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HSEV:
     switch msg.mtype
     case InvResp:
	RemoveFromSharersList_D1(msg.src);
        if cnt = 1
	then
		HomeNode_D1.state := HI;
		HomeNode_D1.IDCP_RW := false;
	else
		HomeNode_D1.state := HSEV;
	endif
      else 
      ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HMEV:
     switch msg.mtype
     case InvResp:
	RemoveFromSharersList_D1(msg.src);
        if cnt = 1
	then
		HomeNode_D1.state := HMEVWB;
	else
		HomeNode_D1.state := HMEV;
	endif
      else 
      ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HEEV:
     Assert(cnt = 1);
     switch msg.mtype
     case InvResp:
	RemoveFromSharersList_D1(msg.src);
	HomeNode_D1.state := HEEVWB;
      case InvRespClean:
	RemoveFromSharersList_D1(msg.src);
	HomeNode_D1.state := HI;
	HomeNode_D1.IDCP_RW := false;
      else 
      ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HMEVWB:
     switch msg.mtype
     case WBReq:
      	Send_D1(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
        HomeNode_D1.val := msg.val;
     case WBAck:
        HomeNode_D1.state := HI;
	HomeNode.val := HomeNode_D1.val;
	HomeNode_D1.IDCP_RW := false;
      else 
      ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;

  case HEEVWB:
     switch msg.mtype
     case WBReq:
      	Send_D1(WBResp, msg.src, HomeType, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, HomeNode_D1.IDCP_RW);
        HomeNode_D1.val := msg.val;
     case WBAck:
        HomeNode_D1.state := HI;
	HomeNode.val := HomeNode_D1.val;
	HomeNode_D1.IDCP_RW := false;
      else 
      ErrorUnhandledMsg_D1(msg, HomeType);
    endswitch;
  else
    ErrorUnhandledState();
  endswitch;
endif;
End;

Procedure ProcReceive_D1(msg:Message; p:Proc);
Begin
  -- default to 'processing' message. set to false otherwise
  msg_processed_D1 := true;

  alias ps:Procs_D1[p].state do
  alias v:Procs_D1[p].val do
  alias rw:Procs_D1[p].IDCP_RW do

  switch ps
  case PI:
	switch msg.mtype	
		case InvReq:
			ps := PI;
    			Send_D1(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false );
		case EInvReq, EInvDowngradeReq:
			ps := PI;
    			Send_D1(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
		else
      			ErrorUnhandledMsg_D1(msg, p);
    		endswitch;

  case PIM:
    switch msg.mtype
	case WriteResp:
		ps := PM;
    		Send_D1(WriteAck, msg.src, p, VC1, UNDEFINED, UNDEFINED, v, false, false);
		v := msg.val;
		rw := msg.isRW;
	case InvReq:
		ps := PIM;
		Send_D1(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
        case EInvReq, EInvDowngradeReq:
		ps := PIM;
		Send_D1(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    	else
    	  	ErrorUnhandledMsg_D1(msg, p);
    	endswitch;

  case PM:
    switch msg.mtype
	case InvReq, EInvReq, EInvDowngradeReq:
		Send_D1(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
		Send_D1(WBReq, msg.src, p, VC3, UNDEFINED, UNDEFINED, v, false, false);
		ps := PMI;
    	else
    	  	ErrorUnhandledMsg_D1(msg, p);
    	endswitch;

  case PMI: 
    switch msg.mtype
	case EInvReq,InvReq,EInvDowngradeReq:
		ps := PMI;
		Send_D1(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
	case WBResp:
		ps := PI;
		Send_D1(WBAck, msg.src, p, VC4, UNDEFINED, UNDEFINED, v, false, false);
    	else
    	  	ErrorUnhandledMsg_D1(msg, p);
    	endswitch;


  case PSM:
    switch msg.mtype
	case InvReq:
		ps := PIM;
		Send_D1(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
	case WriteResp:
		ps := PM;
		Send_D1(WriteAck, msg.src, p, VC1, UNDEFINED, UNDEFINED, v, false, false);
		v := msg.val;
		rw := msg.isRW;
    	else
    	  	ErrorUnhandledMsg_D1(msg, p);
    	endswitch;

  case PIS:
    switch msg.mtype
	case ReadResp: 
    		Send_D1(ReadAck, msg.src, p, VC1, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
		v := msg.val;
		rw := msg.isRW;
		if (msg.isE = true) then 
		    ps := PE;
                else
		    ps := PS;
                endif
	case InvReq:
		ps := PIS;
		Send_D1(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
	case EInvReq, EInvDowngradeReq:
		ps := PIS;
		Send_D1(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    	else
    	  	ErrorUnhandledMsg_D1(msg, p);
    	endswitch;

  case PS:
  switch msg.mtype
  case InvReq:
  	ps := PI;
  	Send_D1(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
  else
  	ErrorUnhandledMsg_D1(msg, p);
  endswitch;

  case PE:
  switch msg.mtype
      case InvReq:
      	ps := PI;
      	Send_D1(InvResp, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
      case EInvReq:
	ps := PI;
      	Send_D1(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
      case EInvDowngradeReq:
	ps := PS;
      	Send_D1(InvRespClean, msg.src, p, VC2, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
  	else
  	  	ErrorUnhandledMsg_D1(msg, p);
  	endswitch;

  case PMBlocked:
  switch msg.mtype
      case MarkRWRespRetry:
	 Assert(rw = false);
	 ps := PM;
      case MarkRWRespSetRW:
	 Assert(rw = false);
	 rw := true;
	 ps := PM;
      else
	 msg_processed_D1 := false;
      endswitch;

  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;
  endalias;
  endalias;
  endalias;
End;
---------------- End of procedures for the second domain ------------


----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)
ruleset n:Proc Do
  alias p:Procs[n] Do

  rule "read request"
    p.state = PI 
  ==>
    Send(ReadReq, HomeType, n, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    p.state := PIS;
  endrule;

  rule "write request"
    (p.state = PI)
  ==>
    Send(WriteReq, HomeType, n, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    p.state := PIM;
  endrule;

  rule "upgrade request S"
    (p.state = PS)
  ==>
    Send(WriteReq, HomeType, n, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    p.state := PSM;
  endrule;

  rule "upgrade request E"
    (p.state = PE)
  ==>
    p.state := PM; -- silent upgrade
  endrule;

  rule "writeback"
    (p.state = PM)
  ==>
    Send(WBReq, HomeType, n, VC3, UNDEFINED, UNDEFINED, p.val, false, false);
    p.state := PMI;
  endrule;

  rule "evict S"
    (p.state = PS)
  ==>
     p.state := PI;
  endrule;

  rule "evict E"
    (p.state = PE)
  ==>
     p.state := PI;
  endrule;

  endalias;
endruleset;

-- Eviction Rules --
rule "evict the HS LLC cache line"
  (HomeNode.state = HS)
==>
  HomeNode.state := HSEV;
  SendInvReqToSharers();
endrule;

rule "evict the HM LLC cache line"
  (HomeNode.state = HM)
==>
  if (MultiSetCount(i:HomeNode.sharers, true) >= 1) then
  	HomeNode.state := HMEV;
  	SendInvReqToSharers();
  else
  	HomeNode.state := HI;
	HomeNode.IDCP_RW := false;
	HomeNode_D1.val := HomeNode.val;
  endif
endrule;

rule "evict the HE LLC cache line"
  (HomeNode.state = HE)
==>
  if (MultiSetCount(i:HomeNode.sharers, true) >= 1) then
     HomeNode.state := HEEV;
     SendEInvReqToSharers();
  else
  	HomeNode.state := HI;
	HomeNode.IDCP_RW := false;
  endif
endrule;

-- writing rules --
ruleset n:Proc Do
  alias p:Procs[n] Do
	ruleset v:Value Do
  	rule "store new value"
   	 ( p.state = PM & (p.IDCP_RW = true) )
    	==>
 		   p.val := v;      
 		   LastWrite := v;  -- We use LastWrite to sanity check that reads receive the value of the last write
		   LastWriteGlobal := v;
  	endrule;
	endruleset;
  endalias;
endruleset;

ruleset n:Proc Do
  alias p:Procs[n] Do
	ruleset v:Value Do
  	rule "change the IDCP permissions to IDCP-RW"
   	 (p.state = PM & (p.IDCP_RW = false))
    	==>
    		Send(MarkRW, HomeType, n, VC3, UNDEFINED, UNDEFINED, p.val, false, false);
		p.state := PMBlocked;
		-- this eviction will remove the cache lines of the other domain
  	endrule;
	endruleset;
  endalias;
endruleset;

ruleset n:Proc Do
  alias p:Procs_D1[n] Do
	ruleset v:Value Do
  	rule "change the IDCP permissions to IDCP-RW, for D1"
   	 (p.state = PM & (p.IDCP_RW = false))
    	==>
    		Send_D1(MarkRW, HomeType, n, VC3, UNDEFINED, UNDEFINED, p.val, false, false);
		p.state := PMBlocked;
		-- this eviction will remove the cache lines of the other domain
  	endrule;
	endruleset;
  endalias;
endruleset;


-- receive rules --
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do

    rule "receive"
      (msg.vc = VC4) |
      (msg.vc = VC3) |
      (msg.vc = VC2) |
      (msg.vc = VC1) |
      (msg.vc = VC0)
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(msg);

	      if msg_processed
	      then
	        MultiSetRemove(midx, chan);
	      endif;
      else
        ProcReceive(msg, n);

	      if msg_processed
	      then
	        MultiSetRemove(midx, chan);
	      endif;
	  
      endif;

    endrule;
  
    endalias;
    endalias;
  endchoose;  
endruleset;

----------- Rules for the other domain -------------
-- Processor actions (affecting coherency) --
ruleset n:Proc Do
  alias p:Procs_D1[n] Do

  rule "read request"
    p.state = PI 
  ==>
    Send_D1(ReadReq, HomeType, n, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    p.state := PIS;
  endrule;

  rule "write request"
    (p.state = PI)
  ==>
    Send_D1(WriteReq, HomeType, n, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    p.state := PIM;
  endrule;

  rule "upgrade request S"
    (p.state = PS)
  ==>
    Send_D1(WriteReq, HomeType, n, VC0, UNDEFINED, UNDEFINED, UNDEFINED, false, false);
    p.state := PSM;
  endrule;

  rule "upgrade request E"
    (p.state = PE)
  ==>
    p.state := PM; -- silent upgrade
  endrule;

  rule "writeback"
    (p.state = PM)
  ==>
    Send_D1(WBReq, HomeType, n, VC3, UNDEFINED, UNDEFINED, p.val, false, false);
    p.state := PMI;
  endrule;

  rule "evict S"
    (p.state = PS)
  ==>
     p.state := PI;
  endrule;

  rule "evict E"
    (p.state = PE)
  ==>
     p.state := PI;
  endrule;

  endalias;
endruleset;

-- Eviction Rules --
rule "evict the HS LLC cache line"
  (HomeNode_D1.state = HS)
==>
  HomeNode_D1.state := HSEV;
  SendInvReqToSharers_D1();
endrule;

rule "evict the HM LLC cache line"
  (HomeNode_D1.state = HM)
==>
  if (MultiSetCount(i:HomeNode_D1.sharers, true) >= 1) then
  	HomeNode_D1.state := HMEV;
  	SendInvReqToSharers_D1();
  else
  	HomeNode_D1.state := HI;
	HomeNode_D1.IDCP_RW := false;
	HomeNode.val := HomeNode_D1.val;
  endif
endrule;

rule "evict the HE LLC cache line"
  (HomeNode_D1.state = HE)
==>
  if (MultiSetCount(i:HomeNode_D1.sharers, true) >= 1) then
     HomeNode_D1.state := HEEV;
     SendEInvReqToSharers_D1();
  else
  	HomeNode_D1.state := HI;
	HomeNode_D1.IDCP_RW := false;
  endif
endrule;

-- writing rules --
ruleset n:Proc Do
  alias p:Procs_D1[n] Do
	ruleset v:Value Do
  	rule "store new value"
   	 ( (p.state = PM) & (p.IDCP_RW = true) )
    	==>
 		   p.val := v;      
 		   LastWrite_D1 := v;  -- We use LastWrite to sanity check that reads receive the value of the last write
		   LastWriteGlobal := v;
  	endrule;
	endruleset;
  endalias;
endruleset;

-- receive rules --
ruleset n:Node do
  choose midx:Net_D1[n] do
    alias chan:Net_D1[n] do
    alias msg:chan[midx] do

    rule "receive"
      (msg.vc = VC4) |
      (msg.vc = VC3) |
      (msg.vc = VC2) |
      (msg.vc = VC1) |
      (msg.vc = VC0)
    ==>
      if IsMember(n, Home)
      then
        HomeReceive_D1(msg);

	      if msg_processed_D1
	      then
	        MultiSetRemove(midx, chan);
	      endif;
      else
        ProcReceive_D1(msg, n);

	      if msg_processed_D1
	      then
	        MultiSetRemove(midx, chan);
	      endif;
      endif;
    endrule;
    endalias;
    endalias;
  endchoose;  
endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate
  -- home node initialization
  HomeNode.state := HI;
  undefine HomeNode.sharers;
  undefine HomeNode.owner;
  undefine HomeNode.pending_node;
  undefine HomeNode.pending_owner;

  For v:Value do
  	-- home node initialization
  	--HomeNode.val := v;
        HomeNode.IDCP_RW := false;
	HomeNode.needsResponse := false;
  endfor;
  --LastWrite := HomeNode.val;
  --LastWriteGlobal := HomeNode_D1.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := PI;
    Procs[i].IDCP_RW := false;
  endfor;

  -- network initialization
  undefine Net;

  ---------------------------
  ---------------------------
  ---------------------------
  ---------------------------
  -- home node initialization
  HomeNode_D1.state := HI;
  undefine HomeNode_D1.sharers;
  undefine HomeNode_D1.owner;
  undefine HomeNode_D1.pending_node;
  undefine HomeNode_D1.pending_owner;

  For v:Value do
  	-- home node initialization
  	HomeNode.val := v;
  	HomeNode_D1.val := v;
        HomeNode_D1.IDCP_RW := false;
	HomeNode_D1.needsResponse := false;
  endfor;
  LastWrite_D1 := HomeNode_D1.val;
  LastWriteGlobal := HomeNode_D1.val;
  LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs_D1[i].state := PI;
    Procs_D1[i].IDCP_RW := false;
  endfor;

  -- network initialization
  undefine Net_D1;


endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

--invariant "modified w/ empty sharers list"
--  HomeNode.state = HM
--    ->
--      MultiSetCount(i:HomeNode.sharers, true) = 0

invariant "The SWMR invariant"
    Forall n : Proc Do	
    Forall m : Proc Do
      Procs[n].state = PM
      ->
      ((Procs[m].state != PM) & (Procs[m].state != PE) & (Procs[m].state != PS) ) | m=n
    end
    end;

--invariant "Data Invariance"
--    Forall n : Proc Do
--    Forall m : Proc Do
--      Procs[n].state = PM | Procs[n].state = PE | Procs[n].state = PS
--      ->
--      (Procs[n].val = LastWrite)
--    end
--    end;

-------------------------------------
-- Invariants for the other domain --
-------------------------------------

invariant "The SWMR invariant for D1"
    Forall n : Proc Do	
    Forall m : Proc Do
      Procs_D1[n].state = PM
      ->
      ((Procs_D1[m].state != PM) & (Procs_D1[m].state != PE) & (Procs_D1[m].state != PS) ) | m=n
    end
    end;

invariant "Data Invariance for D1"
    Forall n : Proc Do
    Forall m : Proc Do
      Procs_D1[n].state = PM | Procs_D1[n].state = PE | Procs_D1[n].state = PS
      ->
      (Procs_D1[n].val = LastWriteGlobal)
    end
    end;

----------------------------
--- SWMR invariants mixed --
----------------------------
invariant "The SWMR invariant for D1 - 1"
    Forall n : Proc Do	
    Forall m : Proc Do
      Procs_D1[n].state = PM & Procs_D1[n].IDCP_RW = true
      ->
      ((Procs[m].state != PM) & (Procs[m].state != PE) & (Procs[m].state != PS) )
    end
    end;

invariant "The SWMR invariant for D1 - 2"
    Forall n : Proc Do	
    Forall m : Proc Do
      Procs[n].state = PM & Procs[n].IDCP_RW = true
      ->
      ((Procs_D1[m].state != PM) & (Procs_D1[m].state != PE) & (Procs_D1[m].state != PS) )
    end
    end;
