(*START ------------------------------------------------------------------------- *)
app load ["stringTheory","wordsTheory", "llistTheory"(* , "preamble" *)];

open arithmeticTheory listTheory stringTheory wordsTheory HolKernel boolLib Parse bossLib optionTheory llistTheory;

open sc1TypesTheory

val _ = new_theory "chain";

(* model *)

Type State = “:SCvalue optionErr”;

Datatype:
    Address = Contract_address num | Client_address num
End

Definition take_address_def:
  take_address (Contract_address n) = n ∧
  take_address (Client_address n) = n
End

Definition address_is_contract_def:
  address_is_contract (Contract_address num) = T ∧
  address_is_contract (Client_address num) = F
End

(* информация о блокчейне для контракта *)
Datatype:
  Chain = <| chainHeight : num; blockNum : num|>
End

Definition get_chainHeight_def:
  get_chainHeight = Chain_chainHeight
End

Definition get_blockNum_def:
  get_blockNum = Chain_blockNum
End

Definition ChainEquiv_def:
    ChainEquiv c1 c2 = ((get_chainHeight c1 = get_chainHeight c2) ∧
    (get_blockNum c1 = get_blockNum c2))
End

(* информация о запросе, который привел к исполнению контракта *)
Datatype :
  ContractCallContext = <| msgSender : Address; ctxContractAddress : Address|>
End

Definition get_msgSender_def:
  get_msgSender = ContractCallContext_msgSender
End

Definition get_ctxContractAddress_def:
  get_ctxContractAddress = ContractCallContext_ctxContractAddress
End

Datatype :
  Data = <|functionSignature: num; params: SCvalue list |>
End

Definition get_functionSignature_def:
  get_functionSignature = Data_functionSignature
End

Definition get_params_def:
  get_params = Data_params
End

Datatype :
  Setup = <|code: word8 list; setupParams: SCvalue list |>
End

Definition get_setupparams_def:
  get_setupparams = Setup_setupParams
End

Datatype : 
  Contract = <| init: (Chain -> ContractCallContext -> Setup -> State); receive: (Chain -> ContractCallContext -> Campaign -> Data -> State) |>
End

Definition build_context_def :  
  build_context from n = <| msgSender := from; blockNum := n|>
End

Definition build_contract_def :  
  build_contract i r = <| init := i; receive := r|>
End

Definition get_init_def:
  get_init = Contract_init
End

Definition get_receive_def:
  get_receive = Contract_receive
End

Datatype:
  ActionBody = Call Address Data | Deploy Contract Setup | noAct
End

(* сам запрос к контракту *)
Datatype :
  Action = <| actFrom : Address; actBody : ActionBody |> 
End

Definition get_actFrom_def:
  get_actFrom = Action_actFrom
End

Definition get_actBody_def:
  get_actBody = Action_actBody
End

Definition act_is_from_account_def: 
  act_is_from_account act = (address_is_contract (get_actFrom act) = F)
End

Datatype:
  Environment = <| envChain : Chain; envContracts : (Address -> Contract option); envContractStates : (Address -> Campaign option)|>
End

Definition get_envChain_def:
  get_envChain = Environment_envChain
End

Definition get_envContracts_def:
  get_envContracts = Environment_envContracts
End

Definition get_envContractStates_def:
  get_envContractStates = Environment_envContractStates
End

Definition EnvironmentEquiv_def:
  EnvironmentEquiv e1 e2 = ((ChainEquiv (get_envChain e1) (get_envChain e2)) ∧
    (∀c. get_envContracts e1 c = get_envContracts e2 c) ∧
    (∀addr. get_envContractStates e1 addr = get_envContractStates e2 addr))
End

Definition add_contract_def :  
  add_contract addr c rec : Environment = 
    rec with envContracts := (get_envContracts rec) (|addr |-> SOME c|) 
End

Definition set_contract_state_def :  
  set_contract_state addr state rec : Environment = 
    rec with envContractStates := (get_envContractStates rec) (|addr |-> SOME state|) 
End

Definition build_act_def :  
  build_act addr body = <| actFrom := addr; actBody := body |>
End

Definition build_ccc_def :  
  build_ccc from to= <| msgSender := from; ctxContractAddress := to|>
End
 
Definition get_campaign_def :  
  get_campaign (Ret (SCCampaign c) _) = SOME c ∧
  get_campaign (Some (SCCampaign c)) = SOME c ∧
  get_campaign _ = NONE
End

Inductive ActionEvaluation:
      (∀ prevEnv act newEnv from to c setup state. 
      (address_is_contract to = T) ∧
      (get_envContracts prevEnv to = NONE) ∧
      (act = build_act from (Deploy c setup)) ∧
      (get_campaign (get_init c (get_envChain prevEnv) (build_ccc from to) setup) = SOME state) ∧
      (newEnv = set_contract_state to state (add_contract to c prevEnv)) ==>
      ActionEvaluation prevEnv act newEnv) ∧
      (∀ prevEnv act newEnv from to c prevState data nextState.
      (get_envContracts prevEnv to = SOME c) ∧
      (get_envContractStates prevEnv to = SOME prevState) ∧
      (act = build_act from (Call to data)) ∧
      (get_campaign (get_receive c (get_envChain prevEnv) (build_ccc from to) prevState data) = SOME nextState) ∧
      (newEnv = set_contract_state to nextState prevEnv) ==>
      ActionEvaluation prevEnv act newEnv)
End

Inductive ChainStep:
  (∀prevState nextState act. (~(get_actBody act = noAct) ∧
  ActionEvaluation prevState act nextState) ==> ChainStep prevState nextState)
End

Inductive ChainedList:
  (∀ p. ChainedList R p p) ∧
  (∀ x z. (?y. R x y ∧ ChainedList R y z) ==> ChainedList R x z)  
End

Inductive ChainTrace :
  (∀ s1 s2. ChainedList ChainStep s1 s2 ==> ChainTrace s1 s2) 
End

Definition empty1_def:
  empty1 _ = NONE
End

Definition empty2_def:
  empty2 _ = NONE
End

Definition emptyState_def:
  emptyState = <| envChain := <| chainHeight := 0; blockNum := 0|>;
                  envContracts := empty1;
                  envContractStates := empty2 |>
End

Inductive reachable :
  (∀ s. (ChainTrace emptyState s) ∧ (~ (emptyState = s)) ==> reachable s) 
End

Inductive transition_relation:
  (∀s. transition_relation s s) ∧
  (∀s t. ChainStep s t ==> transition_relation s t)
End

Definition invariant_def:
  invariant p = (!(s: Environment) (t: Environment). p s /\ ChainStep s t ==> p t)  
End

Definition lAnd_def:
    lAnd P Q (str : Environment llist) = (P str /\ Q str)
End

Definition next_def:
    next P (str : Environment llist) = P (LTL str)
End

Inductive until:
    (!(str : Environment llist). Q str ==> until P Q str) ∧
    (!s (str : Environment llist). P (LCONS s str) /\ until P Q str ==> until P Q (LCONS s str))
End

CoInductive globally:
    (!s (str : Environment llist). P (LCONS s str) /\ globally (P str) ==> globally (P (LCONS s str)))
End

Definition path_def:
    path (str : Environment llist) = (globally (transition_relation (THE (LHD str)) (THE (LHD (THE (LTL str))))) /\ 
                                      (THE (LHD str) = emptyState))
End

Definition safe_def:
    safe f = (!str. path str ==> globally (f str))
End

Definition s2s_def:
    s2s P (str : Environment llist) = P (THE (LHD str))
End

Theorem safety:
    !p e. e = emptyState /\ p e /\ invariant p ==> safe (s2s p)
Proof 
    rw [safe_def, s2s_def] >> fs [invariant_def] >> rw [Once globally_cases] >> fs [path_def] >> fs [Once globally_cases] >> fs [] >> Q.EXISTS_TAC ‘P’ >> Q.EXISTS_TAC ‘s’ >> Q.EXISTS_TAC ‘str'’ >> rw [] >> Q.EXISTS_TAC ‘P’ >> Q.EXISTS_TAC ‘s’ >> Q.EXISTS_TAC ‘str'’ >> rw [] >> fs [Once globally_cases] 
QED

Theorem globally_induction:
  !p str. invariant p /\ path str /\ p (THE (LHD str)) ==> globally ((s2s p) str)
Proof
  rw [Once globally_cases] >> rw [s2s_def] >> fs [invariant_def, path_def] >> fs [Once globally_cases] >> fs [] >> Q.EXISTS_TAC ‘P’ >> Q.EXISTS_TAC ‘s’ >> Q.EXISTS_TAC ‘str'’ >> rw [] >> Q.EXISTS_TAC ‘P’ >> Q.EXISTS_TAC ‘s’ >> Q.EXISTS_TAC ‘str'’ >> rw [] >> fs [Once globally_cases]
QED

val _ = export_theory();
