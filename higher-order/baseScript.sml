(* +----------------------------------------------------------------------------+
    START (open, load)
    DEFINS (datatypes)
    CONSTS
    BASICS:
        oLAST
        oFRONT
        TASK_HASH
    CHEATS
    LOWFUNCS   (as in definitions)
    MIDFUNCS   (--"--)
    HIGHBASICS (--"--)
    HIGHFUNCS  (--"--)
    MOREFUNCS
    PROPS
    THEOREMS
    GOALTHMS
   +----------------------------------------------------------------------------+ *)
(*START ------------------------------------------------------------------------- *)
app load ["stringTheory","wordsTheory", "llistTheory"(* , "preamble" *)];

open arithmeticTheory listTheory stringTheory combinTheory wordsTheory HolKernel boolLib Parse bossLib optionTheory llistTheory;

open sc1TypesTheory
open chainTheory

val _ = new_theory "base";

val const_defs = [
    Define `BAD_ERR = None "Error"`,
    Define `BAD_TYPE = None "Type error"`,
    Define `ERR_TYPE_CONV = None "Type conversion error"`,
    Define `WRNG_NMBR = None "Wrong number of params."`,
    Define `PARSE_ERR_taskId = None "Parse param error: taskId incorrect type."`,
    Define `PRICE_GT0 = None "Price must be more than 0."`,
    Define `NEX_Task = None "Task does not exist."`,
    Define `ONLY_Suppl_appr = None "Only supplier allowed to approve"`,
    Define `NOT_PhTasks = None "Phase is not PhaseTasks"`,
    Define `ONLY_Suppl_rej = None "Only supplier allowed to reject"`,
    Define `NOT_APPROVED_Task = None "Task is not approved yet."`,
    Define `ONLY_worker_acc = None "Only worker allowed to accept Task"`,
    Define `NOT_APPROVED_task = None "Task is not approved yet."`,
    Define `ONLY_SupplCust_get = None "Only supplier or customer allowed to get task"`,
    Define `NOT_ALLOWED_action = None "Action is not allowed at this point."`,
    Define `NOT_ALLOWED_SUPPLIER_REJECT = None "Supplier is not allowed to reject at this point"`,
    Define `NOT_ALLOWED_CUSTOMER_CHANGE_AGREEMENT = None "Customer is not allowed to change agreement at this point"`,
    Define `ONLY_CUST_OR_SUPPL_ALLOWED_VIEW_AGREEMENT = None "Only customer or supplier allowed to view agreement"`,
    Define `ONLY_WAITING_SUPPLIER = None "AgreementNegotiation should be WaitingSupplier"`,
    Define `ONLY_SUPPLIER_REJECT = None "Only supplier is allowed to reject at this point"`,
    Define `ONLY_SUPPLIER_APPROVE = None "Only supplier is allowed to approve at this point"`,
    Define `ONLY_CUSTOMER_CHANGE = None "Only customer is allowed to change agreement at this point"`,
    Define `NO_GAS_REQUESTS = None "No gas requests."`,
    Define `NO_APPROVED_PRICES = None "No approved prices."`,
    Define `NEX_Payment = None "Payment order does not exist."`,
    Define `ONLY_Captain = None "Only captain allowed to do this action."`,
    Define `NEX_function = None "The function doesn't exist"`,
    Define `WRNG_COND_001 = None "Wrong conditions. Please, check: Task must not be approved, Agreement is approved, at least one PriceChange is approved."`,
    Define `AGREEMENT_IS_APPROVED = None "AgreementNegotiation must not be approved."`,
    Define `WRNG_COND_002 = None "Wrong conditions. Please, check: param is a number, sender is Customer, at least one PriceChange exists."`,
    Define `WRNG_COND_003 = None "Wrong conditions. Please, check: sender is Customer, at least one PriceChange exists."`,
    Define `WRNG_COND_004 = None "Wrong conditions. Please, check: sender is Customer, phase is PhaseTasks, at least one PriceChange exists, Agreement is approved."`,
    Define `WRNG_COND_005 = None "Wrong conditions. Please, check: sender is Supplier, phase is PhaseTasks, last PriceChange is approved or rejected, Agreement is approved."`,
    Define `WRNG_COND_006 = None "Wrong conditions. Please, check: params are two numbers."`,
    Define `WRNG_COND_007 = None "Wrong conditions. Please, check: Agreement is approved, at least one PriceChange is approved."`,
    Define `WRNG_COND_008 = None "Wrong conditions. Please, check: params are (number, string, number, string, number, PaymentType), sender is Customer, phase is PhaseTask, Agreement is approved, at least one PriceChange is approved."`,
    Define `WRNG_COND_009 = None "Wrong conditions. Please, check: sender is Worker, Task is approved and accepted."`,
    Define `WRNG_COND_010 = None "Wrong conditions. Please, check: param is a number, phase is PhaseTasks, Agreement is approved, at least one PriceChange exists."`,
    Define `WRNG_COND_011 = None "Wrong conditions. Please, check: sender is Captain, Agreement is approved, Task approved and ready to perform or gas requested."`,
    Define `WRNG_COND_012 = None "Wrong conditions. Please, check: params are two numbers, phase is PhaseTasks."`,
    Define `WRNG_COND_013 = None "Wrong conditions. Please, check: param is a number, phase is PhaseTasks, Agreement is approved, at least one PriceChange is approved."`,
    Define `WRNG_COND_014 = None "Wrong conditions. Please, check: sender is Worker, gas is requested, Task is approved."`,
    Define `WRNG_COND_015 = None "Wrong conditions. Please, check: sender is Worker, Task is approved and performing now."`,
    Define `WRNG_COND_016 = None "Wrong conditions. Please, check: params are two numbers, phase is PhaseTasks, Agreement is approved, at least one PriceChange is approved."`
    ];

(*BASICS ------------------------------------------------------------------------ *)

Definition oLAST_DEF:
    oLAST [] = NONE ∧
    oLAST (h::t) = SOME $ LAST (h::t)
End
Definition oFRONT_DEF:
    oFRONT [] = NONE ∧
    oFRONT (h::t) = SOME $ FRONT (h::t)
End

(*LOWFUNCS ---------------------------------------------------------------------- *)
(* All it is maintained from bad times, our code is better *)

(*Person*)
Definition set_person_id_def:
    set_person_id rec value :Person = rec with id := value
End
Definition set_person_name_def:
    set_person_name rec value :Person = rec with name := value
End
Definition get_person_id_def:
    get_person_id = Person_id
End
Definition get_person_name_def:
    get_person_name = Person_name
End

val Person_defs = [set_person_id_def, set_person_name_def, get_person_id_def, get_person_name_def];

(*AgreementDetails*)
Definition set_agreementDetails_details_def:
    set_agreementDetails_details rec value :AgreementDetails = rec with details := value
End
Definition set_agreementDetails_bankAddress_def:
    set_agreementDetails_bankAddress rec value :AgreementDetails = rec with bankAddress := value
End
Definition get_agreementDetails_details_def:
    get_agreementDetails_details = AgreementDetails_details
End
Definition get_agreementDetails_bankAddress_def:
    get_agreementDetails_bankAddress = AgreementDetails_bankAddress
End
(* TODO *)

(*Agreement*)
Definition set_agreement_negotiation_def:
    set_agreement_negotiation ag v :Agreement = ag with negotiation := v
End
Definition set_agreement_customer_def:
    set_agreement_customer ag v :Agreement = ag with customer := v
End
Definition set_agreement_supplier_def:
    set_agreement_supplier ag v :Agreement = ag with supplier := v
End
Definition set_agreement_details_def:
    set_agreement_details ag v :Agreement = ag with details := v
End
Definition get_agreement_negotiation_def:
    get_agreement_negotiation = Agreement_negotiation
End
Definition get_agreement_customer_def:
    get_agreement_customer = Agreement_customer
End
Definition get_agreement_supplier_def:
    get_agreement_supplier = Agreement_supplier
End
Definition get_agreement_details_def:
    get_agreement_details = Agreement_details
End
(* TODO *)

(*PriceChange*)
Definition set_priceChange_price_def:
    set_priceChange_price rec value :PriceChange = rec with price := value
End
Definition set_priceChange_negotiation_def:
    set_priceChange_negotiation rec value :PriceChange = rec with negotiation := value
End
Definition set_priceChange_startTime_def:
    set_priceChange_startTime rec value :PriceChange = rec with startTime := value
End
Definition get_priceChange_price_def:
    get_priceChange_price = PriceChange_price
End
Definition get_priceChange_negotiation_def:
    get_priceChange_negotiation = PriceChange_negotiation
End
Definition get_priceChange_startTime_def:
    get_priceChange_startTime = PriceChange_startTime
End
(* TODO *)

(*PaymentOrder*)
Definition set_PaymentOrder_amount_def:
    set_PaymentOrder_amount rec value :PaymentOrder = rec with amount := value
End
Definition set_PaymentOrder_paymentTime_def:
    set_PaymentOrder_paymentTime rec value :PaymentOrder = rec with paymentTime := value
End
Definition set_PaymentOrder_paymentId_def:
    set_PaymentOrder_paymentId rec value :PaymentOrder = rec with paymentId := value
End
Definition set_PaymentOrder_taskId_def:
    set_PaymentOrder_taskId rec value :PaymentOrder = rec with taskId := value
End
Definition set_PaymentOrder_paymentStatus_def:
    set_PaymentOrder_paymentStatus rec value :PaymentOrder = rec with paymentStatus := value
End
Definition set_PaymentOrder_direction_def:
    set_PaymentOrder_direction rec value :PaymentOrder = rec with direction := value
End
Definition get_PaymentOrder_amount_def:
    get_PaymentOrder_amount = PaymentOrder_amount
End
Definition get_PaymentOrder_paymentTime_def:
    get_PaymentOrder_paymentTime = PaymentOrder_paymentTime
End
Definition get_PaymentOrder_paymentId_def:
    get_PaymentOrder_paymentId = PaymentOrder_paymentId
End
Definition get_PaymentOrder_taskId_def:
    get_PaymentOrder_taskId = PaymentOrder_taskId
End
Definition get_PaymentOrder_paymentStatus_def:
    get_PaymentOrder_paymentStatus = PaymentOrder_paymentStatus
End
Definition get_PaymentOrder_direction_def:
    get_PaymentOrder_direction = PaymentOrder_direction
End
(* TODO *)

(*Task*)
Definition set_task_id_def:
    set_task_id t v :Task = t with taskID := v
End
Definition set_task_negotiation_def:
    set_task_negotiation t v :Task = t with negotiation := v
End
Definition set_task_captain_def:
    set_task_captain t v :Task = t with captain := v
End
Definition set_task_worker_def:
    set_task_worker t v :Task = t with worker := v
End
Definition set_task_expectedGas_def:
    set_task_expectedGas t v :Task = t with expectedGas := v
End
Definition set_task_requestedGas_def:
    set_task_requestedGas t v :Task = t with requestedGas := v
End
Definition set_task_suppliedGas_def:
    set_task_suppliedGas t v :Task = t with suppliedGas := v
End
Definition set_task_totalGas_def:
    set_task_totalGas t v :Task = t with totalGas := v
End
Definition set_task_requestTime_def:
    set_task_requestTime t v :Task = t with requestTime := v
End
Definition set_task_suppliedTime_def:
    set_task_suppliedTime t v :Task = t with suppliedTime := v
End
Definition set_task_completionTime_def:
    set_task_completionTime t v :Task = t with completionTime := v
End
Definition set_task_paymentTime_def:
    set_task_paymentTime t v :Task = t with paymentTime := v
End
Definition set_task_taskStatus_def:
    set_task_taskStatus t v :Task = t with taskStatus := v
End
Definition set_task_paymentType_def:
    set_task_paymentType t v :Task = t with paymentType := v
End
Definition get_task_id_def:
    get_task_id = Task_taskID
End
Definition get_task_negotiation_def:
    get_task_negotiation = Task_negotiation
End
Definition get_task_captain_def:
    get_task_captain = Task_captain
End
Definition get_task_worker_def:
    get_task_worker = Task_worker
End
Definition get_task_expectedGas_def:
    get_task_expectedGas = Task_expectedGas
End
Definition get_task_requestedGas_def:
    get_task_requestedGas = Task_requestedGas
End
Definition get_task_suppliedGas_def:
    get_task_suppliedGas = Task_suppliedGas
End
Definition get_task_totalGas_def:
    get_task_totalGas = Task_totalGas
End
Definition get_task_requestTime_def:
    get_task_requestTime = Task_requestTime
End
Definition get_task_suppliedTime_def:
    get_task_suppliedTime = Task_suppliedTime
End
Definition get_task_completionTime_def:
    get_task_completionTime = Task_completionTime
End
Definition get_task_paymentTime_def:
    get_task_paymentTime = Task_paymentTime
End
Definition get_task_taskStatus_def:
    get_task_taskStatus = Task_taskStatus
End
Definition get_task_paymentType_def:
    get_task_paymentType = Task_paymentType
End
(* TODO *)

(*Compaign*)
Definition set_campaign_agreement_def:
    set_campaign_agreement ca v :Campaign = ca with agreement := v
End
Definition set_campaign_tasks_def:
    set_campaign_tasks ca v :Campaign = ca with tasks := v
End
Definition set_campaign_negotiation_def:
    set_campaign_negotiation ca v :Campaign = ca with negotiation := v
End
Definition set_campaign_priceChanges_def:
    set_campaign_priceChanges ca v :Campaign = ca with priceChanges := v
End
Definition set_campaign_phase_def:
    set_campaign_phase ca v :Campaign = ca with phase := v
End
Definition set_campaign_paymentOrders_def:
    set_campaign_paymentOrders ca v :Campaign = ca with paymentOrders := v
End
Definition get_campaign_agreement_def:
    get_campaign_agreement = Campaign_agreement
End
Definition get_campaign_tasks_def:
    get_campaign_tasks = Campaign_tasks
End
Definition get_campaign_negotiation_def:
    get_campaign_negotiation = Campaign_negotiation
End
Definition get_campaign_priceChanges_def:
    get_campaign_priceChanges = Campaign_priceChanges
End
Definition get_campaign_phase_def:
    get_campaign_phase = Campaign_phase
End
Definition get_campaign_paymentOrders_def:
    get_campaign_paymentOrders = Campaign_paymentOrders
End
(* TODO *)

(*Context*)
Definition set_context_msgSender_def:
    set_context_msgSender con v :Context = con with msgSender := v
End
Definition set_context_blockNum_def:
    set_context_blockNum con v :Context = con with blockNum := v
End
Definition get_context_msgSender_def:
    get_context_msgSender = Context_msgSender
End
Definition get_context_blockNum_def:
    get_context_blockNum = Context_blockNum
End
(* TODO *)

Definition typeOf_def:
  typeOf (SCInt _) = TypeInt ∧
  typeOf (SCString _) = TypeString ∧
  typeOf (SCBool _) = TypeBool ∧
  typeOf (SCAgreement _) = TypeAgreement ∧
  typeOf (SCTask _) = TypeTask ∧
  typeOf (SCNegotiation _) = TypeNegotiation ∧
  typeOf (SCPriceChange _) = TypePriceChange ∧
  typeOf (SCPaymentOrder _) = TypePaymentOrder ∧
  typeOf (SCCampaign _) = TypeCampaign ∧
  typeOf (SCPerson _) = TypePerson ∧
  typeOf (SCPaymentStatus _) = TypePaymentStatus ∧
  typeOf (SCTaskStatus _) = TypeTaskStatus ∧
  typeOf (SCAgreementDetails _) = TypeAgreementDetails ∧
  typeOf (SCPaymentType _) = TypePaymentType ∧
  typeOf (SCPhase _) = TypePhase
End

(* TODO: unite all definitions of this part *)

(*CHEATS ------------------------------------------------------------------------ *)
Definition checkTypes_def:
  checkTypes params paramTypes = (MAP typeOf params = paramTypes)
End
Definition scToInt_def:
  scToInt (SCInt x) = x
End
Definition scToString_def:
  scToString (SCString x) = x
End
Definition scToBool_def:
  scToBool (SCBool x) = x
End
Definition scToAgreement_def:
  scToAgreement (SCAgreement x) = x
End
Definition scToTask_def:
  scToTask (SCTask x) = x
End
Definition scToNegotiation_def:
  scToNegotiation (SCNegotiation x) = x
End
Definition scToPriceChange_def:
  scToPriceChange (SCPriceChange x) = x
End
Definition scToPaymentOrder_def:
  scToPaymentOrder (SCPaymentOrder x) = x
End
Definition scToCampaign_def:
  scToCampaign (SCCampaign x) = x
End
Definition scToPerson_def:
  scToPerson (SCPerson x) = x
End
Definition scToPaymentStatus_def:
  scToPaymentStatus (SCPaymentStatus x) = x
End
Definition scToTaskStatus_def:
  scToTaskStatus (SCTaskStatus x) = x
End
Definition scToAgreementDetails_def:
  scToAgreementDetails (SCAgreementDetails x) = x
End
Definition scToPaymentType_def:
  scToPaymentType (SCPaymentType x) = x
End
Definition scToPhase_def:
  scToPhase (SCPhase x) = x
End

(*MIDFUNCS ---------------------------------------------------------------------- *)
(* HASH *)
Definition TASK_HASH_DEF:
    TASK_HASH (tl:Task list) = SUC $ FOLDR MAX 0 (MAP get_task_id tl)
End
(*
TASK_HASH (tl:Task list) = SUC $ FOLDR (MAX o get_task_id) 0 tl
(TASK_HASH: Task list -> num) = SUC o LENGTH
*)

(*Agreement*)
Definition update_agreement_details_def:
    update_agreement_details = set_agreement_details
End
Definition approve_agreement_def:
    approve_agreement agreement = set_agreement_negotiation agreement NegotiationApproved
End
Definition reject_agreement_def:
    reject_agreement agreement = set_agreement_negotiation agreement NegotiationRejected
End

(*Campaign*)
(* Definition checkIds_def:
  checkIds taskId [] = NONE /\
  checkIds taskId (h::t) = if (get_task_id h = taskId) then SOME h else checkIds taskId t
End  

Definition p_get_campaign_task_by_task_id_def:
    p_get_campaign_task_by_task_id campaign taskId = 
      let tasks = get_campaign_tasks campaign;
      in checkIds taskId tasks 
End *)

Definition p_get_campaign_task_by_task_id_def:
    p_get_campaign_task_by_task_id campaign taskId =
        FIND (λx. get_task_id x = taskId) $ get_campaign_tasks campaign
End

Definition p_add_task_in_Campaign_def:
    p_add_task_in_Campaign campaign task =
       set_campaign_tasks campaign $ task :: (get_campaign_tasks campaign)
End

Definition calculateLastPrice_def:
  calculateLastPrice campaign =
    oHD $ dropWhile ($≠ NegotiationApproved o get_priceChange_negotiation) (get_campaign_priceChanges campaign)
End


(* 1) use this instead of "LUPDATE newrez indx tasks" *)
(* 2) rewrite p_update_Campaign_tasks_def using this definition *)
Definition UPDATE_BY_ID_def:
  UPDATE_BY_ID newrez id tasks =
    MAP (λt. (if t.taskID = id then (newrez with taskID := id) else t)) tasks
End

Definition p_update_Campaign_tasks_def:
   p_update_Campaign_tasks campaign task taskId =
     set_campaign_tasks campaign $ UPDATE_BY_ID task taskId (get_campaign_tasks campaign)
End

Definition p_get_task_index_by_id_def:
    p_get_task_index_by_id taskList taskId=
        INDEX_FIND 0 (λx. get_task_id x = taskId) taskList
End (*WARNG! RETURN TYPE IS option*)

(*PriceChange*)
Definition p_add_priceChange_in_Campaign_def:
    p_add_priceChange_in_Campaign campaign priceChange =
       set_campaign_priceChanges campaign $ priceChange::(get_campaign_priceChanges campaign)
End

Definition p_get_paymentOrder_by_id_def:
    p_get_paymentOrder_by_id campaign paymentId =
        FIND ((=) paymentId o get_PaymentOrder_paymentId) $ get_campaign_paymentOrders campaign
End

Definition p_update_Campaign_paymentOrders_def:
   p_update_Campaign_paymentOrders campaign payment paymentId =
     set_campaign_paymentOrders campaign $
     MAP (\pmt. if paymentId  = get_PaymentOrder_paymentId payment then payment else pmt) (get_campaign_paymentOrders campaign)
End

(*SCValue*)
Definition scvalue_to_int_def_def:
    scvalue_to_int (SCInt x) = SOME x ∧
    scvalue_to_int _ = NONE
End

(* TODO: unite all definitions of this part *)

Definition addErr_def:
    addErr _ (SOME x) = Some x ∧
    addErr err NONE = None err
End
Definition get_err_def:
    get_err (None x) = SOME x ∧
    get_err _ = NONE
End

Definition p_base_task_replacing_fn_def:
    p_base_task_replacing_fn (main_fn,fin) campaign rez id =
        let newrez = main_fn rez fin;
        in
            set_campaign_tasks campaign $ UPDATE_BY_ID newrez id (get_campaign_tasks campaign)
End

(*HIGHBASICS -------------------------------------------------------------------- *)
Definition isSenderCustomer_def:
    isSenderCustomer context campaign =
      (get_context_msgSender context = get_person_id $ get_agreement_customer $ get_campaign_agreement campaign)
End
Definition isSenderSupplier_def:
    isSenderSupplier context campaign =
      (get_context_msgSender context = get_person_id $ get_agreement_supplier $ get_campaign_agreement campaign)
End
Definition isSenderWorker_def:
    isSenderWorker context task =
      (get_context_msgSender context = get_person_id $ get_task_worker task)
End
Definition isSenderCaptain_def:
    isSenderCaptain context task =
      (get_context_msgSender context = get_person_id $ get_task_captain task)
End
Definition approvedPriceExists_def:
  approvedPriceExists =
    EXISTS (λx. get_priceChange_negotiation x = NegotiationApproved) o get_campaign_priceChanges
End
Definition p_approve_task_by_rez_id_def:
    p_approve_task_by_rez_id =
        p_base_task_replacing_fn (set_task_negotiation, NegotiationApproved)
End
Definition p_reject_task_by_rez_id_def:
    p_reject_task_by_rez_id =
        p_base_task_replacing_fn (set_task_negotiation, NegotiationRejected)
End
Definition p_accept_task_by_rez_id_def:
    p_accept_task_by_rez_id =
        p_base_task_replacing_fn (set_task_taskStatus, TaskAccepted)
End

Definition base_task_fn_def:
    base_task_fn (main_fn,ONLY) context params campaign = (case params of
            [a] => (case a of
                SCInt x => (case p_get_task_index_by_id (get_campaign_tasks campaign) x of
                        NONE => NEX_Task
                        | SOME (_(*indx*), rez) => if get_context_msgSender context = get_person_id $ get_agreement_supplier $ get_campaign_agreement campaign
                            then (case get_campaign_phase campaign of
                                PhaseTasks =>
                                    if get_task_negotiation rez = NegotiationApproved ∨ get_agreement_negotiation $ get_campaign_agreement campaign ≠ NegotiationApproved ∨ ¬(approvedPriceExists campaign) then WRNG_COND_001 else
                                    Some $ SCCampaign $ main_fn campaign rez x(*it used to be indx*)
                                | _ => NOT_PhTasks)
                            else ONLY)
                | _ => PARSE_ERR_taskId)
            | _ => WRNG_NMBR)
End

(* 2+ *)
Definition getAgreement_typed_def:
  getAgreement_typed context params campaign =
  let
    sender = (get_context_msgSender context);
    agreement = (get_campaign_agreement campaign);
    customer = (get_agreement_customer agreement);
    supplier = (get_agreement_supplier agreement);
    custPersID = (get_person_id customer);
    suppPersID = (get_person_id supplier);
  in
  if (sender = custPersID) then
    Ret (SCCampaign campaign) (SCAgreement agreement)
  else
    if (sender = suppPersID) then
      Ret (SCCampaign campaign) (SCAgreement agreement)
    else
      ONLY_CUST_OR_SUPPL_ALLOWED_VIEW_AGREEMENT
End

(* 3+ *)
Definition rejectAgreement_typed_def:
  rejectAgreement_typed context params campaign =
  let
    sender = (get_context_msgSender context);
    agreement = (get_campaign_agreement campaign);
    supplier = (get_agreement_supplier agreement);
    persID = (get_person_id supplier);
  in
  if get_agreement_negotiation agreement ≠ WaitingSupplier then ONLY_WAITING_SUPPLIER else
  if ¬(sender = persID) then ONLY_SUPPLIER_REJECT else
  let phase = (get_campaign_phase campaign) in
  if ¬(phase = PhaseAgreement) then NOT_ALLOWED_SUPPLIER_REJECT else
  let negotiation = (get_campaign_negotiation campaign) in
  if ¬(negotiation = WaitingSupplier) then NOT_ALLOWED_SUPPLIER_REJECT
    (* "Supplier is not waiting" *) else
  let newagreement = set_agreement_negotiation agreement WaitingCustomer in
  let newcampaign  = set_campaign_agreement campaign newagreement in
  Some (SCCampaign newcampaign)
End


(* 4+ *)
Definition approveAgreement_typed_def:
  approveAgreement_typed context params campaign =
  let
    sender = (get_context_msgSender context);
    agreement = (get_campaign_agreement campaign);
    supplier = (get_agreement_supplier agreement);
    persID = (get_person_id supplier);
  in
  if get_agreement_negotiation agreement ≠ WaitingSupplier then ONLY_WAITING_SUPPLIER else
  if ¬(sender = persID) then ONLY_SUPPLIER_APPROVE else
  let phase = (get_campaign_phase campaign) in
  if ¬(phase = PhaseAgreement) then NOT_ALLOWED_SUPPLIER_REJECT else
  let negotiation = (get_campaign_negotiation campaign) in
  if ¬(negotiation = WaitingSupplier) then NOT_ALLOWED_SUPPLIER_REJECT
    (* ??? "Supplier is not waiting" *) else

  let newagreement = set_agreement_negotiation agreement NegotiationApproved in
  let newcampaign  = set_campaign_phase campaign PhaseTasks in
  let newcampaign  = set_campaign_agreement newcampaign newagreement in

  let newcampaign  = campaign in
  Some (SCCampaign newcampaign)
  (* SOME (SCCampaign (set_campaign_agreement (set_campaign_phase campaign PhaseTasks) (set_agreement_negotiation agreement NegotiationApproved))
  ) *)
End


(* 5+ *)
Definition changeAgreement_def:
  changeAgreement context campaign newdetailsSTR bankAddr =
  let
    sender = (get_context_msgSender context);
    agreement = (get_campaign_agreement campaign);
    supplier = (get_agreement_supplier agreement);
    persID = (get_person_id supplier)
  in
  if get_agreement_negotiation agreement = NegotiationApproved then AGREEMENT_IS_APPROVED else
  if ¬(sender = persID) then ONLY_CUSTOMER_CHANGE else
  let phase = (get_campaign_phase campaign) in

  if ¬(phase = PhaseAgreement) then NOT_ALLOWED_CUSTOMER_CHANGE_AGREEMENT else
  let negotiation = (get_campaign_negotiation campaign) in
  if ¬(negotiation = WaitingCustomer) then NOT_ALLOWED_CUSTOMER_CHANGE_AGREEMENT else
  let newagreement = set_agreement_negotiation agreement WaitingSupplier in
  let
    newdetails = (AgreementDetails newdetailsSTR bankAddr);
    newagreement = set_agreement_details newagreement newdetails;
    newagreement = set_agreement_negotiation newagreement WaitingSupplier;
    newcampaign  = set_campaign_phase campaign PhaseTasks;
    newcampaign  = set_campaign_agreement newcampaign newagreement;
  in
  Some (SCCampaign newcampaign)
End

Definition changeAgreement_typed_def:
  changeAgreement_typed context params campaign =
  if ¬(checkTypes params [TypeString; TypeInt]) then BAD_TYPE else
  let
    newdetailsSTR = scToString (HD params);
    bankAddr = scToInt (EL 1 params);
  in
  (changeAgreement context campaign newdetailsSTR bankAddr)
End

(* 6+ *)
Definition getPriceChangeWithNumber_typed_def:
getPriceChangeWithNumber_typed context params campaign =
  if checkTypes params [TypeInt] ∧
     isSenderCustomer context campaign ∧
     (¬ NULL (get_campaign_priceChanges campaign))
  then
    let
      index = (scToInt $ HD params);
    in
      Ret (SCCampaign campaign) (SCPriceChange (EL index (*обезопасить с пом. oEL*) (get_campaign_priceChanges campaign)))
  else
    WRNG_COND_002
End

(* 7+ *)
Definition getPriceChangesLength_typed_def:
getPriceChangesLength_typed context params campaign =
  if isSenderCustomer context campaign ∧
     (¬ NULL (get_campaign_priceChanges campaign))
  then
     Ret (SCCampaign campaign) (SCInt (LENGTH (get_campaign_priceChanges campaign)))
  else
     WRNG_COND_003
End

(* 8+ *)
Definition rejectPrice_typed_def:
rejectPrice_typed context params campaign =
  if isSenderCustomer context campaign ∧
     (get_campaign_phase campaign) = PhaseTasks ∧
     (¬ NULL (get_campaign_priceChanges campaign)) ∧
     (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
     (get_priceChange_negotiation (HD (get_campaign_priceChanges campaign))) = WaitingCustomer
  then
      Some $ SCCampaign $ set_campaign_priceChanges campaign ((set_priceChange_negotiation (HD $ get_campaign_priceChanges campaign) NegotiationRejected)::(TL $ get_campaign_priceChanges campaign))
  else
      WRNG_COND_004
End

(* 9+ *)
Definition approvePrice_typed_def:
approvePrice_typed context params campaign =
  if isSenderCustomer context campaign ∧
     (get_campaign_phase campaign) = PhaseTasks ∧
     (¬ NULL (get_campaign_priceChanges campaign)) ∧
     (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
     (get_priceChange_negotiation $ HD $ get_campaign_priceChanges campaign) = WaitingCustomer
  then
    Some $ SCCampaign $ set_campaign_priceChanges campaign ((set_priceChange_negotiation (HD $ get_campaign_priceChanges campaign) NegotiationApproved)::(TL $ get_campaign_priceChanges campaign))
  else
    WRNG_COND_004
End

(* 10+ *)
Definition declinePrice_typed_def:
declinePrice_typed context params campaign =
  if isSenderCustomer context campaign ∧
     (get_campaign_phase campaign) = PhaseTasks ∧
     (¬ NULL (get_campaign_priceChanges campaign)) ∧
     (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
     (get_priceChange_negotiation $ HD $ get_campaign_priceChanges campaign) = WaitingCustomer
  then
      Some $ SCCampaign (set_campaign_phase campaign PhaseDeclined)
  else
      WRNG_COND_004
End

Definition createPriceChange_def:
createPriceChange context campaign price startTime =
    let
      agreement = (get_campaign_agreement campaign);
    in
    if isSenderSupplier context campaign ∧
       (get_campaign_phase campaign) = PhaseTasks ∧
       (¬ NULL (get_campaign_priceChanges campaign)) ∧
       (EXISTS ($= $ get_priceChange_negotiation $ HD $ get_campaign_priceChanges campaign) [NegotiationApproved; NegotiationRejected]) ∧
       ((get_agreement_negotiation agreement) = NegotiationApproved)
    then
        Some $ SCCampaign $ p_add_priceChange_in_Campaign campaign (PriceChange price WaitingCustomer startTime)
    else
        WRNG_COND_005
End

(* 11+ *)
Definition createPriceChange_typed_def:
createPriceChange_typed context params campaign =
  if checkTypes params [TypeInt; TypeInt] then
    let
      price = scToInt(HD params);
      startTime = scToInt (EL 1 params);
    in
      createPriceChange context campaign price startTime
  else WRNG_COND_006
End

(* 12+ *)
Definition getTask_typed_def:
    getTask_typed context params campaign = case params of
            [a] => (case a of
                SCInt x => (case p_get_task_index_by_id (get_campaign_tasks campaign) x of
                        NONE => NEX_Task
                        | SOME (_, task) => let
                                sender = get_context_msgSender context;
                                agreement = get_campaign_agreement campaign;
                            in
                                if EXISTS ($= sender o get_person_id o $:> agreement) [get_agreement_supplier; get_agreement_customer]
                                then Ret (SCCampaign campaign) (SCTask task)
                                else ONLY_SupplCust_get)
                | _ => PARSE_ERR_taskId)
            | _ => WRNG_NMBR
End

(* 13+ *)
(* Definition approveTask_typed_def:
    approveTask_typed = base_task_fn (p_approve_task_by_rez_id, ONLY_Suppl_appr)
End *)

Definition approveTask_typed_def:
    approveTask_typed context params campaign =
      if checkTypes params [TypeInt] ∧
       get_campaign_phase campaign = PhaseTasks ∧
       (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
       approvedPriceExists campaign
    then
       let
         taskId = scToInt (HD params);
         task = p_get_campaign_task_by_task_id campaign taskId;
       in case task of
          | NONE => NEX_Task
          | SOME task =>
              if get_context_msgSender context = get_person_id $ get_agreement_supplier $ get_campaign_agreement campaign ∧
                 (*WRN*)get_task_negotiation task = NegotiationApproved
              then
                let
                  type = get_task_paymentType task;
                in Some $ SCCampaign (p_update_Campaign_tasks campaign (set_task_negotiation task NegotiationApproved) taskId)
              else
                 NOT_PhTasks
    else
       WRNG_COND_001
End

(* 14+ *)
(* Definition rejectTask_typed_def:
    rejectTask_typed = base_task_fn (p_reject_task_by_rez_id, ONLY_Suppl_rej)
End *)

Definition rejectTask_typed_def:
    rejectTask_typed context params campaign =
      if checkTypes params [TypeInt] ∧
       get_campaign_phase campaign = PhaseTasks ∧
       (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
       approvedPriceExists campaign
    then
       let
         taskId = scToInt (HD params);
         task = p_get_campaign_task_by_task_id campaign taskId;
       in case task of
          | NONE => NEX_Task
          | SOME task =>
              if get_context_msgSender context = get_person_id $ get_agreement_supplier $ get_campaign_agreement campaign ∧
                 (*WRN*)get_task_negotiation task = NegotiationApproved
              then
                let
                  type = get_task_paymentType task;
                in Some $ SCCampaign (p_update_Campaign_tasks campaign (set_task_negotiation task NegotiationRejected) taskId)
              else
                 NOT_PhTasks
    else
       WRNG_COND_001
End

(* 15+ *)
(* Definition acceptTask_typed_def:
    acceptTask_typed context params campaign = (case params of
            [a] => (case a of
                SCInt x => (case p_get_task_index_by_id (get_campaign_tasks campaign) x of
                        NONE => NEX_Task
                        | SOME (_(*indx*), rez) => if get_context_msgSender context = get_person_id $ get_agreement_supplier $ get_campaign_agreement campaign
                            then (case get_campaign_phase campaign of
                                PhaseTasks => (case get_task_negotiation rez of
                                    NegotiationApproved =>
                                        if get_agreement_negotiation $ get_campaign_agreement campaign ≠ NegotiationApproved ∨ ¬(approvedPriceExists campaign) then WRNG_COND_007 else
                                        Some $ SCCampaign $ p_accept_task_by_rez_id campaign rez x(*indx*)
                                    | _ => NOT_APPROVED_task)
                                | _ => NOT_PhTasks)
                            else ONLY_worker_acc)
                | _ => PARSE_ERR_taskId)
            | _ => WRNG_NMBR)
End *)

Definition acceptTask_typed_def:
  acceptTask_typed context params campaign = 
    if checkTypes params [TypeInt] /\
       get_campaign_phase campaign = PhaseTasks /\
       get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved /\ 
       (approvedPriceExists campaign)
    then
      let
         taskId = scToInt (HD params);
         task = p_get_campaign_task_by_task_id campaign taskId;
       in case task of
          | NONE => NEX_Task
          | SOME task =>
              if get_context_msgSender context = get_person_id $ get_agreement_supplier $ get_campaign_agreement campaign /\
                 get_task_negotiation task = NegotiationApproved /\
                 get_task_taskStatus task = TaskNotAccepted
              then 
                Some $ SCCampaign (p_update_Campaign_tasks campaign (set_task_taskStatus task TaskAccepted) taskId)
              else NOT_APPROVED_task
      else WRNG_COND_007
End

(* 17+ *)
Definition addTask_typed_def:
  addTask_typed context params campaign =
    if checkTypes params [TypeInt; TypeString;
         TypeInt; TypeString; TypeInt; TypePaymentType] ∧
       isSenderCustomer context campaign ∧
       get_campaign_phase campaign = PhaseTasks ∧
       (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
       approvedPriceExists campaign
    then
       let
         taskId = TASK_HASH $ get_campaign_tasks campaign;
         captain_id = scToInt (HD params);
         captain_name = scToString (EL 1 params);
         worker_id = scToInt (EL 2 params);
         worker_name = scToString (EL 3 params);
         expectedGas = scToInt (EL 4 params);
         paymentType = scToPaymentType (EL 5 params);

         requestedGas = 0;
         suppliedGas = 0;
         totalGas = 0;
         requestTime = 0;
         suppliedTime = 0;
         completionTime = 0;
         paymentTime = 0;

         task = Task taskId
                 WaitingCustomer
                 (Person captain_id captain_name)
                 (Person worker_id worker_name)
                 expectedGas
                 requestedGas
                 suppliedGas
                 totalGas
                 requestTime
                 suppliedTime
                 completionTime
                 paymentTime
                 TaskNotAccepted
                 paymentType;
       in
         Some $ SCCampaign (p_add_task_in_Campaign campaign task)
    else WRNG_COND_008
End

(* 18+ *)
Definition readyToPerformTask_typed_def:
  readyToPerformTask_typed context params campaign =
    if checkTypes params [TypeInt] ∧
       get_campaign_phase campaign = PhaseTasks ∧
       (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
       approvedPriceExists campaign
    then
       let
         taskId = scToInt (HD params);
         task = p_get_campaign_task_by_task_id campaign taskId;
       in case task of
          | NONE => NEX_Task
          | SOME task =>
              if isSenderWorker context task ∧
                 (*WRN*)get_task_negotiation task = NegotiationApproved ∧
                 get_task_taskStatus task = TaskAccepted
              then
                let
                  type = get_task_paymentType task;
                in Some $ SCCampaign (p_update_Campaign_tasks campaign (set_task_taskStatus task TaskReadyToPerform) taskId)
              else
                 WRNG_COND_009
    else
       WRNG_COND_010
End

(* 19+ *)
Definition requestGas_typed_def:
  requestGas_typed context params campaign =
    if checkTypes params [TypeInt; TypeInt] ∧
       get_campaign_phase campaign = PhaseTasks
    then
       let
         taskId = scToInt (HD   params);
         amount = scToInt (EL 1 params);

         task = p_get_campaign_task_by_task_id campaign taskId;
         gasPrice = calculateLastPrice campaign;
         requestTime = get_context_blockNum context;
       in case task, gasPrice of
          | NONE, _ => NEX_Task
          | _, NONE => NO_APPROVED_PRICES
          | SOME task, SOME gasPrice =>
              if isSenderCaptain context task ∧
                 (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧ get_task_negotiation task = NegotiationApproved ∧
                 (get_task_taskStatus task = TaskReadyToPerform ∨
                 get_task_taskStatus task = GasRequested)
              then
                 let
                   updated_task = set_task_requestTime (set_task_requestedGas (set_task_totalGas (set_task_taskStatus task GasRequested) ((get_task_totalGas task) + amount)) amount) requestTime;
                 in
                    Some $ SCCampaign $ p_update_Campaign_tasks campaign updated_task taskId
              else
                 WRNG_COND_011
    else
       WRNG_COND_012
End

(* 20+ *)
Definition completePayment_typed_def:
  completePayment_typed context params campaign =
  if checkTypes params [TypeInt] ∧
     get_campaign_phase campaign = PhaseTasks ∧
     (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
     approvedPriceExists campaign
  then
    let
      paymentId = scToInt (HD params);
      paymentTime = (get_context_blockNum context);

      paymentOrder = p_get_paymentOrder_by_id campaign paymentId;

    in case paymentOrder of
       | SOME paymentOrder =>
           let
             taskId = (get_PaymentOrder_taskId paymentOrder);
             task = (p_get_campaign_task_by_task_id campaign taskId);
           in (case task of
               | SOME task =>
                      if get_task_negotiation task ≠ NegotiationApproved then NOT_APPROVED_task else
                      if (get_task_taskStatus task) = Confirmed
                      then
                       Some $ SCCampaign
                            (p_update_Campaign_tasks
                             (p_update_Campaign_paymentOrders campaign (set_PaymentOrder_paymentStatus paymentOrder PaymentCompleted) paymentId)
                             (set_task_taskStatus task TaskCompleted)
                             taskId)
                     else Some $ SCCampaign (p_update_Campaign_paymentOrders campaign (set_PaymentOrder_paymentStatus paymentOrder PaymentCompleted) paymentId)
               | NONE => NEX_Task)
              | NONE => NEX_Payment
  else
    WRNG_COND_013
End

(* 21+ *)
Definition performTask_typed_def:
  performTask_typed context params campaign =
    if checkTypes params [TypeInt] ∧
       get_campaign_phase campaign = PhaseTasks ∧
       (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
       approvedPriceExists campaign
    then
       let
         taskId = scToInt (HD params);
         task = p_get_campaign_task_by_task_id campaign taskId;
       in case task of
          | NONE => NEX_Task
          | SOME task =>
              if isSenderWorker context task ∧
                 get_task_taskStatus task = GasRequested
                 (*WRN*) ∧ get_task_negotiation task = NegotiationApproved
              then
                 Some $ SCCampaign (p_update_Campaign_tasks campaign (set_task_taskStatus task Performing) taskId)
              else
                 WRNG_COND_014
    else
       WRNG_COND_013
End

(* 22+ *)
Definition completeTask_typed_def:
completeTask_typed context params campaign =
   if checkTypes params [TypeInt; TypeInt] ∧
      get_campaign_phase campaign = PhaseTasks ∧
       (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
      approvedPriceExists campaign
   then
       let
         taskId = scToInt (HD params);
         suppliedGas = scToInt (EL 1 params);
         task = p_get_campaign_task_by_task_id campaign taskId;
         suppliedTime = (get_context_blockNum context);
       in case task of
          | NONE => NEX_Task
          | SOME task =>
              if isSenderWorker context task ∧
                 get_task_taskStatus task = Performing
                 ∧ get_task_negotiation task = NegotiationApproved
              then
                 Some $ (SCCampaign (p_update_Campaign_tasks campaign
                                                    (set_task_suppliedGas
                                                        (set_task_suppliedTime task suppliedTime)
                                                        suppliedGas)
                                                taskId))
              else
                 WRNG_COND_015
    else
       WRNG_COND_016
End

(* 23 *)
Definition confirmTask_def:
(* Context -> Campaign -> num -> num -> (SCValue OptionErr)  *)
confirmTask context campaign taskId suppliedGas =
  if ¬(
    get_campaign_phase campaign = PhaseTasks ∧
    (*WRN*)get_agreement_negotiation $ get_campaign_agreement campaign = NegotiationApproved ∧
    approvedPriceExists campaign
  ) then NOT_ALLOWED_action else
  let
    sender = (get_context_msgSender context);
    suppliedTime = (get_context_blockNum context);
    (*task = THE (p_get_campaign_task_by_task_id campaign taskId);*)
  in
  case (p_get_campaign_task_by_task_id campaign taskId) of
    NONE => NEX_Task
  | SOME task =>
  if get_task_negotiation task ≠ NegotiationApproved then NOT_APPROVED_task (*WRN*) else
  let
    totalGas = (get_task_totalGas task);
    price = get_priceChange_price $ THE $ calculateLastPrice campaign;
    add_payment_order campaign order =
      set_campaign_paymentOrders campaign (( get_campaign_paymentOrders campaign) ++ [order]);
    direction =
      case ( (get_task_suppliedGas task) < (get_task_totalGas task), (get_task_paymentType task) = Pre) of
        (T,T) => F
      | (T,F) => T
      | (F,_) => T;
    phas = get_task_paymentType task;
    make_payment_order =
      case phas of
      | Pre     => (PaymentOrder (price * if suppliedGas < totalGas
                                    then totalGas - suppliedGas
                                    else suppliedGas - totalGas) 0 0 taskId WaitingForPayment direction)
      | Post    => (PaymentOrder (suppliedGas * price) 0 0 taskId WaitingForPayment direction)
      | Delayed => (PaymentOrder (suppliedGas * price) (get_task_paymentTime task) 0 taskId WaitingForPayment direction);
  in
  case (sender = get_person_id $ get_task_captain task, get_task_taskStatus task = Performing) of
    (T, T) => if (suppliedGas = totalGas ∧ phas = Pre) then Some (SCCampaign
                   (p_update_Campaign_tasks campaign (set_task_taskStatus task TaskCompleted) taskId)
                 )
                 else  Some (SCCampaign (add_payment_order
                             (p_update_Campaign_tasks campaign (set_task_taskStatus task Confirmed) taskId)
                                                (make_payment_order)))
  | (F, _) => ONLY_Captain
  | (T, F) => NO_GAS_REQUESTS
End
(* TODO: unite all definitions of this part *)


Definition confirmTask_typed_def:
(* Context -> (SCValue list) -> Campaign -> (SCValue OptionErr)  *)
confirmTask_typed context params campaign =
  if ¬(checkTypes params [TypeInt; TypeInt]) then
    BAD_TYPE
  else
    let
       taskId = scToInt (HD params);
       suppliedGas = scToInt (EL 1 params);
    in
       confirmTask context campaign taskId suppliedGas
End

Definition constructor_helper_def:
  constructor_helper (customer_id:num) (customer_name:string) (supplier_id:num)
    (supplier_name:string) (agreement_details:string) (bank_addr:num) =
  let
    pc = (Person customer_id customer_name);
    ps = (Person supplier_id supplier_name);
    ad = (AgreementDetails agreement_details bank_addr);
    ag = (Agreement WaitingSupplier pc ps ad);
  in
    (Campaign ag [] WaitingCustomer [] PhaseAgreement [])
End

(*MOREFUNCS --------------------------------------------------------------------- *)
Definition constructor_def:
  constructor context params =
  if  ¬(checkTypes params [TypeInt; TypeString; TypeInt; TypeString; TypeString; TypeInt]) then BAD_TYPE else
  let
    customer_id         = scToInt    (HD   params);
    customer_name       = scToString (EL 1 params);
    supplier_id         = scToInt    (EL 2 params);
    supplier_name       = scToString (EL 3 params);
    agreement_details   = scToString (EL 4 params);
    bank_addr           = scToInt    (EL 5 params);
  in
    Some $ SCCampaign $ constructor_helper
      customer_id customer_name supplier_id supplier_name agreement_details bank_addr
End

val _ = map type_of [``getAgreement_typed``, ``rejectAgreement_typed``, ``approveAgreement_typed``, ``changeAgreement_typed``, ``getPriceChangeWithNumber_typed``, ``getPriceChangesLength_typed``, ``rejectPrice_typed``, ``approvePrice_typed``, ``declinePrice_typed``, ``createPriceChange_typed``, ``getTask_typed``, ``approveTask_typed``, ``rejectTask_typed``, ``acceptTask_typed``, ``removeTask_typed``, ``addTask_typed``, ``readyToPerformTask_typed``, ``requestGas_typed``, ``completePayment_typed``, ``performTask_typed``, ``completeTask_typed``, ``confirmTask_typed``];

Definition chooseFunction_def:
chooseFunction (f:num)  =
    case (f : num) of
      2 => SOME getAgreement_typed
    | 3 => SOME rejectAgreement_typed
    | 4 => SOME approveAgreement_typed
    | 5 => SOME changeAgreement_typed
    | 6 => SOME getPriceChangeWithNumber_typed
    | 7 => SOME getPriceChangesLength_typed
    | 8 => SOME rejectPrice_typed
    | 9 => SOME approvePrice_typed
    | 10 => SOME declinePrice_typed
    | 11 => SOME createPriceChange_typed
    | 12 => SOME getTask_typed
    | 13 => SOME approveTask_typed
    | 14 => SOME rejectTask_typed
    | 15 => SOME acceptTask_typed
    | 17 => SOME addTask_typed
    | 18 => SOME readyToPerformTask_typed
    | 19 => SOME requestGas_typed
    | 20 => SOME completePayment_typed
    | 21 => SOME performTask_typed
    | 22 => SOME completeTask_typed
    | 23 => SOME confirmTask_typed
    |  _ => NONE
End

Definition execute_def:
execute f context (params:SCvalue list) campaign =
  case (chooseFunction f) of
    SOME func => func context params campaign
  | NONE      => NEX_function
End

Definition scReceive_def:
  scReceive chain ccc campaign data = execute (get_functionSignature data) (build_context (take_address (get_msgSender ccc)) (get_blockNum chain)) (get_params data) campaign 
End

Definition scInit_def:
  scInit (chain : Chain) (ccc : ContractCallContext) (setup : Setup) = constructor (build_context (take_address (get_msgSender ccc)) (get_blockNum chain)) (get_setupparams setup)
End

Definition sc1_def:
  sc1 = <| init := scInit; receive := scReceive|>
End

Definition status_numeration_def:
  status_numeration TaskNotAccepted = 0n ∧
  status_numeration TaskAccepted = 1 ∧
  status_numeration TaskReadyToPerform = 2 ∧
  status_numeration GasRequested = 3 ∧
  status_numeration Performing = 4 ∧
  status_numeration Confirmed = 5 ∧
  status_numeration TaskCompleted = 6
End


Theorem not_decreasing_after_2:
    ∀context params s1 s2 t1 t2 taskId.
    SOME s2 = get_campaign(getAgreement_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [getAgreement_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_agreement_def] >> FULL_SIMP_TAC std_ss [get_agreement_supplier_def, get_agreement_customer_def] >> FULL_SIMP_TAC std_ss [get_context_msgSender_def, get_person_id_def] >> 
    Cases_on ‘context.msgSender = s1.agreement.customer.id’ >> FULL_SIMP_TAC std_ss [get_campaign_def] >> rw [] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >> FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >> 
    Cases_on ‘context.msgSender = s1.agreement.supplier.id’ >> FULL_SIMP_TAC std_ss [get_campaign_def] >> rw [] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >> FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >> 
    FULL_SIMP_TAC std_ss [] >> FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem not_decreasing_after_3:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(rejectAgreement_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [rejectAgreement_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_agreement_def] >>
    FULL_SIMP_TAC std_ss [get_agreement_negotiation_def, get_context_msgSender_def, get_agreement_supplier_def, get_person_id_def, get_campaign_phase_def, get_campaign_negotiation_def] >>
    Cases_on ‘s1.agreement.negotiation ≠ WaitingSupplier’ >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on ‘context.msgSender ≠ s1.agreement.supplier.id’ >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on ‘s1.phase ≠ PhaseAgreement’ >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on ‘s1.negotiation ≠ WaitingSupplier’ >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >> FULL_SIMP_TAC (srw_ss()) [set_agreement_negotiation_def] >> 
    FULL_SIMP_TAC (srw_ss()) [set_campaign_agreement_def] >> FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >> rw[] >> FULL_SIMP_TAC (srw_ss()) [p_get_campaign_task_by_task_id_def] >> FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >> FULL_SIMP_TAC (srw_ss()) [get_task_id_def] >> FULL_SIMP_TAC (srw_ss()) [FIND_def] >> FULL_SIMP_TAC (srw_ss()) [INDEX_FIND_def]
QED

Theorem not_decreasing_after_4:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(approveAgreement_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [approveAgreement_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_agreement_def,
    get_campaign_negotiation_def, get_campaign_phase_def, get_agreement_supplier_def,
    get_person_id_def, get_context_msgSender_def, get_agreement_negotiation_def] >>
    Cases_on `s1.agreement.negotiation ≠ WaitingSupplier` >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `context.msgSender ≠ s1.agreement.supplier.id` >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `s1.negotiation ≠ WaitingSupplier` >> FULL_SIMP_TAC std_ss const_defs >>
    Cases_on `s1.phase ≠ PhaseAgreement` >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `s1.negotiation ≠ WaitingSupplier` >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >> FULL_SIMP_TAC std_ss [FIND_def] >>
    FULL_SIMP_TAC std_ss [INDEX_FIND_def]
QED

Theorem not_decreasing_after_5:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(changeAgreement_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [changeAgreement_typed_def, changeAgreement_def] >> FULL_SIMP_TAC std_ss [get_campaign_agreement_def,
    get_campaign_negotiation_def, get_campaign_phase_def, get_agreement_supplier_def, get_person_id_def, 
    get_context_msgSender_def, get_agreement_negotiation_def, set_agreement_negotiation_def, set_agreement_details_def, 
    set_campaign_agreement_def, set_campaign_phase_def] >>
    Cases_on `(¬checkTypes params [TypeString; TypeInt])` >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >>
    Cases_on `s1.agreement.negotiation = NegotiationApproved` >>  FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >>
    Cases_on `context.msgSender ≠ s1.agreement.supplier.id` >>  FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >>
    Cases_on `s1.phase ≠ PhaseAgreement` >>  FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `s1.negotiation ≠ WaitingCustomer` >>  FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >>
    FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >> rw[] >> FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def]
QED

Theorem not_decreasing_after_6:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(getPriceChangeWithNumber_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >>  fs [getPriceChangeWithNumber_typed_def] >> 
    FULL_SIMP_TAC std_ss [get_campaign_agreement_def, get_campaign_priceChanges_def] >>
    Cases_on `checkTypes params [TypeInt] ∧ isSenderCustomer context s1 ∧
             ¬NULL s1.priceChanges` >> rw[] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >> FULL_SIMP_TAC std_ss const_defs >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> FULL_SIMP_TAC std_ss const_defs >>
    FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem not_decreasing_after_7:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(getPriceChangesLength_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [getPriceChangesLength_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def] >>
    Cases_on `isSenderCustomer context s1 ∧ ¬NULL s1.priceChanges` >> FULL_SIMP_TAC std_ss const_defs >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC std_ss const_defs >> rw[] >>  FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_def]
QED


val DE_MORGAN_THM1 = prove
  (``!x y. ~(x /\ y) <=> (~x \/ ~y)``,
   tautLib.TAUT_TAC);

val ERR = mk_HOL_ERR "Tactic"

fun USE_LAST_HYP (fu:term->tactic) : tactic =
  (fn x as (asl:term list, w:term) =>
  (case asl of
   he :: ta => fu he
   | _ => raise ERR "USE_LAST_HYP" "there are no hypotheses"
  ) x)

val FOR_ALL_HYP = REPEAT o USE_LAST_HYP

val UNDISCH_LAST = USE_LAST_HYP UNDISCH_TAC

val UNDISCH_ALL = FOR_ALL_HYP UNDISCH_TAC

val SYM_TAC : tactic = irule EQ_SYM


Theorem not_decreasing_after_8:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(rejectPrice_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >>  fs [rejectPrice_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def, 
    get_agreement_negotiation_def, get_campaign_phase_def, get_priceChange_negotiation_def, 
    get_campaign_agreement_def, set_priceChange_negotiation_def, set_campaign_priceChanges_def] >>
    FULL_SIMP_TAC (srw_ss()) const_defs >> 
    Cases_on `isSenderCustomer context s1 ∧ s1.phase = PhaseTasks ∧
             ¬NULL s1.priceChanges ∧
             s1.agreement.negotiation = NegotiationApproved ∧
             (HD s1.priceChanges).negotiation = WaitingCustomer` >>
    UNDISCH_LAST >> REWRITE_TAC [DE_MORGAN_THM1] >> rpt STRIP_TAC >>
    REWRITE_TAC [] >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem not_decreasing_after_9:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(approvePrice_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [approvePrice_typed_def] >>  FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def] >>
    FULL_SIMP_TAC std_ss [get_agreement_negotiation_def, get_campaign_phase_def, get_priceChange_negotiation_def,
    get_campaign_agreement_def, set_priceChange_negotiation_def, set_campaign_priceChanges_def] >>
    Cases_on `isSenderCustomer context s1 ∧ s1.phase = PhaseTasks ∧
             ¬NULL s1.priceChanges ∧
             s1.agreement.negotiation = NegotiationApproved ∧
             (HD s1.priceChanges).negotiation = WaitingCustomer` >>
    UNDISCH_LAST >> REWRITE_TAC [DE_MORGAN_THM1] >> rpt STRIP_TAC >>   
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem not_decreasing_after_10:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(declinePrice_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [declinePrice_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def,
    get_agreement_negotiation_def, get_campaign_phase_def, get_priceChange_negotiation_def,
    get_campaign_agreement_def, set_campaign_phase_def] >>
    Cases_on `isSenderCustomer context s1 ∧ s1.phase = PhaseTasks ∧
             ¬NULL s1.priceChanges ∧
             s1.agreement.negotiation = NegotiationApproved ∧
             (HD s1.priceChanges).negotiation = WaitingCustomer` >>
    UNDISCH_LAST >> REWRITE_TAC [DE_MORGAN_THM1] >> rpt STRIP_TAC >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem not_decreasing_after_11:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(createPriceChange_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [createPriceChange_typed_def] >> fs [createPriceChange_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def, get_agreement_negotiation_def, 
    get_campaign_phase_def, get_priceChange_negotiation_def, get_campaign_agreement_def, 
    p_add_priceChange_in_Campaign_def, set_campaign_priceChanges_def, get_campaign_priceChanges_def] >>
    Cases_on `checkTypes params [TypeInt; TypeInt]` >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `isSenderSupplier context s1 ∧ s1.phase = PhaseTasks ∧
             ¬NULL s1.priceChanges ∧
             ((HD s1.priceChanges).negotiation = NegotiationApproved ∨
              (HD s1.priceChanges).negotiation = NegotiationRejected) ∧
             s1.agreement.negotiation = NegotiationApproved` >>
    UNDISCH_LAST >> REWRITE_TAC [DE_MORGAN_THM1] >> rpt STRIP_TAC >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem not_decreasing_after_12:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(getTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [getTask_typed_def] >> FULL_SIMP_TAC std_ss [get_context_msgSender_def,
    get_person_id_def, get_agreement_customer_def, get_agreement_supplier_def,
    get_context_msgSender_def, get_campaign_tasks_def] >>
    FULL_SIMP_TAC (srw_ss()) const_defs >>
    Cases_on `params` >> FULL_SIMP_TAC (srw_ss()) [] >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `h` >> fs [] >> 
    Cases_on `t` >> FULL_SIMP_TAC (srw_ss()) [] >>
    FULL_SIMP_TAC std_ss [p_get_task_index_by_id_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_agreement_def] >>
    Cases_on `INDEX_FIND 0 (λx. get_task_id x = n) s1.tasks` >>
    FULL_SIMP_TAC (srw_ss())[] >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) [] >>
    Cases_on `context.msgSender = (s1.agreement :> Agreement_supplier).id ∨
             context.msgSender = (s1.agreement :> Agreement_customer).id ` >>
    FULL_SIMP_TAC (srw_ss())[] >> FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >> rw [] >>
    FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >> rw [] >>
    FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    rpt (FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >> rw [])
QED 


Theorem FIND_then_MEM:
∀t P l. (SOME t = FIND P l) ==> (P t /\ MEM t l)
Proof
  rpt gen_tac >>
  Induct_on ‘l’
  >| [
    simp [mllistTheory.FIND_thm]
  ,
    simp [mllistTheory.FIND_thm] >>
    rw []
  ]
QED

Theorem taskId_MAP_unique:
maplst = MAP (λu. if u.taskID = taskId then x with taskID := taskId else u) tasks
==>
MEM a maplst
==>
MEM b maplst
==>
a.taskID = taskId
==>
b.taskID = taskId
==>
a = b
Proof
  rw [] >>
  fs [listTheory.MEM_MAP] >>
  Cases_on ‘(u :Task).taskID = (b :Task).taskID’
  >| [
    Cases_on ‘(u' :Task).taskID = (b :Task).taskID’
    >| [
      fs []
    ,
      UNDISCH_ALL >>
      rw []
    ]
  ,
    fs  [] >>
    Cases_on ‘(u' :Task).taskID = (b :Task).taskID’
    >| [
      UNDISCH_ALL >>
      fs []
    ,
      UNDISCH_ALL >>
      fs []
    ]
  ]
QED


Theorem FIND_MAP_sameId:
    !t x taskId tasks.
    SOME t = FIND (λy. y.taskID = taskId) (MAP (λu. if u.taskID = taskId then (x with taskID := taskId) else u) tasks) ==>
    t = (x with taskID := taskId)
Proof
  rpt gen_tac >>
  DISCH_TAC >>
  assume_tac (SPECL [“(t :Task)”, “(λ(y :Task). y.taskID = (taskId :num))”, “(MAP (λ(u :Task).if u.taskID = taskId then (x :Task) with taskID := taskId else u) (tasks :Task list))”] (INST_TYPE [alpha |-> ``:Task``] FIND_then_MEM)) >>
  UNDISCH_ALL >>
  rw [] >>
  fs [listTheory.MEM_MAP] >>
  ntac 2 UNDISCH_LAST >>
  (Cases_on ‘(u :Task).taskID = t.taskID’ >> simp []) >>
  rw []
QED


Theorem p_update_Campaign_tasks_correctness1:
    !s1 s2 t taskId x.
    s2 = p_update_Campaign_tasks s1 x taskId /\ 
    SOME t = p_get_campaign_task_by_task_id s2 taskId ==> get_task_taskStatus t = get_task_taskStatus x
Proof
    rpt STRIP_TAC >> rw [get_task_taskStatus_def] >>
    fs [p_update_Campaign_tasks_def, get_campaign_tasks_def, get_task_id_def, set_campaign_tasks_def, p_get_campaign_task_by_task_id_def, UPDATE_BY_ID_def] >>
    STRIP_ASSUME_TAC FIND_MAP_sameId >> first_x_assum (qspecl_then [‘t’, ‘x’, ‘taskId’, ‘s1.tasks’] mp_tac) >> rw []
QED

Theorem lemma_p_update_Campaign_tasks_correctness4:
∀(tasks:Task list).
(id1 :num) ≠ (id2 :num) ==>
        FIND (λ(x :Task). x.taskID = (id1 :num)) tasks =
        FIND (λ(x :Task). x.taskID = id1)
          (MAP
             (λ(t :Task).
                  if t.taskID = (id2 :num) then (x :Task) with taskID := id2
                  else t) tasks)
Proof
  (Induct_on ‘tasks’ >> simp []) >>
  (rw [mllistTheory.FIND_thm] >> fs [])
QED

Theorem p_update_Campaign_tasks_correctness4:
    !s1 x id1 id2. 
    id1 ≠ id2 ==>
    p_get_campaign_task_by_task_id s1 id1 = p_get_campaign_task_by_task_id (p_update_Campaign_tasks s1 x id2) id1
Proof
    rpt STRIP_TAC >> rw [get_task_taskStatus_def] >>
    fs [p_update_Campaign_tasks_def, get_campaign_tasks_def, get_task_id_def, set_campaign_tasks_def, p_get_campaign_task_by_task_id_def, UPDATE_BY_ID_def] >>
    assume_tac (SPECL [“(s1.tasks)”] lemma_p_update_Campaign_tasks_correctness4) >>
    rw []
QED

Theorem p_update_Campaign_tasks_correctness2:
    !s1 s2 t1 t2 x id1 id2. 
    id1 ≠ id2 /\
    SOME t1 = p_get_campaign_task_by_task_id s1 id1 /\ 
    SOME t2 = p_get_campaign_task_by_task_id s2 id1 /\ 
    s2 = p_update_Campaign_tasks s1 x id2
    ==> get_task_taskStatus t2 = get_task_taskStatus t1
Proof
    rpt STRIP_TAC >> rw [] >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> first_x_assum (qspecl_then [‘s1’, ‘x’, ‘id1’, ‘id2’] mp_tac) >> 
    FULL_SIMP_TAC std_ss [p_update_Campaign_tasks_def, get_campaign_tasks_def, get_task_id_def, set_campaign_tasks_def, p_get_campaign_task_by_task_id_def, UPDATE_BY_ID_def, FIND_def, INDEX_FIND_def] >> 
    rw [] >> fs [] 
QED

Theorem not_decreasing_after_13:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(approveTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [approveTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> 
    Cases_on `get_context_msgSender context = get_person_id (get_agreement_supplier (get_campaign_agreement s1)) ∧ 
    get_task_negotiation x = NegotiationApproved` >-
    (fs [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t2’, ‘scToInt (HD params)’, ‘(set_task_negotiation x NegotiationApproved)’] mp_tac) >> 
    fs [] >> rw [set_task_negotiation_def, get_task_taskStatus_def, status_numeration_def]) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, 
    ‘(set_task_negotiation x NegotiationApproved)’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw []) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem not_decreasing_after_14:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(rejectTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [rejectTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> 
    Cases_on `get_context_msgSender context = get_person_id (get_agreement_supplier (get_campaign_agreement s1)) ∧ 
    get_task_negotiation x = NegotiationApproved` >-
    (fs [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t2’, ‘scToInt (HD params)’, ‘(set_task_negotiation x NegotiationRejected)’] mp_tac) >> 
    fs [] >> rw [set_task_negotiation_def, get_task_taskStatus_def, status_numeration_def]) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, 
    ‘(set_task_negotiation x NegotiationRejected)’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw []) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem not_decreasing_after_15:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(acceptTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [acceptTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> 
    Cases_on `get_context_msgSender context = get_person_id (get_agreement_supplier (get_campaign_agreement s1)) ∧ 
    get_task_negotiation x = NegotiationApproved ∧ get_task_taskStatus x = TaskNotAccepted` >-
    (fs [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (fs [] >> rw [status_numeration_def]) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, 
    ‘(set_task_taskStatus x TaskAccepted)’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw []) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem leq_max_list:
  ∀(x:num). ∀(l:num list). (MEM x l) ⇒ (x ≤ (FOLDR MAX 0 l))
Proof
  Induct_on `l`
  >| [
    simp []
  ,
    rw [] >|
    [
      simp []
    ,
      DISJ2_TAC >>
      first_x_assum (qspecl_then [‘x’] mp_tac) >>
      simp []
    ]
  ]
QED

Theorem maxsucnel:
!l. ¬MEM (SUC (FOLDR MAX 0 l)) l
Proof
  STRIP_TAC >> irule boolTheory.MONO_NOT >>
  exists_tac `` (SUC (FOLDR MAX 0 l)) ≤ (FOLDR MAX 0 l)`` >>
  conj_tac
  >| [
    rw []
  ,
    simp [leq_max_list]
  ]
QED

Theorem indexOf_none:
    INDEX_OF (SUC (FOLDR MAX 0 (MAP Task_taskID t))) (MAP Task_taskID t) = NONE
Proof
    STRIP_ASSUME_TAC maxsucnel >> first_x_assum (qspecl_then [‘(MAP Task_taskID t)’] mp_tac) >> rw [INDEX_OF_eq_NONE]
QED

Theorem indexfind_none:
    INDEX_FIND 0 (\x. x.taskID = SUC (FOLDR MAX 0 (MAP Task_taskID t))) t = NONE
Proof
    STRIP_ASSUME_TAC indexOf_none >> fs [INDEX_OF_def] >> cheat
QED

Theorem index_find_snd:
    !P l q (r : Task). INDEX_FIND 0 P l = SOME (q, r) ==> INDEX_FIND 1 P l = SOME (SUC q, r)
Proof
    rpt STRIP_TAC >> fs [Once INDEX_FIND_add] >> rw [ADD1] >> 
    Cases_on `z` >> rw [] >>
    fs [INDEX_FIND_def] >>
    fs [INDEX_FIND_def]
QED

Theorem index_find_snd1:
    !P l (z : num # Task) z'. INDEX_FIND 0 P l = SOME z ==> ∃z'. INDEX_FIND 1 P l = SOME z' 
Proof
    rpt STRIP_TAC >> Cases_on `z` >> Q.EXISTS_TAC `(SUC q, r)` >> fs [index_find_snd] 
QED

Theorem index_find_snd2:
    !P l (z : num # Task) z'. INDEX_FIND 0 P l = SOME z /\
    INDEX_FIND 1 P l = SOME z' ==> SND z = SND z' 
Proof
    rpt STRIP_TAC >> Cases_on `z` >> 
    STRIP_ASSUME_TAC index_find_snd >> 
    first_x_assum (qspecl_then [‘P’, ‘l’, ‘q’, ‘r’] mp_tac) >>
    rw []
QED

Theorem not_decreasing_after_17:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(addTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [addTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt; TypeString; TypeInt; TypeString; TypeInt; TypePaymentType] ∧ 
    isSenderCustomer context s1 ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >- 
    (fs [get_campaign_def, get_campaign_tasks_def, TASK_HASH_DEF, p_get_campaign_task_by_task_id_def, FIND_def] >> 
    PURE_REWRITE_TAC [get_task_taskStatus_def, status_numeration_def] >> 
    fs [get_campaign_tasks_def, INDEX_FIND_def, get_task_id_def, p_add_task_in_Campaign_def, set_campaign_tasks_def] >> 
    Cases_on `SUC (FOLDR MAX 0 (MAP Task_taskID s1.tasks)) = taskId` >- 
    (fs [] >> rw[status_numeration_def] >> fs [indexfind_none]) >> 
    rw [] >> fs [INDEX_FIND_def] >> 
    STRIP_ASSUME_TAC index_find_snd2 >> 
    first_x_assum (qspecl_then [‘(λx. x.taskID = taskId)’, ‘s1.tasks’, ‘z’, ‘z'’] mp_tac) >> fs []) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED


Theorem not_decreasing_after_18:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(readyToPerformTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [readyToPerformTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >- 
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >- 
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> 
    Cases_on `isSenderWorker context x ∧ get_task_negotiation x = NegotiationApproved ∧ 
    get_task_taskStatus x = TaskAccepted` >- 
    (FULL_SIMP_TAC std_ss [get_campaign_def, set_task_taskStatus_def] >> 
    Cases_on `taskId = scToInt (HD params)` >- 
    (fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t2’, ‘scToInt (HD params)’, 
    ‘(x with taskStatus := TaskReadyToPerform)’] mp_tac) >> 
    rw [status_numeration_def, get_task_taskStatus_def]) >>
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, 
    ‘(x with taskStatus := TaskReadyToPerform)’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> 
    rw []) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem not_decreasing_after_19:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(requestGas_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [requestGas_typed_def] >> 
    Cases_on `checkTypes params [TypeInt; TypeInt] ∧ get_campaign_phase s1 = PhaseTasks` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `calculateLastPrice s1` >-
    (fs const_defs >> fs [get_campaign_def]) >>
    fs [] >> 
    Cases_on `isSenderCaptain context x ∧ get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ 
    get_task_negotiation x = NegotiationApproved ∧ get_task_taskStatus x = TaskReadyToPerform` >-
    (fs [] >> FULL_SIMP_TAC std_ss [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t2’, ‘scToInt (HD params)’, 
    ‘(set_task_requestTime (set_task_requestedGas 
    (set_task_totalGas (set_task_taskStatus x GasRequested) 
    (get_task_totalGas x + scToInt (EL 1 params))) (scToInt (EL 1 params))) (get_context_blockNum context))’] mp_tac) >> 
    rw [status_numeration_def, get_task_taskStatus_def, set_task_requestTime_def, set_task_requestedGas_def, 
    set_task_totalGas_def, set_task_taskStatus_def, get_task_totalGas_def, get_context_blockNum_def]) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, 
    ‘(set_task_requestTime (set_task_requestedGas (set_task_totalGas 
    (set_task_taskStatus x GasRequested) (get_task_totalGas x + scToInt (EL 1 params))) 
    (scToInt (EL 1 params))) 
    (get_context_blockNum context))’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw []) >>
    Cases_on `isSenderCaptain context x ∧ get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ 
    get_task_negotiation x = NegotiationApproved ∧ get_task_taskStatus x = GasRequested` >-
    (fs [] >> FULL_SIMP_TAC std_ss [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t2’, ‘scToInt (HD params)’, 
    ‘(set_task_requestTime (set_task_requestedGas (set_task_totalGas 
    (set_task_taskStatus x GasRequested) (get_task_totalGas x + scToInt (EL 1 params))) 
    (scToInt (EL 1 params))) (get_context_blockNum context))’] mp_tac) >> 
    rw [status_numeration_def, get_task_taskStatus_def, set_task_requestTime_def, set_task_requestedGas_def, 
    set_task_totalGas_def, set_task_taskStatus_def, get_task_totalGas_def, get_context_blockNum_def]) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, 
    ‘(set_task_requestTime (set_task_requestedGas (set_task_totalGas 
    (set_task_taskStatus x GasRequested) (get_task_totalGas x + scToInt (EL 1 params))) 
    (scToInt (EL 1 params))) (get_context_blockNum context))’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw []) >> 
    FULL_SIMP_TAC pure_ss [LEFT_AND_OVER_OR] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem p_update_Campaign_paymentOrders_correctness:
    !s1 x id n.
    p_get_campaign_task_by_task_id (p_update_Campaign_paymentOrders s1 x n) id =
    p_get_campaign_task_by_task_id s1 id
Proof
    rpt STRIP_TAC >> 
    rw [p_update_Campaign_paymentOrders_def , p_get_campaign_task_by_task_id_def, get_campaign_paymentOrders_def, set_campaign_paymentOrders_def, get_campaign_tasks_def]
QED

Theorem not_decreasing_after_20:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(completePayment_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [completePayment_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_paymentOrder_by_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on ` p_get_campaign_task_by_task_id s1 (get_PaymentOrder_taskId x)` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_task_negotiation x' ≠ NegotiationApproved` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_task_taskStatus x' = Confirmed` >-
    (fs [get_campaign_def] >> Cases_on `get_PaymentOrder_taskId x = taskId` >-
    (fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘(p_update_Campaign_paymentOrders s1 
    (set_PaymentOrder_paymentStatus x PaymentCompleted) (scToInt (HD params)))’, ‘s2’, ‘t2’, ‘taskId’, 
    ‘(set_task_taskStatus x' TaskCompleted)’] mp_tac) >> 
    rw [set_task_taskStatus_def, get_task_taskStatus_def, status_numeration_def]) >> 
    STRIP_ASSUME_TAC p_update_Campaign_paymentOrders_correctness >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_PaymentOrder_paymentStatus x PaymentCompleted)’, 
    ‘taskId’, ‘(scToInt (HD params))’] mp_tac) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘(p_update_Campaign_paymentOrders s1 
    (set_PaymentOrder_paymentStatus x PaymentCompleted) (scToInt (HD params)))’, ‘s2’, ‘t1’, ‘t2’, 
    ‘(set_task_taskStatus x' TaskCompleted)’, ‘taskId’, ‘(get_PaymentOrder_taskId x)’] mp_tac) >>
    rw []) >> FULL_SIMP_TAC std_ss [get_campaign_def] >> rw [] >>
    STRIP_ASSUME_TAC p_update_Campaign_paymentOrders_correctness >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_PaymentOrder_paymentStatus x PaymentCompleted)’, ‘taskId’, 
    ‘(scToInt (HD params))’] mp_tac) >> 
    rw [] >> FULL_SIMP_TAC pure_ss [] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def, FIND_def, INDEX_FIND_def] >>
    fs [get_campaign_tasks_def, get_task_id_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem not_decreasing_after_21:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(performTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [performTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `isSenderWorker context x ∧ get_task_taskStatus x = GasRequested ∧ 
    get_task_negotiation x = NegotiationApproved` >-
    (fs [] >> FULL_SIMP_TAC std_ss [get_campaign_def, set_task_taskStatus_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t2’, ‘scToInt (HD params)’, 
    ‘(x with taskStatus := Performing)’] mp_tac) >> 
    rw [status_numeration_def, get_task_taskStatus_def]) >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘(x with taskStatus := Performing)’, ‘taskId’, 
    ‘scToInt (HD params)’] mp_tac) >> rw []) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem not_decreasing_after_22:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(completeTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [completeTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt; TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `isSenderWorker context x ∧ get_task_taskStatus x = Performing ∧ 
    get_task_negotiation x = NegotiationApproved` >-
    (fs [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t2’, ‘scToInt (HD params)’, 
    ‘(set_task_suppliedGas (set_task_suppliedTime x (get_context_blockNum context)) (scToInt (EL 1 params)))’] mp_tac) >> 
    fs [get_task_taskStatus_def] >> rw [status_numeration_def, get_task_taskStatus_def, 
    set_task_suppliedGas_def, set_task_suppliedTime_def, get_context_blockNum_def]) >>
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, 
    ‘(set_task_suppliedGas (set_task_suppliedTime x (get_context_blockNum context)) (scToInt (EL 1 params)))’, 
    ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw []) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >>
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem set_campaign_paymentOrders_correctness:
    !s1 x id.
    p_get_campaign_task_by_task_id (set_campaign_paymentOrders s1 x) id =
    p_get_campaign_task_by_task_id s1 id
Proof
    rpt STRIP_TAC >> rw [set_campaign_paymentOrders_def, p_get_campaign_task_by_task_id_def, get_campaign_tasks_def]
QED

Theorem p_update_Campaign_tasks_correctness3:
    !s1 t taskId x.
    SOME t = p_get_campaign_task_by_task_id (p_update_Campaign_tasks s1 x taskId) taskId ==> 
    get_task_taskStatus t = get_task_taskStatus x
Proof
    rpt STRIP_TAC >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(p_update_Campaign_tasks s1 x taskId)’, ‘t’, ‘taskId’, ‘x’] mp_tac) >> rw []
QED

Theorem not_decreasing_after_23:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(confirmTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    rpt STRIP_TAC >> fs [confirmTask_typed_def] >> 
    Cases_on `¬checkTypes params [TypeInt; TypeInt]` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [confirmTask_def] >> 
    Cases_on `get_campaign_phase s1 = PhaseTasks ⇒ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ⇒ ¬approvedPriceExists s1` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_task_negotiation x ≠ NegotiationApproved` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_context_msgSender context = get_person_id (get_task_captain x)` >- 
    (fs [] >> Cases_on `get_task_taskStatus x = Performing` >-
    (fs [] >> Cases_on `scToInt (EL 1 params) = get_task_totalGas x ∧ get_task_paymentType x = Pre` >-
    (fs [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >- 
    (fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness1 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t2’, ‘taskId’, ‘(set_task_taskStatus x TaskCompleted)’] mp_tac) >> 
    rw [set_task_taskStatus_def, get_task_taskStatus_def, status_numeration_def]) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘(set_task_taskStatus x TaskCompleted)’, ‘taskId’, 
    ‘scToInt (HD params)’] mp_tac) >> rw []) >> 
    FULL_SIMP_TAC pure_ss [] >> fs [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC set_campaign_paymentOrders_correctness >>
    first_x_assum (qspecl_then [‘(p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed) (scToInt (HD params)))’, 
    ‘(get_campaign_paymentOrders
             (p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed)
                (scToInt (HD params))) ⧺
           [case get_task_paymentType x of
              Pre =>
                PaymentOrder
                  (get_priceChange_price (THE (calculateLastPrice s1)) *
                   if scToInt (EL 1 params) < get_task_totalGas x then
                     get_task_totalGas x − scToInt (EL 1 params)
                   else scToInt (EL 1 params) − get_task_totalGas x) 0 0
                  (scToInt (HD params)) WaitingForPayment
                  (get_task_suppliedGas x < get_task_totalGas x ⇒
                   get_task_paymentType x ≠ Pre)
            | Post =>
              PaymentOrder
                (get_priceChange_price (THE (calculateLastPrice s1)) *
                 scToInt (EL 1 params)) 0 0 (scToInt (HD params))
                WaitingForPayment
                (get_task_suppliedGas x < get_task_totalGas x ⇒
                 get_task_paymentType x ≠ Pre)
            | Delayed =>
              PaymentOrder
                (get_priceChange_price (THE (calculateLastPrice s1)) *
                 scToInt (EL 1 params)) (get_task_paymentTime x) 0
                (scToInt (HD params)) WaitingForPayment
                (get_task_suppliedGas x < get_task_totalGas x ⇒
                 get_task_paymentType x ≠ Pre)])’, ‘taskId’] mp_tac) >> 
    rw [] >> fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness3 >> 
    first_x_assum (qspecl_then [‘s1’, ‘t2’, ‘scToInt (HD params)’, ‘(set_task_taskStatus t1 Confirmed)’] mp_tac) >> 
    rw [status_numeration_def, set_task_taskStatus_def, get_task_taskStatus_def] >>
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness3 >> 
    first_x_assum (qspecl_then [‘s1’, ‘t2’, ‘scToInt (HD params)’, ‘(set_task_taskStatus t1 Confirmed)’] mp_tac) >> 
    fs [] >> rw [status_numeration_def, set_task_taskStatus_def, get_task_taskStatus_def]) >> 
    STRIP_ASSUME_TAC set_campaign_paymentOrders_correctness >>
    first_x_assum (qspecl_then [‘(p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed) (scToInt (HD params)))’, 
    ‘(get_campaign_paymentOrders
             (p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed)
                (scToInt (HD params))) ⧺
           [case get_task_paymentType x of
              Pre =>
                PaymentOrder
                  (get_priceChange_price (THE (calculateLastPrice s1)) *
                   if scToInt (EL 1 params) < get_task_totalGas x then
                     get_task_totalGas x − scToInt (EL 1 params)
                   else scToInt (EL 1 params) − get_task_totalGas x) 0 0
                  (scToInt (HD params)) WaitingForPayment
                  (get_task_suppliedGas x < get_task_totalGas x ⇒
                   get_task_paymentType x ≠ Pre)
            | Post =>
              PaymentOrder
                (get_priceChange_price (THE (calculateLastPrice s1)) *
                 scToInt (EL 1 params)) 0 0 (scToInt (HD params))
                WaitingForPayment
                (get_task_suppliedGas x < get_task_totalGas x ⇒
                 get_task_paymentType x ≠ Pre)
            | Delayed =>
              PaymentOrder
                (get_priceChange_price (THE (calculateLastPrice s1)) *
                 scToInt (EL 1 params)) (get_task_paymentTime x) 0
                (scToInt (HD params)) WaitingForPayment
                (get_task_suppliedGas x < get_task_totalGas x ⇒
                 get_task_paymentType x ≠ Pre)])’, ‘taskId’] mp_tac) >> 
    rw [] >> fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed) (scToInt (HD params))’, 
    ‘t1’, ‘t2’, ‘(set_task_taskStatus x Confirmed)’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> 
    rw [] >> fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness2 >> 
    first_x_assum (qspecl_then [‘s1’, ‘p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed) (scToInt (HD params))’, 
    ‘t1’, ‘t2’, ‘(set_task_taskStatus x Confirmed)’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> 
    rw []) >> fs const_defs >> fs [get_campaign_def]) >> fs const_defs >> fs [get_campaign_def]
QED


Theorem not_decreasing_after_execute:
    ∀f (context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(execute f context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧
    SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ 
    status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
    STRIP_TAC >> FULL_SIMP_TAC std_ss [execute_def] >> Cases_on ‘chooseFunction f’ >> FULL_SIMP_TAC std_ss [] >> FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >> FULL_SIMP_TAC std_ss [chooseFunction_def] >> 
    Cases_on ‘f = 2’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_2] >> FULL_SIMP_TAC std_ss [] >> 
    Cases_on ‘f = 3’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_3] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 4’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_4] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 5’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_5] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 6’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_6] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 7’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_7] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 8’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_8] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 9’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_9] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 10’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_10] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 11’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_11] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 12’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_12] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 13’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_13] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 14’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_14] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 15’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_15] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 17’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_17] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 18’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_18] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 19’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_19] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 20’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_20] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 21’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_21] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 22’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_22] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 23’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [not_decreasing_after_23] >> FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss []
QED


Theorem task_after_2:
    ∀context params s1 s2 t1 taskId.
    SOME s2 = get_campaign (getAgreement_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [getAgreement_typed_def] >> FULL_SIMP_TAC std_ss [ get_context_msgSender_def,
    get_person_id_def,  get_agreement_customer_def, get_campaign_agreement_def, get_context_msgSender_def,
    get_agreement_supplier_def, get_campaign_agreement_def] >>
    Cases_on `context.msgSender = s1.agreement.customer.id` >> fs[] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >> fs[] >>
    FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    Cases_on `context.msgSender = s1.agreement.supplier.id` >> fs[] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >> fs[] >>
    FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC (srw_ss()) const_defs >>  FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem task_after_3:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(rejectAgreement_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [rejectAgreement_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_agreement_def,
    get_campaign_negotiation_def, get_campaign_phase_def, get_agreement_supplier_def, get_person_id_def, 
    get_context_msgSender_def, get_agreement_negotiation_def, set_agreement_negotiation_def, 
    set_campaign_agreement_def] >> FULL_SIMP_TAC (srw_ss()) const_defs >>
    Cases_on `s1.agreement.negotiation ≠ WaitingSupplier` >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    Cases_on `s1.phase ≠ PhaseAgreement` >>   
    Cases_on `context.msgSender ≠ s1.agreement.supplier.id` >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `s1.negotiation ≠ WaitingSupplier` >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `context.msgSender ≠ s1.agreement.supplier.id` >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `context.msgSender ≠ s1.agreement.supplier.id` >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >> FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> rw[] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def]
QED

Theorem task_after_4:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(approveAgreement_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [approveAgreement_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_agreement_def,
    get_campaign_negotiation_def, get_campaign_phase_def, get_agreement_supplier_def,
    get_person_id_def, get_context_msgSender_def, get_agreement_negotiation_def] >>
    Cases_on `s1.agreement.negotiation ≠ WaitingSupplier` >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `context.msgSender ≠ s1.agreement.supplier.id` >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `s1.negotiation ≠ WaitingSupplier` >> FULL_SIMP_TAC std_ss const_defs >>
    Cases_on `s1.phase ≠ PhaseAgreement` >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `s1.negotiation ≠ WaitingSupplier` >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >> FULL_SIMP_TAC std_ss [FIND_def] >>
    FULL_SIMP_TAC std_ss [INDEX_FIND_def]
QED

Theorem task_after_5:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(changeAgreement_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [changeAgreement_typed_def, changeAgreement_def] >> FULL_SIMP_TAC std_ss [get_campaign_agreement_def,
    get_campaign_negotiation_def, get_campaign_phase_def, get_agreement_supplier_def, get_person_id_def, 
    get_context_msgSender_def, get_agreement_negotiation_def, set_agreement_negotiation_def, set_agreement_details_def, 
    set_campaign_agreement_def, set_campaign_phase_def] >>
    Cases_on `(¬checkTypes params [TypeString; TypeInt])` >> FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >>
    Cases_on `s1.agreement.negotiation = NegotiationApproved` >>  FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >>
    Cases_on `context.msgSender ≠ s1.agreement.supplier.id` >>  FULL_SIMP_TAC std_ss const_defs >> 
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >>
    Cases_on `s1.phase ≠ PhaseAgreement` >>  FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `s1.negotiation ≠ WaitingCustomer` >>  FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >>
    FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >> rw[] >> FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def]
QED

Theorem task_after_6:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(getPriceChangeWithNumber_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >>  fs [getPriceChangeWithNumber_typed_def] >> 
    FULL_SIMP_TAC std_ss [get_campaign_agreement_def, get_campaign_priceChanges_def] >>
    Cases_on `checkTypes params [TypeInt] ∧ isSenderCustomer context s1 ∧
             ¬NULL s1.priceChanges` >> rw[] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >> FULL_SIMP_TAC std_ss const_defs >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> FULL_SIMP_TAC std_ss const_defs >>
    FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem task_after_7:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(getPriceChangesLength_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [getPriceChangesLength_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def] >>
    Cases_on `isSenderCustomer context s1 ∧ ¬NULL s1.priceChanges` >> FULL_SIMP_TAC std_ss const_defs >>
    FULL_SIMP_TAC std_ss [get_campaign_def] >> rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC std_ss const_defs >> rw[] >>  FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem task_after_8:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(rejectPrice_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
        rpt STRIP_TAC >>  fs [rejectPrice_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def, 
    get_agreement_negotiation_def, get_campaign_phase_def, get_priceChange_negotiation_def, 
    get_campaign_agreement_def, set_priceChange_negotiation_def, set_campaign_priceChanges_def] >>
    FULL_SIMP_TAC (srw_ss()) const_defs >> 
    Cases_on `isSenderCustomer context s1 ∧ s1.phase = PhaseTasks ∧
             ¬NULL s1.priceChanges ∧
             s1.agreement.negotiation = NegotiationApproved ∧
             (HD s1.priceChanges).negotiation = WaitingCustomer` >>
    UNDISCH_LAST >> REWRITE_TAC [DE_MORGAN_THM1] >> rpt STRIP_TAC >>
    REWRITE_TAC [] >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem task_after_9:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(approvePrice_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [approvePrice_typed_def] >>  FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def] >>
    FULL_SIMP_TAC std_ss [get_agreement_negotiation_def, get_campaign_phase_def, get_priceChange_negotiation_def,
    get_campaign_agreement_def, set_priceChange_negotiation_def, set_campaign_priceChanges_def] >>
    Cases_on `isSenderCustomer context s1 ∧ s1.phase = PhaseTasks ∧
             ¬NULL s1.priceChanges ∧
             s1.agreement.negotiation = NegotiationApproved ∧
             (HD s1.priceChanges).negotiation = WaitingCustomer` >>
    UNDISCH_LAST >> REWRITE_TAC [DE_MORGAN_THM1] >> rpt STRIP_TAC >>   
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem task_after_10:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(declinePrice_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
        rpt STRIP_TAC >> fs [declinePrice_typed_def] >> FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def,
    get_agreement_negotiation_def, get_campaign_phase_def, get_priceChange_negotiation_def,
    get_campaign_agreement_def, set_campaign_phase_def] >>
    Cases_on `isSenderCustomer context s1 ∧ s1.phase = PhaseTasks ∧
             ¬NULL s1.priceChanges ∧
             s1.agreement.negotiation = NegotiationApproved ∧
             (HD s1.priceChanges).negotiation = WaitingCustomer` >>
    UNDISCH_LAST >> REWRITE_TAC [DE_MORGAN_THM1] >> rpt STRIP_TAC >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem task_after_11:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(createPriceChange_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [createPriceChange_typed_def] >> fs [createPriceChange_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_priceChanges_def, get_agreement_negotiation_def, 
    get_campaign_phase_def, get_priceChange_negotiation_def, get_campaign_agreement_def, 
    p_add_priceChange_in_Campaign_def, set_campaign_priceChanges_def, get_campaign_priceChanges_def] >>
    Cases_on `checkTypes params [TypeInt; TypeInt]` >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `isSenderSupplier context s1 ∧ s1.phase = PhaseTasks ∧
             ¬NULL s1.priceChanges ∧
             ((HD s1.priceChanges).negotiation = NegotiationApproved ∨
              (HD s1.priceChanges).negotiation = NegotiationRejected) ∧
             s1.agreement.negotiation = NegotiationApproved` >>
    UNDISCH_LAST >> REWRITE_TAC [DE_MORGAN_THM1] >> rpt STRIP_TAC >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >> 
    rw[] >> FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def]
QED

Theorem task_after_12:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(getTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [getTask_typed_def] >> FULL_SIMP_TAC std_ss [get_context_msgSender_def,
    get_person_id_def, get_agreement_customer_def, get_agreement_supplier_def,
    get_context_msgSender_def, get_campaign_tasks_def] >>
    FULL_SIMP_TAC (srw_ss()) const_defs >>
    Cases_on `params` >> FULL_SIMP_TAC (srw_ss()) [] >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `h` >> fs [] >> 
    Cases_on `t` >> FULL_SIMP_TAC (srw_ss()) [] >>
    FULL_SIMP_TAC std_ss [p_get_task_index_by_id_def] >>
    FULL_SIMP_TAC std_ss [get_campaign_agreement_def] >>
    Cases_on `INDEX_FIND 0 (λx. get_task_id x = n) s1.tasks` >>
    FULL_SIMP_TAC (srw_ss())[] >> FULL_SIMP_TAC std_ss [get_campaign_def] >>
    Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) [] >>
    Cases_on `context.msgSender = (s1.agreement :> Agreement_supplier).id ∨
             context.msgSender = (s1.agreement :> Agreement_customer).id ` >>
    FULL_SIMP_TAC (srw_ss())[] >> FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >> rw [] >>
    FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def] >>
    FULL_SIMP_TAC std_ss [FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_def] >> rw [] >>
    FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def] >>
    FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def]
QED

Theorem task_after_p_update_Campaign_tasks:
    !s1 s2 t1 t2 taskId x.
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId /\
    s2 = p_update_Campaign_tasks s1 x taskId ==> 
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> 
    fs [p_update_Campaign_tasks_def, get_campaign_tasks_def, get_task_id_def, set_campaign_tasks_def, 
    p_get_campaign_task_by_task_id_def, UPDATE_BY_ID_def] >> 
    cheat
QED

Theorem task_after_13:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(approveTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [approveTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_context_msgSender context = get_person_id (get_agreement_supplier (get_campaign_agreement s1)) ∧ 
    get_task_negotiation x = NegotiationApproved` >-
    (fs [get_campaign_def] >> Cases_on `taskId=scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, 
    ‘(set_task_negotiation x NegotiationApproved)’] mp_tac) >> rw []) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_negotiation x NegotiationApproved)’, ‘taskId’, 
    ‘scToInt (HD params)’] mp_tac) >> rw [] >> Q.EXISTS_TAC `t1` >> rw []) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_14:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(rejectTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [rejectTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_context_msgSender context = get_person_id (get_agreement_supplier (get_campaign_agreement s1)) ∧ 
    get_task_negotiation x = NegotiationApproved` >-
    (fs [get_campaign_def] >> Cases_on `taskId=scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, 
    ‘(set_task_negotiation x NegotiationRejected)’] mp_tac) >> rw []) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_negotiation x NegotiationRejected)’, ‘taskId’, 
    ‘scToInt (HD params)’] mp_tac) >> rw [] >> Q.EXISTS_TAC `t1` >> rw []) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_15:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(acceptTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [acceptTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_context_msgSender context = get_person_id (get_agreement_supplier (get_campaign_agreement s1)) ∧ 
    get_task_negotiation x = NegotiationApproved ∧ get_task_taskStatus x = TaskNotAccepted` >-
    (fs [get_campaign_def] >> Cases_on `taskId=scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, 
    ‘(set_task_taskStatus x TaskAccepted)’] mp_tac) >> rw []) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_taskStatus x TaskAccepted)’, ‘taskId’, 
    ‘scToInt (HD params)’] mp_tac) >> rw [] >> Q.EXISTS_TAC `t1` >> rw []) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_17:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(addTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [addTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt; TypeString; TypeInt; TypeString; TypeInt; TypePaymentType] ∧
    isSenderCustomer context s1 ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >- 
    (fs [] >> fs [get_campaign_def, get_campaign_tasks_def, TASK_HASH_DEF, p_get_campaign_task_by_task_id_def, FIND_def] >> 
    fs [get_campaign_tasks_def, INDEX_FIND_def, get_task_id_def, p_add_task_in_Campaign_def, set_campaign_tasks_def] >>
    Cases_on `SUC (FOLDR MAX 0 (MAP Task_taskID s1.tasks)) = taskId` >> 
    fs [] >> rw [] >> STRIP_ASSUME_TAC index_find_snd1 >> 
    first_x_assum (qspecl_then [‘(λx. x.taskID = taskId)’, ‘s1.tasks’, ‘z’, ‘z'’] mp_tac) >> rw [] >> 
    Q.EXISTS_TAC ‘z'’ >> rw []) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_18:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(readyToPerformTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [readyToPerformTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> fs [] >> Cases_on `isSenderWorker context x ∧ 
    get_task_negotiation x = NegotiationApproved ∧ get_task_taskStatus x = TaskAccepted` >- 
    (FULL_SIMP_TAC std_ss [get_campaign_def] >> Cases_on `taskId=scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, 
    ‘(set_task_taskStatus x TaskReadyToPerform)’] mp_tac) >> rw [set_task_taskStatus_def]) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_taskStatus x TaskReadyToPerform)’, ‘taskId’, 
    ‘scToInt (HD params)’] mp_tac) >> rw [] >> Q.EXISTS_TAC `t1` >> rw []) >> FULL_SIMP_TAC pure_ss [] >>
    fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_19:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(requestGas_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [requestGas_typed_def] >> 
    Cases_on `checkTypes params [TypeInt; TypeInt] ∧ get_campaign_phase s1 = PhaseTasks` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> fs [] >> Cases_on `calculateLastPrice s1` >-
    (fs const_defs >> fs [get_campaign_def]) >> fs [] >> Cases_on `isSenderCaptain context x ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ 
    get_task_negotiation x = NegotiationApproved ∧ get_task_taskStatus x = TaskReadyToPerform` >-
    (fs [get_campaign_def] >> Cases_on `taskId=(scToInt (HD params))` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, ‘(set_task_requestTime 
    (set_task_requestedGas (set_task_totalGas (set_task_taskStatus x GasRequested) 
    (get_task_totalGas x + scToInt (EL 1 params))) (scToInt (EL 1 params))) 
    (get_context_blockNum context))’] mp_tac) >> rw []) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_requestTime (set_task_requestedGas 
    (set_task_totalGas (set_task_taskStatus x GasRequested) 
    (get_task_totalGas x + scToInt (EL 1 params))) (scToInt (EL 1 params))) 
    (get_context_blockNum context))’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw [] >> Q.EXISTS_TAC `t1` >> rw []) >> 
    Cases_on `isSenderCaptain context x ∧ get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ 
    get_task_negotiation x = NegotiationApproved ∧ get_task_taskStatus x = GasRequested` >-
    (fs [get_campaign_def] >> Cases_on `taskId=(scToInt (HD params))` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, ‘(set_task_requestTime 
    (set_task_requestedGas (set_task_totalGas (set_task_taskStatus x GasRequested) 
    (get_task_totalGas x + scToInt (EL 1 params))) (scToInt (EL 1 params))) 
    (get_context_blockNum context))’] mp_tac) >> rw []) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_requestTime (set_task_requestedGas 
    (set_task_totalGas (set_task_taskStatus x GasRequested) 
    (get_task_totalGas x + scToInt (EL 1 params))) (scToInt (EL 1 params))) 
    (get_context_blockNum context))’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw [] >> Q.EXISTS_TAC `t1` >> rw []) >>
    FULL_SIMP_TAC pure_ss [LEFT_AND_OVER_OR] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_20:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(completePayment_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [completePayment_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_paymentOrder_by_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (get_PaymentOrder_taskId x)` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_task_negotiation x' ≠ NegotiationApproved` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_task_taskStatus x' = Confirmed` >-
    (fs [get_campaign_def] >> Cases_on `taskId = get_PaymentOrder_taskId x` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘(p_update_Campaign_paymentOrders s1 
    (set_PaymentOrder_paymentStatus x PaymentCompleted) (scToInt (HD params)))’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, 
    ‘(set_task_taskStatus x' TaskCompleted)’] mp_tac) >> 
    STRIP_ASSUME_TAC p_update_Campaign_paymentOrders_correctness >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_PaymentOrder_paymentStatus x PaymentCompleted)’, ‘taskId’, 
    ‘(scToInt (HD params))’] mp_tac) >> rw []) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >>
    first_x_assum (qspecl_then [‘(p_update_Campaign_paymentOrders s1 
    (set_PaymentOrder_paymentStatus x PaymentCompleted) (scToInt (HD params)))’, ‘(set_task_taskStatus x' TaskCompleted)’, 
    ‘taskId’, ‘(get_PaymentOrder_taskId x)’] mp_tac) >> rw [] >> Q.EXISTS_TAC `t1` >> rw [] >> 
    STRIP_ASSUME_TAC p_update_Campaign_paymentOrders_correctness >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_PaymentOrder_paymentStatus x PaymentCompleted)’, ‘taskId’, 
    ‘(scToInt (HD params))’] mp_tac) >> rw []) >>
    fs [get_campaign_def] >> STRIP_ASSUME_TAC p_update_Campaign_paymentOrders_correctness >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_PaymentOrder_paymentStatus x PaymentCompleted)’, ‘taskId’, 
    ‘(scToInt (HD params))’] mp_tac) >> rw [] >> Q.EXISTS_TAC `t1` >> rw []) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_21:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(performTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [performTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `isSenderWorker context x ∧ get_task_taskStatus x = GasRequested ∧ 
    get_task_negotiation x = NegotiationApproved ` >- 
    (FULL_SIMP_TAC std_ss [get_campaign_def] >> Cases_on `taskId=scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, ‘(set_task_taskStatus x Performing)’] mp_tac) >> rw []) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_taskStatus x Performing)’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> 
    rw [] >> Q.EXISTS_TAC `t1` >> rw []) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_22:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(completeTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [completeTask_typed_def] >> 
    Cases_on `checkTypes params [TypeInt; TypeInt] ∧ get_campaign_phase s1 = PhaseTasks ∧ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ∧ approvedPriceExists s1` >-
    (fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `isSenderWorker context x ∧ get_task_taskStatus x = Performing ∧ 
    get_task_negotiation x = NegotiationApproved` >- 
    (FULL_SIMP_TAC std_ss [get_campaign_def] >> Cases_on `taskId=scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, 
    ‘(set_task_suppliedGas (set_task_suppliedTime x (get_context_blockNum context)) (scToInt (EL 1 params)))’] mp_tac) >> rw []) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_suppliedGas (set_task_suppliedTime x 
    (get_context_blockNum context)) (scToInt (EL 1 params)))’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw [] >> 
    Q.EXISTS_TAC `t1` >> rw []) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]) >> 
    FULL_SIMP_TAC pure_ss [] >> fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_23:
    ∀(context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1 t2:Task) (taskId:num).
    SOME s2 = get_campaign(confirmTask_typed context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒
    ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    rpt STRIP_TAC >> fs [confirmTask_typed_def] >> Cases_on `¬checkTypes params [TypeInt; TypeInt]` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [confirmTask_def] >> Cases_on `get_campaign_phase s1 = PhaseTasks ⇒ 
    get_agreement_negotiation (get_campaign_agreement s1) = NegotiationApproved ⇒ ¬approvedPriceExists s1` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `p_get_campaign_task_by_task_id s1 (scToInt (HD params))` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_task_negotiation x ≠ NegotiationApproved` >-
    (fs const_defs >> fs [get_campaign_def]) >> 
    fs [] >> Cases_on `get_context_msgSender context = get_person_id (get_task_captain x)` >- 
    (fs [] >> Cases_on `get_task_taskStatus x = Performing` >-
    (fs [] >> Cases_on `scToInt (EL 1 params) = get_task_totalGas x ∧ get_task_paymentType x = Pre` >-
    (fs [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, ‘(set_task_taskStatus x TaskCompleted)’] mp_tac) >> rw []) >> 
    STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_taskStatus x TaskCompleted)’, ‘taskId’, ‘scToInt (HD params)’] mp_tac) >> rw [] >>
    Q.EXISTS_TAC `t1` >> rw []) >> FULL_SIMP_TAC pure_ss [] >> fs [get_campaign_def] >> Cases_on `taskId = scToInt (HD params)` >-
    (fs [] >> STRIP_ASSUME_TAC set_campaign_paymentOrders_correctness >>
    first_x_assum (qspecl_then [‘(p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed) (scToInt (HD params)))’, 
    ‘(get_campaign_paymentOrders
             (p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed)
                (scToInt (HD params))) ⧺
           [case get_task_paymentType x of
              Pre =>
                PaymentOrder
                  (get_priceChange_price (THE (calculateLastPrice s1)) *
                   if scToInt (EL 1 params) < get_task_totalGas x then
                     get_task_totalGas x − scToInt (EL 1 params)
                   else scToInt (EL 1 params) − get_task_totalGas x) 0 0
                  (scToInt (HD params)) WaitingForPayment
                  (get_task_suppliedGas x < get_task_totalGas x ⇒
                   get_task_paymentType x ≠ Pre)
            | Post =>
              PaymentOrder
                (get_priceChange_price (THE (calculateLastPrice s1)) *
                 scToInt (EL 1 params)) 0 0 (scToInt (HD params))
                WaitingForPayment
                (get_task_suppliedGas x < get_task_totalGas x ⇒
                 get_task_paymentType x ≠ Pre)
            | Delayed =>
              PaymentOrder
                (get_priceChange_price (THE (calculateLastPrice s1)) *
                 scToInt (EL 1 params)) (get_task_paymentTime x) 0
                (scToInt (HD params)) WaitingForPayment
                (get_task_suppliedGas x < get_task_totalGas x ⇒
                 get_task_paymentType x ≠ Pre)])’, ‘taskId’] mp_tac) >> 
    rw [] >> fs [] >> STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘(p_update_Campaign_tasks s1 (set_task_taskStatus t1 Confirmed)(scToInt (HD params)))’, 
    ‘t1’, ‘t2’, ‘(scToInt (HD params))’, ‘(set_task_taskStatus t1 Confirmed)’] mp_tac) >> rw [] >> 
    STRIP_ASSUME_TAC task_after_p_update_Campaign_tasks >> 
    first_x_assum (qspecl_then [‘s1’, ‘(p_update_Campaign_tasks s1 (set_task_taskStatus t1 Confirmed)(scToInt (HD params)))’, 
    ‘t1’, ‘t2’, ‘(scToInt (HD params))’, ‘(set_task_taskStatus t1 Confirmed)’] mp_tac) >> rw []) >> 
    fs [] >> STRIP_ASSUME_TAC set_campaign_paymentOrders_correctness >>
    first_x_assum (qspecl_then [‘(p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed) (scToInt (HD params)))’, 
    ‘(get_campaign_paymentOrders
             (p_update_Campaign_tasks s1 (set_task_taskStatus x Confirmed)
                (scToInt (HD params))) ⧺
           [case get_task_paymentType x of
              Pre =>
                PaymentOrder
                  (get_priceChange_price (THE (calculateLastPrice s1)) *
                   if scToInt (EL 1 params) < get_task_totalGas x then
                     get_task_totalGas x − scToInt (EL 1 params)
                   else scToInt (EL 1 params) − get_task_totalGas x) 0 0
                  (scToInt (HD params)) WaitingForPayment
                  (get_task_suppliedGas x < get_task_totalGas x ⇒
                   get_task_paymentType x ≠ Pre)
            | Post =>
              PaymentOrder
                (get_priceChange_price (THE (calculateLastPrice s1)) *
                 scToInt (EL 1 params)) 0 0 (scToInt (HD params))
                WaitingForPayment
                (get_task_suppliedGas x < get_task_totalGas x ⇒
                 get_task_paymentType x ≠ Pre)
            | Delayed =>
              PaymentOrder
                (get_priceChange_price (THE (calculateLastPrice s1)) *
                 scToInt (EL 1 params)) (get_task_paymentTime x) 0
                (scToInt (HD params)) WaitingForPayment
                (get_task_suppliedGas x < get_task_totalGas x ⇒
                 get_task_paymentType x ≠ Pre)])’, ‘taskId’] mp_tac) >> 
    rw [] >> fs [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_taskStatus x Confirmed)’, ‘taskId’, ‘(scToInt (HD params))’] mp_tac) >> rw [] >> 
    Q.EXISTS_TAC `t1` >> rw [] >> STRIP_ASSUME_TAC p_update_Campaign_tasks_correctness4 >> 
    first_x_assum (qspecl_then [‘s1’, ‘(set_task_taskStatus x Confirmed)’, ‘taskId’, ‘(scToInt (HD params))’] mp_tac) >> rw [] >> 
    Q.EXISTS_TAC `t1` >> rw []) >> 
    fs const_defs >> fs [get_campaign_def]) >>
    fs const_defs >> fs [get_campaign_def]
QED

Theorem task_after_execute:
  ∀f (context:Context) (params:SCvalue list) (s1 s2:Campaign) (t1:Task) (taskId:num).
    SOME s2 = get_campaign(execute f context params s1) ∧
    SOME t1 = p_get_campaign_task_by_task_id s1 taskId ⇒ ∃t2. SOME t2 = p_get_campaign_task_by_task_id s2 taskId
Proof
    STRIP_TAC >> FULL_SIMP_TAC std_ss [execute_def] >> Cases_on ‘chooseFunction f’ >> FULL_SIMP_TAC std_ss [] >> FULL_SIMP_TAC std_ss const_defs >> FULL_SIMP_TAC std_ss [get_campaign_def] >> FULL_SIMP_TAC std_ss [chooseFunction_def] >>
    Cases_on ‘f = 2’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_2] >> FULL_SIMP_TAC std_ss [] >> 
    Cases_on ‘f = 3’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_3] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 4’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_4] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 5’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_5] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 6’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_6] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 7’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_7] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 8’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_8] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 9’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_9] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 10’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_10] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 11’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_11] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 12’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_12] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 13’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_13] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 14’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_14] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 15’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_15] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 17’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_17] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 18’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_18] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 19’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_19] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 20’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_20] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 21’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_21] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 22’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_22] >> FULL_SIMP_TAC std_ss [] >>
    Cases_on ‘f = 23’ >> FULL_SIMP_TAC (srw_ss()) [] >> PURE_REWRITE_TAC [task_after_23] >> FULL_SIMP_TAC std_ss [] >>
    FULL_SIMP_TAC std_ss []
QED

Theorem deploy_same_state:
   ∀e1 e2 to caddr sc1 c setup s1 state act from.
   get_envContracts e1 caddr = SOME sc1 ∧
   get_envContractStates e1 caddr = SOME s1 ∧
   get_envContracts e1 to = NONE ∧
   act = build_act from (Deploy c setup) ∧
   get_campaign (get_init c (get_envChain e1) (build_ccc from to) setup) = SOME state ∧
   e2 = set_contract_state to state (add_contract to c e1) ⇒ get_envContractStates e2 caddr = SOME s1
Proof
    rpt STRIP_TAC >> 
    rw [get_envContractStates_def, add_contract_def, get_envContracts_def, set_contract_state_def, 
    get_envContractStates_def, UPDATE_def] >> fs [get_envContractStates_def]
QED

Theorem set_state_same_addr:
    ∀ e1 nextState caddr sc. get_envContracts e1 caddr = sc ⇒
    get_envContracts (set_contract_state caddr nextState e1) caddr = sc
Proof
    FULL_SIMP_TAC (srw_ss()) [get_envContracts_def, set_contract_state_def]
QED

Theorem none_not_some_addr:
    ∀ e1 to caddr. e1.envContracts to = NONE ∧ e1.envContracts caddr = SOME sc1 ⇒ ~ (to = caddr)
Proof
    rpt STRIP_TAC >> FULL_SIMP_TAC std_ss []
QED

Theorem status_not_decreasing:
  ∀(e1 e2:Environment) (s1 s2:Campaign) (t1 t2:Task) (taskId:num) caddr. 
  get_envContracts e1 caddr = SOME sc1 ∧ 
  get_envContractStates e1 caddr = SOME s1 ∧ 
  get_envContracts e2 caddr = SOME sc1 ∧ 
  get_envContractStates e2 caddr = SOME s2 ∧ 
  ChainTrace e1 e2 ∧ 
  SOME t1 = p_get_campaign_task_by_task_id s1 taskId ∧ 
  SOME t2 = p_get_campaign_task_by_task_id s2 taskId ⇒ status_numeration(get_task_taskStatus t2) >= status_numeration(get_task_taskStatus t1)
Proof
  FULL_SIMP_TAC std_ss [ChainTrace_cases] >> 
  Induct_on ‘ChainedList ChainStep e1 e2’ >> 
  STRIP_TAC >- 
  (rw[] >> FULL_SIMP_TAC std_ss [] >> rw [] >> 
  FULL_SIMP_TAC std_ss [p_get_campaign_task_by_task_id_def, FIND_def] >> FULL_SIMP_TAC std_ss [INDEX_FIND_def]) >> 
  rpt STRIP_TAC >> FULL_SIMP_TAC std_ss [Once ChainStep_cases] >> FULL_SIMP_TAC std_ss [Once ActionEvaluation_cases] >- 
  (STRIP_ASSUME_TAC deploy_same_state >> first_x_assum (qspecl_then [‘e1’, ‘e1'’, ‘to’, ‘caddr’, ‘sc1’, ‘c’, ‘setup’, ‘s1’, 
  ‘state’, ‘act’, ‘from’] mp_tac) >> FULL_SIMP_TAC (srw_ss()) [] >> STRIP_TAC >> 
  FULL_SIMP_TAC (srw_ss()) [build_act_def,get_actBody_def] >> rw [] >> 
  first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, ‘caddr’] mp_tac) >> FULL_SIMP_TAC (srw_ss()) [] >> 
  STRIP_TAC >> 
  FULL_SIMP_TAC (srw_ss()) [add_contract_def, get_envContracts_def, set_contract_state_def, get_envContractStates_def, 
  UPDATE_def] >> STRIP_ASSUME_TAC none_not_some_addr >> 
  first_x_assum (qspecl_then [‘e1’, ‘to’, ‘caddr’] mp_tac) >> FULL_SIMP_TAC (srw_ss()) []) >> 
  Cases_on ‘to=caddr’ >- 
  (FULL_SIMP_TAC std_ss [] >> rw [] >> FULL_SIMP_TAC std_ss [get_receive_def] >> FULL_SIMP_TAC (srw_ss()) [sc1_def] >> 
  FULL_SIMP_TAC std_ss [scReceive_def] >> FULL_SIMP_TAC (srw_ss()) [build_act_def,get_actBody_def] >> rw [] >> 
  STRIP_ASSUME_TAC task_after_execute >> 
  first_x_assum (qspecl_then [‘get_functionSignature data’, 
  ‘build_context (take_address (get_msgSender (build_ccc from caddr))) (get_blockNum (get_envChain e1))’, 
  ‘get_params data’,‘prevState’, ‘nextState’, ‘t1’, ‘taskId’] mp_tac) >> FULL_SIMP_TAC (srw_ss()) [] >> 
  STRIP_TAC >> STRIP_ASSUME_TAC not_decreasing_after_execute >> 
  first_x_assum (qspecl_then [‘get_functionSignature data’, 
  ‘build_context (take_address (get_msgSender (build_ccc from caddr))) (get_blockNum (get_envChain e1))’, 
  ‘get_params data’, ‘prevState’, ‘nextState’, ‘t1’, ‘t2'’, ‘taskId’] mp_tac) >> FULL_SIMP_TAC (srw_ss()) [] >> 
  STRIP_TAC >> first_x_assum (qspecl_then [‘nextState’, ‘s2’, ‘t2'’, ‘t2’, ‘taskId’, ‘caddr’] mp_tac) >> 
  FULL_SIMP_TAC (srw_ss()) [] >> STRIP_TAC >> STRIP_ASSUME_TAC set_state_same_addr >> 
  first_x_assum (qspecl_then [‘e1’, ‘nextState’, ‘caddr’, ‘SOME <|init := scInit; receive := scReceive|>’] mp_tac) >> 
  FULL_SIMP_TAC (srw_ss()) [] >> STRIP_TAC >> 
  FULL_SIMP_TAC (srw_ss()) [set_contract_state_def, get_envContractStates_def, UPDATE_def] >> rw []) >> 
  FULL_SIMP_TAC (srw_ss()) [build_act_def,get_actBody_def] >> rw [] >> 
  first_x_assum (qspecl_then [‘s1’, ‘s2’, ‘t1’, ‘t2’, ‘taskId’, ‘caddr’] mp_tac) >> FULL_SIMP_TAC (srw_ss()) [] >> 
  STRIP_TAC >> FULL_SIMP_TAC (srw_ss()) [set_contract_state_def, get_envContractStates_def, get_envContracts_def, UPDATE_def]
QED

val _ = export_theory();
