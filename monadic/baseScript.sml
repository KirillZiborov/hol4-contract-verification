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
open preamble
open basis
open ml_monad_translator_interfaceLib

open stringTheory
open wordsTheory
open listTheory
(* open monadChainTheory *)
open sc1TypesTheory

val _ = new_theory "base";
val _ = translation_extends "basisProg";
val _ = ParseExtras.temp_tight_equality ();

(*CONSTS ------------------------------------------------------------------------ *)
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

val sconst_defs = [
    Define `SBAD_ERR = "Error"`,
    Define `SBAD_TYPE = "Type error"`,
    Define `SERR_TYPE_CONV = "Type conversion error"`,
    Define `SWRNG_NMBR = "Wrong number of params."`,
    Define `SPARSE_ERR_taskId = "Parse param error: taskId incorrect type."`,
    Define `SPRICE_GT0 = "Price must be more than 0."`,
    Define `SNEX_Task = "Task does not exist."`,
    Define `SONLY_Suppl_appr = "Only supplier allowed to approve"`,
    Define `SNOT_PhTasks = "Phase is not PhaseTasks"`,
    Define `SONLY_Suppl_rej = "Only supplier allowed to reject"`,
    Define `SNOT_APPROVED_Task = "Task is not approved yet."`,
    Define `SONLY_worker_acc = "Only worker allowed to accept Task"`,
    Define `SNOT_APPROVED_task = "Task is not approved yet."`,
    Define `SONLY_SupplCust_get = "Only supplier or customer allowed to get task"`,
    Define `SNOT_ALLOWED_action = "Action is not allowed at this point."`,
    Define `SNOT_ALLOWED_SUPPLIER_REJECT = "Supplier is not allowed to reject at this point"`,
    Define `SNOT_ALLOWED_CUSTOMER_CHANGE_AGREEMENT = "Customer is not allowed to change agreement at this point"`,
    Define `SONLY_CUST_OR_SUPPL_ALLOWED_VIEW_AGREEMENT = "Only customer or supplier allowed to view agreement"`,
    Define `SONLY_WAITING_SUPPLIER = "AgreementNegotiation should be WaitingSupplier"`,
    Define `SONLY_SUPPLIER_REJECT = "Only supplier is allowed to reject at this point"`,
    Define `SONLY_SUPPLIER_APPROVE = "Only supplier is allowed to approve at this point"`,
    Define `SONLY_CUSTOMER_CHANGE = "Only customer is allowed to change agreement at this point"`,
    Define `SNO_GAS_REQUESTS = "No gas requests."`,
    Define `SNO_APPROVED_PRICES = "No approved prices."`,
    Define `SNEX_Payment = "Payment order does not exist."`,
    Define `SONLY_Captain = "Only captain allowed to do this action."`,
    Define `SNEX_function = "The function doesn't exist"`,
    Define `SWRNG_COND_001 = "TaskNegotiation must not be approved. AgreementNegotiation must be approved. At least one PriceChange must be approved."`,
    Define `SAGREEMENT_IS_APPROVED = "AgreementNegotiation must not be approved."`,
    Define `SWRNG_COND_002 = "Param must be a number. Only customer allowed to do this action. At least one PriceChange must exist."`,
    Define `SWRNG_COND_003 = "Wrong conditions. Please, check: sender is Customer, at least one PriceChange exists."`,
    Define `SWRNG_COND_004 = "Wrong conditions. Please, check: sender is Customer, phase is PhaseTasks, at least one PriceChange exists, Agreement is approved."`,
    Define `SWRNG_COND_005 = "Wrong conditions. Please, check: sender is Supplier, phase is PhaseTasks, last PriceChange is approved or rejected, Agreement is approved."`,
    Define `SWRNG_COND_006 = "Wrong conditions. Please, check: params are two numbers."`,
    Define `SWRNG_COND_007 = "Wrong conditions. Please, check: Agreement is approved, at least one PriceChange is approved."`,
    Define `SWRNG_COND_008 = "Wrong conditions. Please, check: params are (number, string, number, string, number, PaymentType), sender is Customer, phase is PhaseTask, Agreement is approved, at least one PriceChange is approved."`,
    Define `SWRNG_COND_009 = "Wrong conditions. Please, check: sender is Worker, Task is approved and accepted."`,
    Define `SWRNG_COND_010 = "Wrong conditions. Please, check: param is a number, phase is PhaseTasks, Agreement is approved, at least one PriceChange exists."`,
    Define `SWRNG_COND_011 = "Wrong conditions. Please, check: sender is Captain, Agreement is approved, Task approved and ready to perform or gas requested."`,
    Define `SWRNG_COND_012 = "Wrong conditions. Please, check: params are two numbers, phase is PhaseTasks."`,
    Define `SWRNG_COND_013 = "Wrong conditions. Please, check: param is a number, phase is PhaseTasks, Agreement is approved, at least one PriceChange is approved."`,
    Define `SWRNG_COND_014 = "Wrong conditions. Please, check: sender is Worker, gas is requested, Task is approved."`,
    Define `SWRNG_COND_015 = "Wrong conditions. Please, check: sender is Worker, Task is approved and performing now."`,
    Define `SWRNG_COND_016 = "Wrong conditions. Please, check: params are two numbers, phase is PhaseTasks, Agreement is approved, at least one PriceChange is approved."`
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
Definition set_context_storage_def:
    set_context_storage con v :Context = con with storage := v
End
Definition get_context_msgSender_def:
    get_context_msgSender = Context_msgSender
End
Definition get_context_blockNum_def:
    get_context_blockNum = Context_blockNum
End
Definition get_context_storage_def:
    get_context_storage = Context_storage
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

Definition p_update_Campaign_tasks_def:
   p_update_Campaign_tasks campaign task taskId =
     set_campaign_tasks campaign $
     MAP (\tsk. if taskId = get_task_id tsk then task else tsk) (get_campaign_tasks campaign)
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

(* 1) use this instead of "LUPDATE newrez indx tasks" *)
(* 2) rewrite p_update_Campaign_tasks_def using this definition *)
Definition UPDATE_BY_ID_def:
  UPDATE_BY_ID newrez id tasks =
    MAP (λ t. (if t.taskID = id then (newrez with taskID := id) else t) ) tasks
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

(* -------------------- *)
(* BEGIN common tactics *)
val ERR = mk_HOL_ERR "Tactic"
fun empty th [] = th
  | empty th _ = raise ERR "empty" "Bind Error"
fun sing f [x] = f x
  | sing f _ = raise ERR "sing" "Bind Error"
fun pairths f [x, y] = f x y
  | pairths f _ = raise ERR "pairths" "Bind Error"
(* END common tactics *)

(* BEGIN tactics*)

fun dummy_tac q : tactic
    = all_tac

(*
datatype lambda =
     VAR of string * hol_type
   | CONST of {Name: string, Thy: string, Ty: hol_type}
   | COMB of term * term
   | LAMB of term * term
*)

fun lambda_comb (COMB pt) = pt
  | lambda_comb _ = raise Fail "not a lambda COMB"

fun lambdagetpair (COMB pt) = pt
  | lambdagetpair (LAMB pt) = pt
  | lambdagetpair _ = raise Fail "wrong constructor"

fun term_by_bin ([]:int list) (t:term) : term = t
  | term_by_bin (he::ta) t =
    (let
      val p = t |> dest_term |> lambdagetpair
      val st = (if he=0 then (fst p) else (snd p))
    in
      term_by_bin ta st
    end)

(* GET SUBTERM TACTICS *)

(* redundant! it is similar to "strip_comb" function, but works when term con *)
(*see also strip_fun for types*)
fun term_as_list te : term list =
    (term_as_list (rator te)) @ [(rand te)] handle _ => [te]

fun list_as_term li : term = List.foldl (mk_comb o swap) (hd li) (tl li)

val get_head = hd o term_as_list
val get_args = tl o term_as_list

(* otherwise "val gener:term = ``COND``" gives <<HOL message: inventing new type variable names: 'a>> *)
fun fst_subterm_matches gener s1 s2 w =
     let
       val l = term_as_list w
       val insta = (el 1 l)
       val sub = (match_term gener insta)
         handle _ => raise ERR s1 s2
     in
       w
     end

val gener_ALL : term = ``(!) : (α -> bool) -> bool``
val checkALL : term -> term = fst_subterm_matches gener_ALL "checkALL" "Not a FORALL term"

val gener_EX : term = ``(?) : (α -> bool) -> bool``
val checkEX : term -> term = fst_subterm_matches gener_EX "checkEX" "Not an EX term"

val gener_NEG : term = ``(~) : bool -> bool``
val checkNEG : term -> term = fst_subterm_matches gener_NEG "checkNEG" "Not a NEG term"

val gener_IF : term = ``COND : bool -> α -> α -> α``
val checkIF : term -> term = fst_subterm_matches gener_IF "checkIF" "Not an IF term"

val gener_EQ : term = ``(=) : α -> α -> bool``
val checkEQ : term -> term = fst_subterm_matches gener_EQ "checkEQ" "Not an EQ term"

(* *)
val Cases_on_term: term -> tactic
     = fn (te : term) => (Cases_on ([ANTIQUOTE te]) >> simp []) : tactic

val get_first_arg  = (el 1) o get_args
val get_second_arg = (el 2) o get_args
(**)

(** Functions for the term destruction **)

fun term_by_num [] t = t
  | term_by_num (he::ta) t =
      term_by_num ta (el he $ term_as_list $ t)

(** Functions for the explicit term destruction **)

(* ∀ *)
val get_forall_body : term -> term
   = term_by_bin [1,1] o checkALL

(* ∃ *)
val get_exists_body : term -> term
   = term_by_bin [1,1] o checkEX

(* get left subterm of equality *)
val get_eq_left : term -> term
  = term_by_num [2] o checkEQ

(* get right subterm of equality *)
val get_eq_right : term -> term
  = term_by_num [3] o checkEQ

(* get neg's arg *)
val get_neg : term -> term
  = term_by_num [2] o checkNEG

(* get IF's condition *)
val get_if_cond : term -> term
  = term_by_num [2] o checkIF

val get_cond_term = get_if_cond
(* see HOL/src/portbleML/Portable.sml *)
val to_quotation : term -> term quotation
  = single o ANTIQUOTE

(* get the conclusion of the goal *)
val get_concl : goal -> term = snd

(* get ==>'s antecedent *)
val get_antecedent : term -> term
  = term_by_num [2] (* o checkIMP  TODO! "($==>:bool=>bool=>bool)" *)

(* Using something obtained from the goal as the argument
   to a function that creates a tactic.

Use cases:
1) for debug
  use_goal (print_term o get_neg o get_if_cond o get_eq_left o get_exists_body o get_concl) dummy_tac >>
2) for reasoning:
  use_goal (to_quotation o get_neg o get_if_cond o get_eq_left o get_exists_body o get_concl) Cases_on >>
*)

fun use_goal (obt:goal->'a) (tacf:'a->tactic) : tactic
    = (fn x as (asl, w) => tacf (obt x) x)

fun print_endline x = print (x ^ "\n")
val print_term = print_endline o term_to_string
(* END tactics *)

(* BEGIN debug tactics *)
val sg : goal ref = ref ([],``0``)
fun sasl () : term list = fst (!sg)
fun   sw () : term = snd (!sg)

val sg_tac : tactic
    = (fn x as (asl, w) => (sg:=x; all_tac) x)

val show_term : term -> string =
 fn x => (String.concatWith ";\n" o map term_to_string o term_as_list) x ^ ";\n"

val print_tac : tactic
    = (fn x as (asl, w) =>
(print $ show_term w; all_tac) x)
(* END debug tactics *)

(* BEGIN Unique ID section *)
(** Tactics **)
(* Tactic that drops one hypothesis from the context *)
val WEAK_TAC: tactic =
   fn (asl, w) =>
    case asl of
      [] => raise ERR "WEAK_TAC" ""
    | h::t => ([(t,w)], sing (fn x => x))

(* Tactic that rotates hypotheses *)
val ROUND_TAC: tactic =
   fn (asl, w) =>
    case asl of
      [] => raise ERR "ROUND_TAC" ""
    | h::t => ([(t @ [h],w)], sing (fn x => x))

(* Tactic that proves thm if the first hypothesis equals the conclusion. *)
val EXACT_TAC: tactic =
   fn (asl, w) =>
    case asl of
      [] => raise ERR "EXACT_TAC" ""
    | h::t => ([], empty (Thm.ASSUME h))


(*HIGHFUNCS --------------------------------------------------------------------- *)

Definition get_state_def:
get_state : (State, State, state_exn) M =
  λ (s:State). (Success s, s)
End

Definition set_state_def:
  set_state : State -> (State, unit, state_exn) M
    = λ s w. (Success (), s)
End

Definition scMToString_def:
scMToString (sc:SCvalue) : (State, string, state_exn) M  =
  (λ (s:State). case sc of
    SCString stri => (Success stri, s)
  | _ => (Failure (Fail SERR_TYPE_CONV), s))
End

Definition scMToInt_def:
scMToInt (sc:SCvalue) : (State, num, state_exn) M  =
  (λ (s:State). case sc of
    SCInt v => (Success v, s)  (*Success*)
  | _ => (Failure (Fail SERR_TYPE_CONV), s)) (*Failure*)
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

Definition new_getAgreement_typed_def:
  new_getAgreement_typed : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    sender <<- (get_context_msgSender s.context);
    agreement <<- (get_campaign_agreement s.campaign);
    customer <<- (get_agreement_customer agreement);
    supplier <<- (get_agreement_supplier agreement);
    custPersID <<- (get_person_id customer);
    suppPersID <<- (get_person_id supplier);
      assert SONLY_CUST_OR_SUPPL_ALLOWED_VIEW_AGREEMENT ¬(sender ≠ custPersID ∨ sender ≠ suppPersID);
    return (SCAgreement agreement);
   od
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

Definition new_rejectAgreement_typed_def:
  new_rejectAgreement_typed : (State, unit, state_exn) M =
  do
    s <- get_state;
    assert SONLY_WAITING_SUPPLIER (get_agreement_negotiation s.campaign.agreement = WaitingSupplier);
    agreement <<- (get_campaign_agreement s.campaign);
    supplier <<- (get_agreement_supplier agreement);
    persID <<- (get_person_id supplier);
    sender <<- (get_context_msgSender s.context);
      assert SONLY_SUPPLIER_REJECT (sender = persID);

    phase <<- (get_campaign_phase s.campaign);
      assert SNOT_ALLOWED_SUPPLIER_REJECT (phase = PhaseAgreement);

    negotiation <<- (get_campaign_negotiation s.campaign);
      assert SNOT_ALLOWED_SUPPLIER_REJECT (negotiation = WaitingSupplier);

    newagreement <<- set_agreement_negotiation agreement WaitingCustomer;
    newcampaign  <<- set_campaign_agreement s.campaign newagreement;
    res  <- set_state (s with campaign:=newcampaign);
    return ();
  od
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

Definition new_approveAgreement_typed_def:
  new_approveAgreement_typed : (State, unit, state_exn) M =
  do
    s <- get_state;

    agreement <<- (get_campaign_agreement s.campaign);
       assert SONLY_WAITING_SUPPLIER (get_agreement_negotiation agreement = WaitingSupplier);

    sender <<- (get_context_msgSender s.context);
    supplier <<- (get_agreement_supplier agreement);
    persID <<- (get_person_id supplier);
        assert SONLY_SUPPLIER_APPROVE (sender = persID);

    phase <<- (get_campaign_phase s.campaign);
        assert SNOT_ALLOWED_SUPPLIER_REJECT (phase = PhaseAgreement);

    negotiation <<- (get_campaign_negotiation s.campaign);
        assert SNOT_ALLOWED_SUPPLIER_REJECT (negotiation = WaitingSupplier);

    newagreement <<- set_agreement_negotiation agreement NegotiationApproved;
    newcampaign <<- set_campaign_phase s.campaign PhaseTasks;
    newcampaign <<- set_campaign_agreement newcampaign newagreement;
    res <- set_state (s with campaign:=newcampaign);
    return();
  od
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

Definition new_changeAgreement_def:
new_changeAgreement (newdetailsSTR:string) (bankAddr:num) : (State, SCvalue, state_exn) M =
do
  s <- get_state;
    assert SAGREEMENT_IS_APPROVED ¬(get_agreement_negotiation s.campaign.agreement = NegotiationApproved);

  sender <<- (get_context_msgSender s.context);
  agreement <<- (get_campaign_agreement s.campaign);
  supplier <<- (get_agreement_supplier agreement);
  persID <<- (get_person_id supplier);
  phase <<- (get_campaign_phase s.campaign);
    assert SONLY_CUSTOMER_CHANGE (sender = persID);
    assert SNOT_ALLOWED_CUSTOMER_CHANGE_AGREEMENT (phase = PhaseAgreement);
  negotiation <<- get_campaign_negotiation s.campaign;
    assert SNOT_ALLOWED_CUSTOMER_CHANGE_AGREEMENT (negotiation = WaitingCustomer);

  newagreement <<- set_agreement_negotiation agreement WaitingSupplier;
  newdetails <<- (AgreementDetails newdetailsSTR bankAddr);
  newagreement <<- set_agreement_details newagreement newdetails;
  newagreement <<- set_agreement_negotiation newagreement WaitingSupplier;
  newcampaign <<- set_campaign_phase s.campaign PhaseTasks;

  newcampaign  <<- set_campaign_agreement newcampaign newagreement;
  res <- set_state (s with campaign:=newcampaign);
  return (SCUnit);
od
End

(*  (Success (), s with cur_camp := newcampaign)
  λ (s:State).
  let
    context = s.cur_cont;
    campaign = s.cur_camp;
    sender = (get_context_msgSender context);
    agreement = (get_campaign_agreement campaign);
    supplier = (get_agreement_supplier agreement);
    persID = (get_person_id supplier)
  in
  (*WRN*)if get_agreement_negotiation agreement = NegotiationApproved then BAD_ERR else
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
  (Success (), s with cur_camp := newcampaign)
End*)
(*
Theorem ex_EQ_EXT:
∃s. () ⇒ ∃s. (f = g)
*)

Theorem nonConstrQ_imp:
 ∀A. ((∀ (s:'a). A ⇒ F) ⇒ F) ⇒ ∃(s:'a). A
Proof
  cheat
QED
(*  use_goal (print_term o get_neg o get_if_cond o get_eq_left o get_exists_body o get_concl) dummy_tac >> *)

(* ?? *)
val negcases_tac:tactic =
  irule boolTheory.EQ_EXT >>
  (gen_tac >> simp []) >>
  (Cases_on `get_state x` >> simp []) >>
  (Cases_on `q` >>  simp []) >>
  cheat


Theorem test1:
∀ (s:State) (newdetailsSTR:string) (bankAddr:num).
  let
    sender = (get_context_msgSender s.context);
    agreement = (get_campaign_agreement s.campaign);
    supplier = (get_agreement_supplier agreement);
    persID = (get_person_id supplier);
  in
    ¬(sender = persID) ⇒
    ∃ (q:string). ∃ (w:State).
    new_changeAgreement newdetailsSTR bankAddr = (failwith ( q): State -> (SCvalue, state_exn) exc # State)
Proof
  (* todo: refomulate theorem or find new way to prove the same,
     but INSIDE the existantial quantifier(better) *)
  rw [new_changeAgreement_def] >>
  (* simp [SPEC nonConstrQ] >>*)
  (* irule nonConstrQ_imp >> ??? *)
  (* (use_goal (get_exists_body o get_concl) (fn x => simp [SPEC x nonConstrQ]) ) >> ??? *)
  exists_tac ``SONLY_CUSTOMER_CHANGE`` >>
  negcases_tac
(* simp [ml_monadBaseTheory.st_ex_bind_def] >>*)
  (*irule boolTheory.EQ_EXT >>
  (gen_tac >> simp []) >>
  (Cases_on `get_state x` >> simp []) >>
  (Cases_on `q` >>  simp []) >>
  cheat*)
QED

Theorem changeAgreement_assert_phase:
∀ (s:State) (newdetailsSTR:string) (bankAddr:num).
  let
    phase = (get_campaign_phase s.campaign)
  in
    ¬(phase = PhaseAgreement) ⇒
    ∃ (q:string). ∃ (w:State).
    new_changeAgreement newdetailsSTR bankAddr = fail q
Proof
  rw [new_changeAgreement_def] >>
  exists_tac ``SNOT_ALLOWED_CUSTOMER_CHANGE_AGREEMENT`` >>
  negcases_tac
(*irule boolTheory.EQ_EXT >>
  (gen_tac >> simp []) >>
  (Cases_on `get_state x` >> simp []) >>
  (Cases_on `q` >>  simp []) >>
  cheat*)
QED

Theorem changeAgreement_assert_negotiation:
∀ (s:State) (newdetailsSTR:string) (bankAddr:num).
    ¬(get_agreement_negotiation s.campaign.agreement = NegotiationApproved) ⇒
    ∃ (q:string). ∃ (w:State).
    new_changeAgreement newdetailsSTR bankAddr = fail q
Proof
  rw [new_changeAgreement_def] >>
  exists_tac ``SAGREEMENT_IS_APPROVED`` >>
  (*simp [ml_monadBaseTheory.st_ex_bind_def] >>
  irule boolTheory.EQ_EXT >>
  (gen_tac >> simp []) >>
  (Cases_on `get_state x` >> simp []) >>
  (Cases_on `q` >>  simp []) >>
  cheat*)
  negcases_tac
QED


  (* SOME (SCCampaign (set_campaign_bankAddr (set_campaign_agreement campaign (set_agreement_details (set_agreement_negotiation agreement WaitingSupplier) (AgreementDetails details bankAddr)))) ) *)
  (*if ¬(checkTypes params [TypeString; TypeInt]) then BAD_TYPE else*)

Definition new_changeAgreement_typed_def:
  new_changeAgreement_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    assert SBAD_TYPE (checkTypes params [TypeString; TypeInt]);
    newdetailsSTR <- (scMToString (EL 0 params));
    bankAddr      <- (scMToInt    (EL 1 params));
    res  <- new_changeAgreement newdetailsSTR bankAddr;
    return (SCUnit);
  od
End

(*** JUST IN CASE WE WILL USE PMATCH:

(*patternMatchesLib.ENABLE_PMATCH_CASES();*)
(* ENABLE_PMATCH_CASES() turns on parsing for
     PMATCH style case expressions. After calling it
     expressions like `case ... of ...` are not parsed
     to decision trees any more, but to PMATCH expressions.
     Decision tree case expressions are afterwards available
     via `dtcase ... of ...`.*)

Definition scMToVal_def:
scMToVal (f:α -> SCvalue) (sc:SCvalue) : (State, α, state_exn) M  =
  (λ (s:State). case sc of
    f stri => (Success stri, s)
  | _ => (Failure "Type conversion", s))
End

Definition scMToInt_def:
scMToInt = scMToVal SCInt
End

Definition scMToString_def:
scMToString = scMToVal SCString
End

JUST IN CASE WE WILL USE PMATCH ***)

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

Definition new_getPriceChangeWithNumber_typed_def:
  new_getPriceChangeWithNumber_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    assert SWRNG_COND_002 (checkTypes params [TypeInt] ∧
            isSenderCustomer s.context s.campaign ∧
            (¬ NULL (get_campaign_priceChanges s.campaign)));

    index <- (scMToInt (HD params));

    return(SCPriceChange (EL index (get_campaign_priceChanges s.campaign)));
  od
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

Definition new_getPriceChangesLength_typed_def:
  new_getPriceChangesLength_typed : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    assert SWRNG_COND_003 (isSenderCustomer s.context s.campaign ∧
     (¬ NULL (get_campaign_priceChanges s.campaign)));
    return(SCInt (LENGTH (get_campaign_priceChanges s.campaign)));
  od
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

Definition new_rejectPrice_typed_def:
  new_rejectPrice_typed : (State, unit, state_exn) M =
  do
    s <- get_state;
    assert SWRNG_COND_004 (isSenderCustomer s.context s.campaign ∧
     (get_campaign_phase s.campaign) = PhaseTasks ∧
     (¬ NULL (get_campaign_priceChanges s.campaign)) ∧
     (*WRN*)get_agreement_negotiation (get_campaign_agreement s.campaign) = NegotiationApproved ∧
     (get_priceChange_negotiation (HD (get_campaign_priceChanges s.campaign))) = WaitingCustomer);

    newcampaign <<- set_campaign_priceChanges s.campaign ((set_priceChange_negotiation (HD (get_campaign_priceChanges s.campaign)) NegotiationRejected)::(TL (get_campaign_priceChanges s.campaign)));

    res <- set_state (s with campaign := newcampaign);
    return();
  od
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

Definition new_approvePrice_typed_def:
  new_approvePrice_typed : (State, unit, state_exn) M =
  do
    s <- get_state;
    assert SWRNG_COND_004 (isSenderCustomer s.context s.campaign ∧
     (get_campaign_phase s.campaign) = PhaseTasks ∧
     (¬ NULL (get_campaign_priceChanges s.campaign)) ∧
     (*WRN*)get_agreement_negotiation (get_campaign_agreement s.campaign) = NegotiationApproved ∧
     (get_priceChange_negotiation (HD (get_campaign_priceChanges s.campaign))) = WaitingCustomer);

    newcampaign <<- set_campaign_priceChanges s.campaign ((set_priceChange_negotiation (HD (get_campaign_priceChanges s.campaign)) NegotiationApproved)::(TL (get_campaign_priceChanges s.campaign)));

    res <- set_state (s with campaign := newcampaign);
    return();
  od
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

Definition new_declinePrice_typed_def:
  new_declinePrice_typed : (State, unit, state_exn) M =
  do
    s <- get_state;
    assert SWRNG_COND_004 (isSenderCustomer s.context s.campaign ∧
     (get_campaign_phase s.campaign) = PhaseTasks ∧
     (¬ NULL (get_campaign_priceChanges s.campaign)) ∧
     (*WRN*)get_agreement_negotiation (get_campaign_agreement s.campaign) = NegotiationApproved ∧
     (get_priceChange_negotiation (HD (get_campaign_priceChanges s.campaign))) = WaitingCustomer);

    newcampaign <<- set_campaign_phase s.campaign PhaseDeclined;

    res <- set_state (s with campaign := newcampaign);
    return();
  od
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

Definition new_createPriceChange_def:
  new_createPriceChange (price:num) (startTime:num) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    agreement <<- get_campaign_agreement s.campaign;
    assert SWRNG_COND_005 (isSenderSupplier s.context s.campaign ∧
       (get_campaign_phase s.campaign) = PhaseTasks ∧
       (¬ NULL (get_campaign_priceChanges s.campaign)) ∧
       (EXISTS ($= (get_priceChange_negotiation (HD (get_campaign_priceChanges s.campaign)))) [NegotiationApproved; NegotiationRejected]) ∧
       ((get_agreement_negotiation agreement) = NegotiationApproved));

    newcampaign <<- p_add_priceChange_in_Campaign s.campaign (PriceChange price WaitingCustomer startTime);

    res <- set_state (s with campaign := newcampaign);
    return(SCUnit);
  od
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

Definition new_createPriceChange_typed_def:
  new_createPriceChange_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    assert SWRNG_COND_006 (checkTypes params [TypeInt; TypeInt]);

    price <- scMToInt(HD params);
    startTime <- scMToInt (EL 1 params);
    _ <- new_createPriceChange price startTime;
    return (SCUnit);
  od
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


Definition optErrM_def:
    optErrM (s:string) (SOME q) = st_ex_return q ∧
    optErrM (s:string) NONE = fail s
End

Definition new_getTask_typed_def:
  new_getTask_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    assert SPARSE_ERR_taskId (checkTypes params [TypeInt]);
    task_id <- scMToInt (HD params);
    task_index <<- p_get_task_index_by_id (get_campaign_tasks s.campaign) task_id;
    (_, task) <- optErrM SNEX_Task task_index;
    sender <<- get_context_msgSender s.context;
    agreement <<- get_campaign_agreement s.campaign;
    assert SONLY_SupplCust_get (EXISTS ($= sender o get_person_id o $:> agreement) [get_agreement_supplier; get_agreement_customer]);
    return(SCTask task);
  od
End

(* 13+ *)
Definition approveTask_typed_def:
    approveTask_typed = base_task_fn (p_approve_task_by_rez_id, ONLY_Suppl_appr)
End

(*Definition new_approveTask_typed_def:
  new_approveTask_typed : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    newcampaign <<- base_task_fn (p_approve_task_by_rez_id, ONLY_Suppl_appr);
    _ <- set_state (s with campaign := newcampaign);
    return (SCUnit);
  od
End*)

(* 14+ *)
Definition rejectTask_typed_def:
    rejectTask_typed = base_task_fn (p_reject_task_by_rez_id, ONLY_Suppl_rej)
End

(*Definition new_rejectTask_typed_def:
  new_rejectTask_typed : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    newcampaign <<- base_task_fn (p_reject_task_by_rez_indx, ONLY_Suppl_rej);
    _ <- set_state (s with campaign := newcampaign);
    return (SCUnit);
  od
End*)

(* 15+ *)
Definition acceptTask_typed_def:
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
End

Definition new_acceptTask_typed_def:
  new_acceptTask_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
      assert SPARSE_ERR_taskId (checkTypes params [TypeInt]);
    task_id <- scMToInt (HD params);
    task_index <<- p_get_task_index_by_id (get_campaign_tasks s.campaign) task_id;
    (_ (*indx*), rez) <- optErrM SNEX_Task task_index;
      assert SONLY_worker_acc (get_context_msgSender s.context = get_person_id $ get_agreement_supplier $ get_campaign_agreement s.campaign);
      assert SNOT_PhTasks (get_campaign_phase s.campaign = PhaseTasks);
      assert SNOT_APPROVED_task (get_task_negotiation rez = NegotiationApproved);
      assert SWRNG_COND_007 (get_agreement_negotiation $ get_campaign_agreement s.campaign = NegotiationApproved ∧ (approvedPriceExists s.campaign));
    newcampaign <<- p_accept_task_by_rez_id s.campaign rez task_id(*indx*);

    res <- set_state (s with campaign := newcampaign);
    return(SCUnit);
  od
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

Definition new_addTask_typed_def:
  new_addTask_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    assert SWRNG_COND_008 (checkTypes params [TypeInt; TypeString;
         TypeInt; TypeString; TypeInt; TypePaymentType] ∧
       isSenderCustomer s.context s.campaign ∧
       get_campaign_phase s.campaign = PhaseTasks ∧
       (*WRN*)get_agreement_negotiation $ get_campaign_agreement s.campaign = NegotiationApproved ∧
       approvedPriceExists s.campaign);

    taskId <<- TASK_HASH $ get_campaign_tasks s.campaign;
    captain_id <<- scToInt (HD params);
    captain_name <<- scToString (EL 1 params);
    worker_id <<- scToInt (EL 2 params);
    worker_name <<- scToString (EL 3 params);
    expectedGas <<- scToInt (EL 4 params);
    paymentType <<- scToPaymentType (EL 5 params);

    requestedGas <<- 0;
    suppliedGas <<- 0;
    totalGas <<- 0;
    requestTime <<- 0;
    suppliedTime <<- 0;
    completionTime <<- 0;
    paymentTime <<- 0;

    task <<- Task taskId
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

    newcampaign <<- p_add_task_in_Campaign s.campaign task;

    res <- set_state (s with campaign := newcampaign);
    return(SCUnit);
  od
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

Definition new_readyToPerformTask_typed_def:
  new_readyToPerformTask_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;

      assert SWRNG_COND_010 (checkTypes params [TypeInt] ∧
        get_campaign_phase s.campaign = PhaseTasks ∧
        get_agreement_negotiation $ get_campaign_agreement s.campaign = NegotiationApproved ∧
        approvedPriceExists s.campaign);
    task_id <- scMToInt (HD params);
    task <<- p_get_campaign_task_by_task_id s.campaign task_id;
    task <- optErrM SNEX_Task task;
      assert SWRNG_COND_009 (isSenderWorker s.context task ∧
        get_task_negotiation task = NegotiationApproved ∧
        get_task_taskStatus task = TaskAccepted);
    type <<- get_task_paymentType task;

    newcampaign <<- p_update_Campaign_tasks s.campaign (set_task_taskStatus task TaskReadyToPerform) task_id;

    res <- set_state (s with campaign := newcampaign);
    return(SCUnit);
  od
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

Definition new_requestGas_typed_def:
  new_requestGas_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;

    assert SWRNG_COND_012 (checkTypes params [TypeInt; TypeInt] ∧
      get_campaign_phase s.campaign = PhaseTasks);

    task_id <- scMToInt (HD params);
    amount <- scMToInt (EL 1 params);

    task <<- p_get_campaign_task_by_task_id s.campaign task_id;
    gasPrice <<- calculateLastPrice s.campaign;
    requestTime <<- get_context_blockNum s.context;
    task <- optErrM SNEX_Task task;
    gasPrice <- optErrM SNO_APPROVED_PRICES gasPrice;

    assert SWRNG_COND_011 (isSenderCaptain s.context task ∧
      get_agreement_negotiation $ get_campaign_agreement s.campaign = NegotiationApproved ∧
      get_task_negotiation task = NegotiationApproved ∧
      (get_task_taskStatus task = TaskReadyToPerform ∨
      get_task_taskStatus task = GasRequested));

    updated_task <<- set_task_requestTime (set_task_requestedGas (set_task_totalGas (set_task_taskStatus task GasRequested) ((get_task_totalGas task) + amount)) amount) requestTime;

    newcampaign <<- p_update_Campaign_tasks s.campaign updated_task task_id;

    res <- set_state (s with campaign := newcampaign);
    return(SCUnit);
  od
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

Definition new_completePayment_typed_def:
  new_completePayment_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;

    assert SWRNG_COND_013 (checkTypes params [TypeInt] ∧
      get_campaign_phase s.campaign = PhaseTasks ∧
      get_agreement_negotiation $ get_campaign_agreement s.campaign = NegotiationApproved ∧
      approvedPriceExists s.campaign);

    payment_id <- scMToInt (HD params);

    payment_time <<- get_context_blockNum s.context;
    payment_order <<- p_get_paymentOrder_by_id s.campaign payment_id;

    payment_order <- optErrM SNEX_Payment payment_order;

    task_id <<- get_PaymentOrder_taskId payment_order;
    task <<- p_get_campaign_task_by_task_id s.campaign task_id;

    task <- optErrM SNEX_Task task;

    assert SNOT_APPROVED_task (get_task_negotiation task = NegotiationApproved);

    newcampaign <<- p_update_Campaign_paymentOrders s.campaign (set_PaymentOrder_paymentStatus payment_order PaymentCompleted) payment_id;
    if (get_task_taskStatus task = Confirmed) then
      do
        newcampaign <<- p_update_Campaign_tasks (p_update_Campaign_paymentOrders s.campaign (set_PaymentOrder_paymentStatus payment_order PaymentCompleted) payment_id) (set_task_taskStatus task TaskCompleted) task_id;
        res <- set_state (s with campaign := newcampaign);
        return(SCUnit);
      od
    else
      do
        newcampaign <<- p_update_Campaign_paymentOrders s.campaign (set_PaymentOrder_paymentStatus payment_order PaymentCompleted) payment_id;
        res <- set_state (s with campaign := newcampaign);
        return(SCUnit);
      od
  od
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

Definition new_performTask_typed_def:
  new_performTask_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;

    assert SWRNG_COND_013 (checkTypes params [TypeInt] ∧
       get_campaign_phase s.campaign = PhaseTasks ∧
       get_agreement_negotiation $ get_campaign_agreement s.campaign = NegotiationApproved ∧
       approvedPriceExists s.campaign);

    task_id <- scMToInt (HD params);
    task <<- p_get_campaign_task_by_task_id s.campaign task_id;

    task <- optErrM SNEX_Task task;

    assert SWRNG_COND_014 (isSenderWorker s.context task ∧
                 get_task_taskStatus task = GasRequested ∧
                 get_task_negotiation task = NegotiationApproved);

    newcampaign <<- p_update_Campaign_tasks s.campaign (set_task_taskStatus task Performing) task_id;

    res <- set_state (s with campaign := newcampaign);
    return(SCUnit);
  od
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

Definition new_completeTask_typed_def:
  new_completeTask_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;

    assert SWRNG_COND_016 (checkTypes params [TypeInt; TypeInt] ∧
      get_campaign_phase s.campaign = PhaseTasks ∧
      get_agreement_negotiation $ get_campaign_agreement s.campaign = NegotiationApproved ∧
      approvedPriceExists s.campaign);

    task_id <- scMToInt (HD params);
    suppliedGas <- scMToInt (EL 1 params);
    task <<- p_get_campaign_task_by_task_id s.campaign task_id;
    suppliedTime <<- get_context_blockNum s.context;

    task <- optErrM SNEX_Task task;

    assert SWRNG_COND_015 (isSenderWorker s.context task ∧
                 get_task_taskStatus task = Performing ∧
                 get_task_negotiation task = NegotiationApproved);

    newcampaign <<- p_update_Campaign_tasks s.campaign (set_task_suppliedGas (set_task_suppliedTime task suppliedTime) suppliedGas) task_id;

    res <- set_state (s with campaign := newcampaign);
    return(SCUnit);
  od
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
  (*case (sender = get_person_id $ get_task_captain task, get_task_taskStatus task = GasRequested) of*)
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

Definition new_confirmTask_def:
  new_confirmTask (taskId:num) (suppliedGas:num) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    assert SNOT_ALLOWED_action (
      get_campaign_phase s.campaign = PhaseTasks ∧
      get_agreement_negotiation $ get_campaign_agreement s.campaign = NegotiationApproved ∧
      approvedPriceExists s.campaign);

    sender <<- get_context_msgSender s.context;
    suppliedTime <<- get_context_blockNum s.context;
    task <<- p_get_campaign_task_by_task_id s.campaign taskId;

    task <- optErrM SNEX_Task task;

    assert SNOT_APPROVED_task (get_task_negotiation task = NegotiationApproved);

    totalGas <<- get_task_totalGas task;
    price <<- get_priceChange_price $ THE $ calculateLastPrice s.campaign;
    direction <<-
      case ( (get_task_suppliedGas task) < (get_task_totalGas task), (get_task_paymentType task) = Pre) of
        (T,T) => F
      | (T,F) => T
      | (F,_) => T;

    phas <<- get_task_paymentType task;
    make_payment_order <<-
      case phas of
      | Pre     => (PaymentOrder (price * if suppliedGas < totalGas
                                    then totalGas - suppliedGas
                                    else suppliedGas - totalGas) 0 0 taskId WaitingForPayment direction)
      | Post    => (PaymentOrder (suppliedGas * price) 0 0 taskId WaitingForPayment direction)
      | Delayed => (PaymentOrder (suppliedGas * price) (get_task_paymentTime task) 0 taskId WaitingForPayment direction);

    assert SONLY_Captain (sender = get_person_id $ get_task_captain task);
    assert SNO_GAS_REQUESTS (get_task_taskStatus task = Performing);

    if (suppliedGas = totalGas ∧ phas = Pre) then
      do
        newcampaign <<- p_update_Campaign_tasks s.campaign (set_task_taskStatus task TaskCompleted) taskId;
        res <- set_state (s with campaign := newcampaign);
        return(SCUnit);
      od
    else
      do
        newcampaign <<- set_campaign_paymentOrders (p_update_Campaign_tasks s.campaign (set_task_taskStatus task Confirmed) taskId) (( get_campaign_paymentOrders s.campaign) ++ [make_payment_order]);
        res <- set_state (s with campaign := newcampaign);
        return(SCUnit);
      od
  od
End

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

Definition new_confirmTask_typed_def:
  new_confirmTask_typed (params : SCvalue list) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    assert SBAD_TYPE (checkTypes params [TypeInt; TypeInt]);

    taskId <- scMToInt (HD params);
    suppliedGas <- scMToInt (EL 1 params);

    _ <- new_confirmTask taskId suppliedGas;
    return (SCUnit);
  od
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

Definition constructor_typed_def:
  constructor_typed (customer_id:num) (customer_name:string) (supplier_id:num) (supplier_name:string) (agreement_details:string) (bank_addr:num) : (State, SCvalue, state_exn) M =
  do
    s <- get_state;
    pc <<- (Person customer_id customer_name);
    ps <<- (Person supplier_id supplier_name);
    ad <<- (AgreementDetails agreement_details bank_addr);
    ag <<- (Agreement WaitingSupplier pc ps ad);

    newcampaign <<- (Campaign ag [] WaitingCustomer [] PhaseAgreement []);
    _ <- set_state (s with campaign := newcampaign);
    return(SCUnit);
  od
End

(*MOREFUNCS --------------------------------------------------------------------- *)
Definition constructor_def:
  constructor context params campaign =
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

Definition new_chooseFunction_def:
new_chooseFunction (f:num) =
    case (f : num) of
    | 5 => new_changeAgreement_typed
    |  _ => (λparams. fail SNEX_function)
End

Definition new_execute_def:
new_execute (f:num) (params:SCvalue list) : (State, SCvalue, state_exn) M =
  do
    v <- new_chooseFunction f params;
    return v
  od
End

(*PRORS ------------------------------------------------------------------------ *)
Definition IDS_ARE_UNIQUE_DEF:
    IDS_ARE_UNIQUE tasks =
        let taskIds = MAP get_task_id tasks
        in ALL_DISTINCT taskIds (*∀x. MEM x taskIds ⇒ UNIQUE x taskIds*)
End

(*THEOREMS --------------------------------------------------------------------- *)

Theorem checkTypes_LENGTH:
    ∀ params paramTypes .
     checkTypes params paramTypes ⇒
     LENGTH params = LENGTH paramTypes
Proof
  GEN_TAC >> GEN_TAC >>
  REWRITE_TAC[checkTypes_def] >>
  ‘paramTypes = MAP I paramTypes’ by rw[listTheory.MAP_ID] >>
  pop_assum SUBST1_TAC >>
  rw[listTheory.MAP_EQ_EVERY2]
QED

Theorem p_add_task_in_Campaign_ALL_DISTINCT:
    ∀ taskIds campaign task .
      taskIds = MAP get_task_id $ get_campaign_tasks campaign ∧
      ALL_DISTINCT taskIds ∧
      ¬ MEM (get_task_id task) taskIds ⇒

      ALL_DISTINCT (MAP get_task_id $ get_campaign_tasks (p_add_task_in_Campaign campaign task))
Proof
  rpt STRIP_TAC >>
  Cases_on ‘campaign’ >>
  FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def, p_add_task_in_Campaign_def,
                        set_campaign_tasks_def] >>
  rw[]
QED


Theorem INDEX_SUC:
  ∀ i P t x a.
    INDEX_FIND i P t = SOME (x, a) ⇒
    INDEX_FIND (SUC i) P t = SOME (SUC x, a)
Proof
  Induct_on ‘t’ >>
  rw[INDEX_FIND_def]
QED


Theorem get_by_taskId_correct:
  ∀ tasks campaign taskId .
    tasks = get_campaign_tasks campaign ∧
    MEM taskId (MAP get_task_id $ tasks) ⇒

    ∃ tsk . p_get_campaign_task_by_task_id campaign taskId = SOME tsk
Proof
  rpt STRIP_TAC >>
  Cases_on ‘campaign’ >>
  FULL_SIMP_TAC (srw_ss()) [get_campaign_tasks_def, p_get_campaign_task_by_task_id_def,
                        set_campaign_tasks_def, FIND_def] >>
  rw[] >>
  Induct_on ‘l’ >>
  rw[INDEX_FIND_def] >>
  FULL_SIMP_TAC (srw_ss()) [get_task_id_def, MAP, MEM, INDEX_FIND_def] >>
  Cases_on ‘z’ >>
  Q.EXISTS_TAC ‘(SUC q, r)’ >>
  ONCE_REWRITE_TAC[DECIDE “1 = SUC 0”] >>
  metis_tac[INDEX_SUC]
QED

(* get agreement, positive case *)
Theorem getAgreement_senderEqCustPersID:
  ∀context. ∀campaign.
    let sender = get_context_msgSender context;
        agreement = get_campaign_agreement campaign;
        customer = get_agreement_customer agreement;
        custPersID = get_person_id customer;
    in
    (get_context_msgSender context = custPersID) ⇒
    getAgreement_typed context params campaign = Ret (SCCampaign campaign) (SCAgreement (get_campaign_agreement campaign))
Proof
  rpt GEN_TAC >>
  PURE_REWRITE_TAC [getAgreement_typed_def] >>
  rewrite_tac [LET_THM] >>
  FULL_SIMP_TAC bool_ss []
QED

(* reject agreement, positive case *)
(* REDO
Theorem rejectAgreement_positive:
  ∀context. ∀campaign.
  let
    sender = (get_context_msgSender context);
    agreement = (get_campaign_agreement campaign);
    supplier = (get_agreement_supplier agreement);
    persID = (get_person_id supplier);
  in
    (sender = persID) ⇒
    ((get_campaign_phase campaign) = PhaseAgreement) ⇒
    ((get_campaign_negotiation campaign) = WaitingSupplier) ⇒
    ∃NC.
      rejectAgreement_typed context params campaign = Some (SCCampaign NC)
Proof
  rw [] >>
  simp [rejectAgreement_typed_def] >>
(*  rpt GEN_TAC >>
  PURE_REWRITE_TAC [rejectAgreement_typed_def] >>
  rewrite_tac [LET_THM] >>
  FULL_SIMP_TAC bool_ss [] >>
  rpt DISCH_TAC >>
  EXISTS_TAC ``(set_campaign_agreement campaign
    (set_agreement_negotiation (get_campaign_agreement campaign) WaitingCustomer))`` >>
  REFL_TAC *)
QED
*)

(* approve agreement, positive case *)
(* REDO
Theorem approveAgreement_positive:
  ∀context. ∀campaign.
  let
    sender = (get_context_msgSender context);
    agreement = (get_campaign_agreement campaign);
    supplier = (get_agreement_supplier agreement);
    persID = (get_person_id supplier);
  in
    (sender = persID) ⇒
    ((get_campaign_phase campaign) = PhaseAgreement) ⇒
    ((get_campaign_negotiation campaign) = WaitingSupplier) ⇒
    ∃NC.
    approveAgreement_typed context params campaign = Some NC
Proof
  rpt GEN_TAC >>
  PURE_REWRITE_TAC [approveAgreement_typed_def] >>
  rewrite_tac [LET_THM] >>
  FULL_SIMP_TAC bool_ss [] >>
  rpt DISCH_TAC >>
  EXISTS_TAC ``(SCCampaign campaign)`` >>
  REFL_TAC
QED
*)

(* approve agreement, negative case *)
(*Theorem approveAgreement_negative:
  ∀context. ∀campaign.
  let
    sender = (get_context_msgSender context);
    agreement = (get_campaign_agreement campaign);
    supplier = (get_agreement_supplier agreement);
    persID = (get_person_id supplier);
  in
    (~(sender = persID) \/
    ~((get_campaign_phase campaign) = PhaseAgreement) \/
    ~((get_campaign_negotiation campaign) = WaitingSupplier)) ⇒
    ∃st.
    approveAgreement context params campaign = None st
Proof
  let
    fun tt s = (FULL_SIMP_TAC bool_ss []) >> (EXISTS_TAC s) >> rpt REFL_TAC
    val ttt = ASM_CASES_TAC ``get_context_msgSender context = get_person_id (get_agreement_supplier (get_campaign_agreement campaign))`` >> (FULL_SIMP_TAC bool_ss [])  >| (map tt [``"Supplier is not allowed to reject at this point"``, ``"Only supplier is allowed to reject at this point"``])
  in
    (
    rpt GEN_TAC >>
    PURE_REWRITE_TAC [approveAgreement_def] >>
    rewrite_tac [LET_THM] >>
    FULL_SIMP_TAC bool_ss [] >>
    STRIP_TAC
    ) >| ([tt ``"Only supplier is allowed to reject at this point"``, ttt, ttt])
  end
QED
*)

Theorem getPriceChangesLength_trivial:
  ∀params context campaign.
    isSenderCustomer context campaign ∧
    (¬ NULL (get_campaign_priceChanges campaign)) ⇒
∃x. ∃y. getPriceChangesLength_typed context params campaign = Ret x y
Proof
  rpt STRIP_TAC >>
  PURE_REWRITE_TAC [getPriceChangesLength_typed_def] >>
  FULL_SIMP_TAC bool_ss [] >>
  EXISTS_TAC ``(SCCampaign campaign)`` >>
  EXISTS_TAC ``(SCInt (LENGTH (get_campaign_priceChanges campaign)))`` >>
  REFL_TAC
QED;

(* Adding price changes is possible only with an agreed Agreement *)
Theorem priceChangeAgreement:
  ∀context. ∀campaign.
  let
    sender = (get_context_msgSender context);
    agreement = (get_campaign_agreement campaign);
    supplier = (get_agreement_supplier agreement);
    persID = (get_person_id supplier);
  in
    (sender = persID) ⇒
    ((get_campaign_phase campaign) = PhaseTasks) ⇒
     (∃NC: Campaign . createPriceChange_typed context params campaign = Some (SCCampaign NC) )⇒
     ((get_agreement_negotiation agreement) = NegotiationApproved)
Proof
  rw (createPriceChange_typed_def :: createPriceChange_def :: const_defs)
QED;

(** Lemmas **)
(* Lemma for trivial cases *)
Theorem lem01:
  n=0 \/ n=1 ⇒
  execute n context params campaign0 = NEX_function
Proof
  STRIP_TAC >> (
  REWRITE_TAC[execute_def, chooseFunction_def] >>
  FULL_SIMP_TAC arith_ss [] )
QED

Definition distIDs_def:
distIDs tasks0 =
    (∀x. ∀y. ( MEM x tasks0 /\ MEM y tasks0 ) /\ (get_task_id x = get_task_id y) ⇒  x=y)
End

Definition distTaskIDs_def:
distTaskIDs campaign0 = distIDs (get_campaign_tasks campaign0)
End

Theorem Campaign_scTo_retr:
scToCampaign (SCCampaign campaign0) = campaign0
Proof
  rw [scToCampaign_def]
QED

(* CASE tactics *)

(* Tactic GET CASE ARGUMENT *)
val get_case_arg = get_first_arg

(* Tactic GET FIRST TERM *)
val term_to_string : term -> string = fst (valOf Parse.stdprinters)
val type_to_string : hol_type -> string = snd (valOf Parse.stdprinters)

val get_first_term = (el 1) o term_as_list
(*
fun get_first_term te = get_first_term (fst (dest_comb te)) handle _ => te
(* example: "get_first_term ``approveAgreement context params campaign0``";
   gives ``approveAgreement`` *)
*)

(* Predicate that all task id of a campaign are distinct *)
Definition atid_def:
atid campaign = ALL_DISTINCT (MAP get_task_id (get_campaign_tasks campaign))
End

Definition casestmnt_def:
casestmnt campaign1scopt =
  case campaign1scopt of
  | Some (SCCampaign campaign1) => atid campaign1
  | Ret (SCCampaign campaign1) B => atid campaign1
  | None s => T
  | _ => F
End

(* Statement about different IDs for particular number of function *)
Definition distmnt_def:
distmnt f = ∀context. ∀params. ∀campaign0.
  atid campaign0 ⇒
  casestmnt (execute f context params campaign0)
End

val tac01 : tactic =
  simp [distmnt_def, casestmnt_def] >>
  rpt GEN_TAC >>
  rw [lem01]

val casestmnt_tac : tactic
 = fn (v as (asl, w)) => ((Cases_on_term (w |> get_first_arg |> get_if_cond)) >> simp [casestmnt_def])  v

val start_tac : tactic =
  simp [distmnt_def] >>
  rpt GEN_TAC >>
  rw [] >>
  simp [execute_def, chooseFunction_def]

fun lookup key ((k,v)::pairs) =
        if k = key then v else lookup key pairs

val name_tac: tactic =
   fn (v as (asl, w)) =>
   let
     val x = (fst (valOf Parse.stdprinters) (get_first_term (get_first_arg w))) ^ "_def"
     val y = lookup x (current_definitions())
   in
     (simp [y] >> simp const_defs) v
   end

val deflist = (casestmnt_def::const_defs)

val partsimp = [simp deflist, all_tac]

val if_inside_casestmnt_tac : tactic =
 ((fn x => (Cases_on_term o get_first_arg o get_first_arg o snd) x x):tactic)

val addErr_inside_casestmnt_tac : tactic =
 ((fn x => (Cases_on_term o get_second_arg o get_first_arg o snd) x x):tactic)

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

Theorem distmnt0:
distmnt 0
Proof
 tac01 >>
 simp const_defs
QED

Theorem distmnt1:
distmnt 1
Proof
 tac01 >>
 simp const_defs
QED

Theorem distmnt2:
distmnt 2
Proof
  simp [distmnt_def] >>
  rw [] >>
  simp [execute_def, chooseFunction_def] >>
  simp [getAgreement_typed_def] >>
  ntac 2 casestmnt_tac >>
  simp const_defs
QED

Theorem sca_lemma_lem:
 (get_campaign_tasks
  (set_campaign_agreement campaign0 agreement)
 = get_campaign_tasks campaign0)
Proof
   Cases_on `campaign0` >>
   simp [get_campaign_tasks_def, set_campaign_agreement_def]
QED

Theorem sca_lemma:
atid campaign0 ⇒  atid (set_campaign_agreement campaign0 agreement)
Proof
   simp [atid_def] >>
   rw [sca_lemma_lem]
QED

(* old
Theorem st4_lemma_lem:
 (get_campaign_tasks (set_campaign_bankAddress campaign0 agreement) = get_campaign_tasks campaign0)
Proof
   Cases_on `campaign0` >>
   simp [get_campaign_tasks_def, set_campaign_bankAddress_def]
QED

Theorem st4_lemma:
atid campaign0 ⇒  atid (set_campaign_bankAddress campaign0 x)
Proof
   simp [atid_def] >>
   rw [st4_lemma_lem]
QED
*)

Theorem scph_lemma_lem:
 (get_campaign_tasks (set_campaign_phase campaign0 agreement) = get_campaign_tasks campaign0)
Proof
   Cases_on `campaign0` >>
   simp [get_campaign_tasks_def, set_campaign_phase_def]
QED

Theorem scph_lemma:
atid campaign0 ⇒  atid (set_campaign_phase campaign0 x)
Proof
   simp [atid_def] >>
   rw [scph_lemma_lem]
QED

Theorem scpc_lemma_lem:
 (get_campaign_tasks (set_campaign_priceChanges campaign0 agreement) = get_campaign_tasks campaign0)
Proof
   Cases_on `campaign0` >>
   simp [get_campaign_tasks_def, set_campaign_priceChanges_def]
QED

Theorem scpc_lemma:
atid campaign0 ⇒  atid (set_campaign_priceChanges campaign0 x)
Proof
   simp [atid_def] >>
   rw [scpc_lemma_lem]
QED

Theorem scpo_lemma_lem:
 (get_campaign_tasks (set_campaign_paymentOrders campaign0 agreement) = get_campaign_tasks campaign0)
Proof
   Cases_on `campaign0` >>
   simp [get_campaign_tasks_def, set_campaign_paymentOrders_def]
QED

Theorem scpo_lemma:
atid campaign0 ⇒  atid (set_campaign_paymentOrders campaign0 x)
Proof
   simp [atid_def] >>
   rw [scpo_lemma_lem]
QED

Theorem distmnt3:
distmnt 3
Proof
  simp [distmnt_def] >>
  rw [] >>
  simp [execute_def, chooseFunction_def] >>
  simp [rejectAgreement_typed_def] >>
  simp const_defs >>
  ntac 4 casestmnt_tac >>
  irule sca_lemma >>
  simp []
QED

Theorem distmnt4:
distmnt 4
Proof
  start_tac >>
  name_tac >>
  simp const_defs >>
  ntac 4 casestmnt_tac
QED

Theorem distmnt5:
  distmnt 5
Proof
  start_tac >>
  name_tac >>
  simp [changeAgreement_def] >>
  simp const_defs >>
  ntac 5 casestmnt_tac >>
  (* irule st4_lemma >> *)
  irule sca_lemma >>
  irule scph_lemma >>
  simp []
QED

Theorem distmnt6:
distmnt 6
Proof
  start_tac >>
  name_tac >>
  simp const_defs >>
  ntac 1 casestmnt_tac
QED

Theorem distmnt7:
distmnt 7
Proof
  start_tac >>
  name_tac >>
  simp const_defs >>
  ntac 1 casestmnt_tac
QED

Theorem distmnt8:
distmnt 8
Proof
  start_tac >>
  name_tac >>
  simp const_defs >>
  ntac 1 casestmnt_tac >>
  irule scpc_lemma >>
  simp []
QED

Theorem distmnt9:
distmnt 9
Proof
  start_tac >>
  name_tac >>
  simp const_defs >>
  ntac 1 casestmnt_tac >>
  irule scpc_lemma >>
  simp []
QED

Theorem distmnt10:
distmnt 10
Proof
  start_tac >>
  name_tac >>
  simp const_defs >>
  ntac 1 casestmnt_tac >>
  irule scph_lemma >>
  simp []
QED

Theorem distmnt11:
distmnt 11
Proof
  start_tac >>
  name_tac >>
  simp [createPriceChange_def] >>
  simp const_defs >>
  ntac 2 casestmnt_tac >>
  simp [p_add_priceChange_in_Campaign_def] >>
  irule scpc_lemma >>
  simp []
QED

Theorem distmnt12:
distmnt 12
Proof
  start_tac >>
  name_tac >>
  (Cases_on `params` >> simp deflist ) >>
  (Cases_on `t` >> simp deflist) >>
  (Cases_on `h` >> simp deflist) >>
  (Cases_on `p_get_task_index_by_id (get_campaign_tasks campaign0) n` >> simp []) >>
  (Cases_on `x` >> simp deflist) >>
  ntac 1 casestmnt_tac
QED

Theorem getset_campaign_tasks:
  (get_campaign_tasks (set_campaign_tasks campaign0 x)) = x
Proof
  Cases_on `campaign0` >> simp [get_campaign_tasks_def, set_campaign_tasks_def]
QED

Theorem getset_task_id_negotiation:
  (get_task_id (set_task_negotiation t n)) = (get_task_id t)
Proof
  Cases_on `t` >> simp [get_task_id_def, set_task_negotiation_def]
QED

Theorem getset_task_id_taskStatus:
  (get_task_id (set_task_taskStatus t n)) = (get_task_id t)
Proof
  Cases_on `t` >> simp [get_task_id_def, set_task_taskStatus_def]
QED

Theorem getset_task_id_requestTime:
  (get_task_id (set_task_requestTime t n)) = (get_task_id t)
Proof
  Cases_on `t` >> simp [get_task_id_def, set_task_requestTime_def]
QED

Theorem getset_task_id_requestedGas:
  (get_task_id (set_task_requestedGas t n)) = (get_task_id t)
Proof
  Cases_on `t` >> simp [get_task_id_def, set_task_requestedGas_def]
QED

Theorem getset_task_id_suppliedTime:
  (get_task_id (set_task_suppliedTime t n)) = (get_task_id t)
Proof
  Cases_on `t` >> simp [get_task_id_def, set_task_suppliedTime_def]
QED

Theorem getset_task_id_suppliedGas:
  (get_task_id (set_task_suppliedGas t n)) = (get_task_id t)
Proof
  Cases_on `t` >> simp [get_task_id_def, set_task_suppliedGas_def]
QED

Theorem getset_task_id_totalGas:
  (get_task_id (set_task_totalGas t n)) = (get_task_id t)
Proof
  Cases_on `t` >> simp [get_task_id_def, set_task_totalGas_def]
QED

Theorem REL_lemma:
∀tasks. ∀q. ∀task. LIST_REL (λx y. get_task_id x = get_task_id y) tasks (UPDATE_BY_ID task q tasks)
Proof
  rpt gen_tac >>
  simp [UPDATE_BY_ID_def] >>
  simp [listTheory.LIST_REL_MAP2] >>
  irule quotient_listTheory.LIST_REL_REFL >>
  ntac 2 gen_tac >>
  irule boolTheory.IMP_ANTISYM_AX >>
  CONJ_TAC
  >| [
    rw [] >>
    simp [boolTheory.FUN_EQ_THM] >>
    gen_tac >>
    simp [get_task_id_def]
  ,
    simp [boolTheory.FUN_EQ_THM] >>
    rw [get_task_id_def]
  ]
QED

Theorem replacing_fn_lemma_lem2:
∀tasks q task. (MAP get_task_id tasks) =
 (MAP get_task_id (UPDATE_BY_ID task q
  tasks))
Proof
  simp [listTheory.MAP_EQ_EVERY2] >>
  rw []
  >| [
    rw [UPDATE_BY_ID_def]
  ,
    rw [REL_lemma]
  ]
QED

Theorem replacing_fn_lemma_lem1:
∀campaign0 q task.
atid campaign0
⇒
atid
(set_campaign_tasks campaign0
 (UPDATE_BY_ID task q
  (get_campaign_tasks campaign0)))
Proof
  rpt gen_tac >>
  simp [atid_def] >>
  simp [getset_campaign_tasks] >>
  MP_TAC (SPECL [``(get_campaign_tasks campaign0)``, ``(q:num)``, ``(task:Task)``]  replacing_fn_lemma_lem2) >>
  rw []
QED

Theorem replacing_fn_lemma:
∀(value:α) (setter:Task->α->Task) (campaign0:Campaign) (r:Task) (q:num).
atid (campaign0 :Campaign)
⇒
atid
 (p_base_task_replacing_fn
  (setter,value) (campaign0 :Campaign)
   (r :Task) (q :num))
Proof
  rpt gen_tac >>
  simp [p_base_task_replacing_fn_def] >>
  MP_TAC (SPECL [``(campaign0:Campaign)``, ``(q:num)``, ``((setter (r:Task) (value:α)):Task)``]
    (replacing_fn_lemma_lem1)
  ) >>
  rw []
QED


Theorem distmnt13:
distmnt 13
Proof
  start_tac >>
  name_tac >>
  simp [base_task_fn_def] >>
  (Cases_on `params` >| partsimp ) >>
  (Cases_on `t` >| [all_tac, simp (casestmnt_def::const_defs)] ) >>
  (Cases_on `h` >> simp deflist) >>  simp [GSYM casestmnt_def] >>
  (Cases_on `p_get_task_index_by_id (get_campaign_tasks campaign0) n` >> simp [casestmnt_def]) >> simp [GSYM casestmnt_def] >>
  (Cases_on `x` >> simp deflist) >> simp [GSYM casestmnt_def] >>
  ntac 1 casestmnt_tac >> simp [GSYM casestmnt_def] >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]),all_tac,(simp [casestmnt_def])]) >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]),all_tac]) >>
  simp [casestmnt_def] >>
  simp [p_approve_task_by_rez_id_def] >>
  MP_TAC (INST_TYPE [alpha |-> ``:Negotiation``] replacing_fn_lemma) >>
  rw []
QED

Theorem distmnt14:
distmnt 14
Proof
  start_tac >>
  name_tac >>
  (Cases_on `params` >|
            [simp ([base_task_fn_def] @ deflist) , all_tac]
  ) >>
  (Cases_on `t` >| [ all_tac, simp [base_task_fn_def] >> simp deflist ]) >>

  simp [base_task_fn_def] >>
  (Cases_on `h` >> simp deflist) >>
  (Cases_on `p_get_task_index_by_id (get_campaign_tasks campaign0) n` >> simp [casestmnt_def]) >> simp [GSYM casestmnt_def] >>
  (Cases_on `x` >> simp deflist) >> simp [GSYM casestmnt_def] >>
  ntac 1 casestmnt_tac >> simp [GSYM casestmnt_def] >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]),all_tac,(simp [casestmnt_def])]) >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]), all_tac]) >>
  simp [casestmnt_def] >>
  simp [p_reject_task_by_rez_id_def] >>
  MP_TAC (INST_TYPE [alpha |-> ``:Negotiation``] replacing_fn_lemma) >>
  rw []
QED

Theorem distmnt15:
distmnt 15
Proof
  start_tac >>
  name_tac >>
  (Cases_on `params` >| partsimp ) >>
  (Cases_on `t` >| [simp const_defs, all_tac] ) >>
  (Cases_on `h` >> simp deflist) >>  simp [GSYM casestmnt_def] >>
  (Cases_on `p_get_task_index_by_id (get_campaign_tasks campaign0) n` >> simp [casestmnt_def]) >> simp [GSYM casestmnt_def] >>
  (Cases_on `x` >> simp deflist) >> simp [GSYM casestmnt_def] >>
  ntac 1 casestmnt_tac >> simp [GSYM casestmnt_def] >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]),all_tac,(simp [casestmnt_def])]) >>
  (if_inside_casestmnt_tac >> simp [casestmnt_def]) >>
  casestmnt_tac >>
  simp [p_accept_task_by_rez_id_def] >>
  MP_TAC (INST_TYPE [alpha |-> ``:TaskStatus``] replacing_fn_lemma) >>
  rw []
QED

Theorem MEM_FU:
∀ y. ∀ l. ∀ f. MEM (y:α) (l:α list) ⇒  MEM ((f:α->β) y) (MAP f l)
Proof
  ntac 3 gen_tac >>
  rw [MEM_MAP] >>
  exists_tac ``(y:α)`` >>
  rw []
QED

Theorem all_dist_map_lem:
ALL_DISTINCT (MAP get_task_id (l :Task list))
 ⇒
MEM x l
 ⇒
MEM y l
 ⇒
get_task_id x = get_task_id y
 ⇒
x = y
Proof
  Induct_on `l`
  >| [
    simp []
  ,
    simp [] >>
    strip_tac >>
    rw []
    >| [
      (let
        val t1 = (INST_TYPE [alpha |-> ``:Task``, beta |-> ``:num`` ] MEM_FU)
        val t2 = (SPECL [``(y:Task)``, ``(l:Task list)``,  ``get_task_id``] t1)
      in
        mp_tac t2
      end) >>
      rw [] >>
      FULL_SIMP_TAC std_ss []
    ,
      (let
        val t1 = (INST_TYPE [alpha |-> ``:Task``, beta |-> ``:num`` ] MEM_FU)
        val t2 = (SPECL [``(x:Task)``, ``(l:Task list)``,  ``get_task_id``] t1)
      in
        mp_tac t2
      end)  >>
      rw [] >>
      FULL_SIMP_TAC std_ss []
    ,
      FULL_SIMP_TAC std_ss []
    ]
  ]
QED

Theorem tech_lem:
ALL_DISTINCT (MAP get_task_id (l :Task list))
 ⇒
ALL_DISTINCT (l :Task list)
Proof
  rw [] >>
  irule $ INST_TYPE [alpha |-> ``:Task``, beta |-> ``:num``] ALL_DISTINCT_MAP >>
  exists_tac ``(get_task_id)`` >>
  simp []
QED


Theorem distmnt16:
distmnt 16
Proof
  start_tac >>
  simp $ casestmnt_def::const_defs
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
¬MEM (SUC (FOLDR MAX 0 (l:num list))) l
Proof
  irule boolTheory.MONO_NOT >>
  exists_tac `` (SUC (FOLDR MAX 0 l)) ≤ (FOLDR MAX 0 l)`` >>
  conj_tac
  >| [
    rw []
  ,
    simp [leq_max_list]
  ]
QED

(* deprecated
Theorem HASH_IS_GOOD:
¬MEM (TASK_HASH (tasks)) (MAP get_task_id tasks)
Proof
  simp [TASK_HASH_DEF] >>
  simp [maxsucnel]
QED*)

Theorem HASH_IS_GOOD:
¬MEM (TASK_HASH (tasks)) (MAP Task_taskID tasks)
Proof
  simp [TASK_HASH_DEF] >>
  simp [get_task_id_def] >>
  simp [maxsucnel]
QED

Theorem property7:
execute 17 context params campaign0 = Some $ SCCampaign campaign1
  ⇒
let
  tasks = get_campaign_tasks $ campaign1
in
  ~MEM (get_task_id $ HD $ tasks) (MAP get_task_id $ TL $ tasks)
Proof (* get $ HD $ get_campaign_tasks $ campaign1 *)
  simp [execute_def, chooseFunction_def, addTask_typed_def] >>
  simp const_defs >>
  rw [] >>
  simp [p_add_task_in_Campaign_def] >>
  simp [getset_campaign_tasks] >>
  simp [get_task_id_def] >>
  simp [HASH_IS_GOOD]
QED

Theorem distmnt17:
distmnt 17
Proof
  start_tac >>
  name_tac >>
  simp const_defs >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  simp [casestmnt_def] >>
  simp [atid_def] >>
  irule p_add_task_in_Campaign_ALL_DISTINCT >>
  exists_tac “MAP get_task_id (get_campaign_tasks campaign0)” >>
  strip_tac
  >| [
    UNDISCH_TAC “atid (campaign0 :Campaign)” >>
    simp [atid_def]
  ,
    strip_tac
    >| [
      simp [get_task_id_def] >>
      simp [HASH_IS_GOOD]
    ,
      simp []
    ]
  ]
QED

Theorem find_prop_lem:
  ∀M. ∀l. INDEX_FIND (M :num) (P :α -> bool) (l :α list ) = SOME (z :num # α)
  ⇒
  P (SND z)
Proof
  Induct_on `l`
  >| [
    simp [INDEX_FIND_def]
  ,
    GEN_TAC >>
    GEN_TAC >>
    simp [INDEX_FIND_def] >>
    Cases_on `P h` >|
    [
      rw [] >>
      simp []
    ,
      simp [] >>
      rw [] >>
      first_x_assum (qspecl_then [‘SUC M’] mp_tac) >>
      rw []
    ]
  ]
QED

Theorem find_prop:
∀ P. ∀ l. ∀ x. FIND (P:α->bool) (l:α list) = SOME x ⇒ P x
Proof
  ntac 3 gen_tac >>
  simp [FIND_def] >>
  rw [] >>
  irule find_prop_lem >>
  exists_tac ``(0:num)`` >>
  exists_tac ``(l:α list)`` >>
  rw []
QED

Theorem smalllem:
∀n. ∀x. ((λy. get_task_id y = n) x) ⇒ ((n:num) = get_task_id (x:Task) )
Proof
  FULL_SIMP_TAC std_ss []
QED

Theorem task_by_task_id_lemma:
p_get_campaign_task_by_task_id (campaign0:Campaign) (n:num) = SOME x
 ⇒
get_task_id x = n
Proof
  simp [p_get_campaign_task_by_task_id_def] >>
  rw [] >>
  SYM_TAC >>
  irule smalllem >>
  (let
    val q = (INST_TYPE [alpha |-> ``:Task``] find_prop)
    val q1 = SPECL [``(λx. get_task_id x = n)``, ``(l:Task list)``, ``(x:Task)``] q
  in
    irule q1
  end) >>
  exists_tac ``(get_campaign_tasks (campaign0 :Campaign))`` >>
  rw []
QED

Theorem getset_campaign_tasks:
(get_campaign_tasks (set_campaign_tasks campaign0 ta)) = ta
Proof
  Cases_on `campaign0` >>
  simp [get_campaign_tasks_def, set_campaign_tasks_def]
QED

Theorem update_preserves_taskid:
get_task_id (y :Task) = (n :num)
 ⇒
(MAP get_task_id (get_campaign_tasks (p_update_Campaign_tasks campaign0 y n)))
 = (MAP get_task_id (get_campaign_tasks campaign0))
Proof
  rw [] >>
  simp [p_update_Campaign_tasks_def] >>
  simp [getset_campaign_tasks] >>
  simp [MAP_MAP_o] >>
  rw [] >>
  irule MAP_CONG >>
  rw []
QED

Theorem p_update_Campaign_tasks_lemma:
atid campaign0
 ⇒
get_task_id y = n
 ⇒
atid (p_update_Campaign_tasks campaign0 (y:Task) (n:num))
Proof
  simp [atid_def] >>
  rw [update_preserves_taskid]
QED

Theorem distmnt18:
distmnt 18
Proof
  start_tac >>
  name_tac >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]), all_tac]) >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  simp [casestmnt_def] >>
  irule p_update_Campaign_tasks_lemma >>
  simp [] >>
  simp [getset_task_id_taskStatus] >>
  irule task_by_task_id_lemma >>
  exists_tac ``(campaign0:Campaign)`` >>
  simp []
QED

Theorem distmnt19:
distmnt 19
Proof
  start_tac >>
  name_tac >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]), all_tac]) >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]), all_tac]) >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  simp [casestmnt_def] >>
    irule p_update_Campaign_tasks_lemma >>
    simp [] >>
  simp [getset_task_id_requestTime] >>
  simp [getset_task_id_requestedGas] >>
  simp [getset_task_id_totalGas] >>
  simp [getset_task_id_taskStatus] >>
    irule task_by_task_id_lemma >>
    exists_tac ``(campaign0:Campaign)`` >>
     simp []
QED


Theorem paymentOrder_and_tasks:
atid campaign0
 ⇒
atid (p_update_Campaign_paymentOrders campaign0 paymentOrder (n:num))
Proof
 simp [p_update_Campaign_paymentOrders_def] >>
 simp [scpo_lemma]
QED

Theorem distmnt20:
distmnt 20
Proof
  start_tac >>
  rw [completePayment_typed_def, casestmnt_def] >>
  simp const_defs >>
NTAC 4 if_inside_casestmnt_tac 
>|
[
  (irule p_update_Campaign_tasks_lemma >> simp []) >>
  rw []
  >| [
    simp [paymentOrder_and_tasks]
  ,
    simp [getset_task_id_taskStatus] >>
    irule task_by_task_id_lemma >>
    exists_tac ``(campaign0:Campaign)`` >>
    simp []
  ]
,
  simp [casestmnt_def] >>
  simp [paymentOrder_and_tasks]
]
QED

Theorem distmnt21:
distmnt 21
Proof
  start_tac >>
  name_tac >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]), all_tac]) >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  simp [casestmnt_def] >>
  (irule p_update_Campaign_tasks_lemma >> simp []) >>
    simp [getset_task_id_taskStatus] >>
    irule task_by_task_id_lemma >>
    exists_tac ``(campaign0:Campaign)`` >>
    simp []
QED

Theorem distmnt22:
distmnt 22
Proof
  start_tac >>
  name_tac >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]), all_tac]) >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  simp [casestmnt_def] >>
  (irule p_update_Campaign_tasks_lemma >> simp []) >>
    simp [getset_task_id_taskStatus] >>
    simp [getset_task_id_suppliedGas] >>
    simp [getset_task_id_suppliedTime] >>
    irule task_by_task_id_lemma >>
    exists_tac ``(campaign0:Campaign)`` >>
    simp []
QED

Theorem setPaymentOrder_and_tasks:
atid campaign0
 ⇒
atid (set_campaign_paymentOrders campaign0 paymentOrders)
Proof
  simp [atid_def] >>
  Cases_on `(campaign0:Campaign)` >>
  simp [set_campaign_paymentOrders_def] >>
  simp [atid_def] >>
  simp [get_campaign_tasks_def]
QED

Theorem distmnt23:
distmnt 23
Proof
  start_tac >>
  simp [confirmTask_typed_def] >>
  simp const_defs >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]),all_tac]) >>
  simp [confirmTask_def] >>
  (*name_tac >> *)
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]),all_tac]) >>
  simp const_defs >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]),all_tac]) >>
  (if_inside_casestmnt_tac >| [(simp [casestmnt_def]),all_tac]) >>
  simp const_defs >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])]) >>
  (if_inside_casestmnt_tac >| [all_tac, (simp [casestmnt_def])])
  >| [
    simp [casestmnt_def] >>
    (irule p_update_Campaign_tasks_lemma >> simp []) >>
    simp [getset_task_id_taskStatus] >>
    irule task_by_task_id_lemma >>
    exists_tac ``(campaign0:Campaign)`` >>
    simp []
  ,
    irule setPaymentOrder_and_tasks >>
    (irule p_update_Campaign_tasks_lemma >> simp []) >>
    simp [getset_task_id_taskStatus] >>
    irule task_by_task_id_lemma >>
    exists_tac ``(campaign0:Campaign)`` >>
    simp []
  ]
QED

Theorem distmnt24:
distmnt 24
Proof
  start_tac >>
  simp $ casestmnt_def::const_defs
QED

val nextCase: tactic =
let
  val var1 = "n"
  val var2 = "n'"
in
     (
       rpt (Cases_on [QUOTE (var1 ^ ":num")]) >>
       rpt (Cases_on [QUOTE (var2 ^ ":num")])
     )
end

Theorem differentId:
  ∀n. distmnt n
Proof
  GEN_TAC >>
  Cases_on `n:num` >> rw [distmnt0] >>
  Cases_on `n':num` >> rw [distmnt1] >>
  Cases_on `n:num` >> rw [distmnt2] >>
  Cases_on `n':num` >> rw [distmnt3] >>
  Cases_on `n:num` >> rw [distmnt4] >>
  Cases_on `n':num` >> rw [distmnt5] >>
  Cases_on `n:num` >> rw [distmnt6] >>
  Cases_on `n':num` >> rw [distmnt7] >>
  Cases_on `n:num` >> rw [distmnt8] >>
  Cases_on `n':num` >> rw [distmnt9] >>
  Cases_on `n:num` >> rw [distmnt10] >>
  Cases_on `n':num` >> rw [distmnt11] >>
  Cases_on `n:num` >> rw [distmnt12] >>
  Cases_on `n':num` >> rw [distmnt13] >>
  Cases_on `n:num` >> rw [distmnt14] >>
  Cases_on `n':num` >> rw [distmnt15] >>
  Cases_on `n:num` >> rw [distmnt16] >>
  Cases_on `n':num` >> rw [distmnt17] >>
  Cases_on `n:num` >> rw [distmnt18] >>
  Cases_on `n':num` >> rw [distmnt19] >>
  Cases_on `n:num` >> rw [distmnt20] >>
  Cases_on `n':num` >> rw [distmnt21] >>
  Cases_on `n:num` >> rw [distmnt22] >>
  Cases_on `n':num` >> rw [distmnt23] >>
  simp [distmnt_def, casestmnt_def, execute_def, chooseFunction_def] >>
  simp const_defs
QED
(* END Unique ID section *)

val prop10_tac =
    use_goal (to_quotation o get_if_cond o get_eq_left o get_exists_body o get_concl) Cases_on

Theorem property10:
  ∀context params campaign.
  let
    phase = (get_campaign_phase campaign);
    negotiation = (get_campaign_negotiation campaign);
  in
     ¬(negotiation = WaitingCustomer)∧
     ¬(phase = PhaseAgreement) ⇒
    ∃st.
    changeAgreement_typed context params campaign = None st
Proof
  rw [] >>
  simp [changeAgreement_typed_def, changeAgreement_def] >>
  simp const_defs >>
  ntac 3 (prop10_tac >> simp [])
QED

(*
"После получения сообщения от топливозаправщика (выполнение readyToPerformTask) цена согласована между поставщиком и кастомером."
"gasPrice = None  ⇒   error"
*)
Theorem property11:
∀context params campaign campaign2.
~(approvedPriceExists campaign)
 ⇒
∃s. (readyToPerformTask_typed context params campaign = None s)
Proof
  simp $ readyToPerformTask_typed_def::const_defs
QED

(* при отклонении цены в пользу другого поставщика функции контракта становятся недоступны (при declined); *)
(* Незачем ставить Campaign a b c d phase f, достаточно указать просто campaign.
 * Не надо плодить сущности!
 *)
Theorem PhaseDeclinedAfterdeclinePrice:
  ∀params context a b c d phase f.
    isSenderCustomer context (Campaign a b c d phase f) ∧
    (get_campaign_phase (Campaign a b c d phase f)) = PhaseTasks ∧
    get_agreement_negotiation (get_campaign_agreement (Campaign a b c d phase f)) = NegotiationApproved ∧ (*todo*)
    (¬ NULL (get_campaign_priceChanges (Campaign a b c d phase f))) ∧
    (get_priceChange_negotiation $ HD $ get_campaign_priceChanges (Campaign a b c d phase f)) = WaitingCustomer ⇒
    ∃c1. declinePrice_typed context params (Campaign a b c d phase f) = Some (SCCampaign c1) ∧
         (get_campaign_phase c1) = PhaseDeclined
Proof
    rw [declinePrice_typed_def, get_campaign_phase_def, set_campaign_phase_def]
QED


val paramcases:tactic =
  (Cases_on `params` >> simp const_defs) >>
  (Cases_on `t` >> simp const_defs) >>
  (Cases_on `h` >> simp const_defs) >>
  (Cases_on `p_get_task_index_by_id (get_campaign_tasks campaign) n` >> simp []) >>
  (Cases_on `x` >> simp const_defs)
          
Theorem PhaseDeclinedBlockFunctions13:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 13 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [approveTask_typed_def] >> rw[base_task_fn_def] >> FULL_SIMP_TAC bool_ss [] >>
  Cases_on `params=[]` >> rw const_defs >>
  ntac 2 paramcases
QED
    
Theorem PhaseDeclinedBlockFunctions14:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 14 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [rejectTask_typed_def] >> rw[base_task_fn_def] >> FULL_SIMP_TAC bool_ss [] >>
  Cases_on `params=[]` >> rw const_defs >>
  ntac 2 paramcases
QED

Theorem PhaseDeclinedBlockFunctions15:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 15 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [acceptTask_typed_def] >> FULL_SIMP_TAC bool_ss [] >>
  Cases_on `params=[]` >> rw const_defs >>
  ntac 2 paramcases
QED

Theorem PhaseDeclinedBlockFunctions3:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 3 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [rejectAgreement_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions4:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 4 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [approveAgreement_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions5:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 5 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [changeAgreement_typed_def, changeAgreement_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions8:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 8 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [rejectPrice_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions9:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 9 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [approvePrice_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions10:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 10 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [declinePrice_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions11:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 11 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [createPriceChange_typed_def, createPriceChange_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions17:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 17 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [addTask_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions18:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 18 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [readyToPerformTask_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions19:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 19 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [requestGas_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions20:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 20 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [completePayment_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions21:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 21 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [performTask_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions22:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 22 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [completeTask_typed_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions23:
  ∀params context campaign. get_campaign_phase campaign = PhaseDeclined ⇒ ∃e. execute 23 context params campaign = None e
Proof
  rpt STRIP_TAC >> rw [execute_def, chooseFunction_def] >> rw [confirmTask_typed_def, confirmTask_def] >> simp const_defs
QED

Theorem PhaseDeclinedBlockFunctions:
  ∀f params context campaign. get_campaign_phase campaign = PhaseDeclined ∧
  (MEM f [3;4;5;8;9;10;11;13;14;15;17;18;19;20;21;22;23]) ⇒ ∃e. execute f context params campaign = None e
Proof
  rpt STRIP_TAC >>
  Cases_on `f=3` >> rw [PhaseDeclinedBlockFunctions3] >>
  Cases_on `f=4` >> rw [PhaseDeclinedBlockFunctions4] >>
  Cases_on `f=5` >> rw [PhaseDeclinedBlockFunctions5] >>
  Cases_on `f=8` >> rw [PhaseDeclinedBlockFunctions8] >>
  Cases_on `f=9` >> rw [PhaseDeclinedBlockFunctions9] >>
  Cases_on `f=10` >> rw [PhaseDeclinedBlockFunctions10] >>
  Cases_on `f=11` >> rw [PhaseDeclinedBlockFunctions11] >>
  Cases_on `f=13` >> rw [PhaseDeclinedBlockFunctions13] >>
  Cases_on `f=14` >> rw [PhaseDeclinedBlockFunctions14] >>
  Cases_on `f=15` >> rw [PhaseDeclinedBlockFunctions15] >>
  Cases_on `f=17` >> rw [PhaseDeclinedBlockFunctions17] >>
  Cases_on `f=18` >> rw [PhaseDeclinedBlockFunctions18] >>
  Cases_on `f=19` >> rw [PhaseDeclinedBlockFunctions19] >>
  Cases_on `f=20` >> rw [PhaseDeclinedBlockFunctions20] >>
  Cases_on `f=21` >> rw [PhaseDeclinedBlockFunctions21] >>
  Cases_on `f=22` >> rw [PhaseDeclinedBlockFunctions22] >>
  Cases_on `f=23` >> rw [PhaseDeclinedBlockFunctions23] >>
  FULL_SIMP_TAC (srw_ss()) [MEM]
QED

Definition useCampaign_def:
 useCampaign defa func (scoptc:SCvalue optionErr) =
 case scoptc of
   Some c => func c
 | Ret c _ => func c
 | None _ => defa
End

Definition useCampaignT_def:
 useCampaignT = useCampaign T
End

Inductive isFeasible_def:
 (∀(context:Context) (params:SCvalue list) (campaign:Campaign) (campaign1:Campaign).
   ((constructor context params campaign) = Some (SCCampaign campaign1) ==> isFeasible campaign1)
) ∧
 (∀(context:Context) (params:SCvalue list) (campaign:Campaign) (campaign1:Campaign) (dummy:SCvalue).
   ((constructor context params campaign) = Ret (SCCampaign campaign1) dummy ==> isFeasible campaign1)
) ∧
 (∀(f:num) (context:Context) (params:SCvalue list) (campaign:Campaign) (campaign1:Campaign).
   ((execute f context params campaign) = Some (SCCampaign campaign1) ==> isFeasible campaign1)
) ∧
 (∀(f:num) (context:Context) (params:SCvalue list) (campaign:Campaign) (campaign1:Campaign) (dummy:SCvalue).
   ((execute f context params campaign) = Ret (SCCampaign campaign1) dummy ==> isFeasible campaign1)
)
End

Theorem property_new_l1:
∀(context:Context) (params:SCvalue list) (campaign:Campaign) (campaign':Campaign).
constructor context params campaign = Some (SCCampaign campaign')
⇒
(get_campaign_phase campaign' = PhaseTasks)
⇒
(get_agreement_negotiation (get_campaign_agreement campaign') = NegotiationApproved)
Proof
  rpt gen_tac >>
  simp [constructor_def] >> simp const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_left o get_antecedent o get_concl) Cases_on >> simp []) >>
  simp [constructor_helper_def] >>
  rw [get_campaign_agreement_def, get_agreement_negotiation_def, get_campaign_phase_def] >>
  UNDISCH_ALL >>
  simp []
QED

Theorem property_new_l2:
∀(context:Context) (params:SCvalue list) (campaign:Campaign) (campaign':Campaign) (dummy:SCvalue).
constructor context params campaign = Ret (SCCampaign campaign') dummy
⇒
(get_campaign_phase campaign' = PhaseTasks)
⇒
(get_agreement_negotiation (get_campaign_agreement campaign') = NegotiationApproved)
Proof
  rpt gen_tac >>
  simp [constructor_def] >> simp const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_left o get_antecedent o get_concl) Cases_on >> simp [])
QED

Theorem phaseLemma:
∀(P:bool) (A :Agreement) (l :Task list) (l0 :PriceChange list) (l1 :PaymentOrder list)
(A' :Agreement) (l' :Task list) (N' :Negotiation)
(l0' :PriceChange list) (l1' :PaymentOrder list).
Campaign (A :Agreement) (l :Task list) WaitingSupplier
(l0 :PriceChange list) PhaseAgreement (l1 :PaymentOrder list) with
agreement := A with negotiation := WaitingCustomer =
Campaign (A' :Agreement) (l' :Task list) (N' :Negotiation)
(l0' :PriceChange list) PhaseTasks (l1' :PaymentOrder list)
⇒
P
Proof
  strip_tac >> fs[definition "Campaign_agreement_fupd"]
QED

Theorem property_new_l3:
∀(f:num) (context:Context) (params:SCvalue list) (campaign:Campaign) (campaign':Campaign).
execute f context params campaign = Some (SCCampaign campaign')
⇒
(get_campaign_phase campaign' = PhaseTasks)
⇒
(get_agreement_negotiation (get_campaign_agreement campaign') = NegotiationApproved)
Proof
  rpt gen_tac >>
  (* 0 *) (Cases_on `f:num` >| [ simp [execute_def, chooseFunction_def] >> simp const_defs, all_tac ] ) >>
  (* 1 *) (Cases_on `n:num` >| [ simp [execute_def, chooseFunction_def] >> simp const_defs, all_tac ] ) >>
  (* 2 *) (Cases_on `n':num` >| [
    simp [execute_def, chooseFunction_def, getAgreement_typed_def]>> simp const_defs >>
    ntac 2 (use_goal (to_quotation o get_if_cond o get_eq_left o get_antecedent o get_concl) Cases_on >> simp [])
  , all_tac ] ) >>
  (* 3 *) (Cases_on `n:num` >| [
    simp [execute_def, chooseFunction_def, rejectAgreement_typed_def]>> simp const_defs >>
    ntac 4 (use_goal (to_quotation o get_if_cond o get_eq_left o get_antecedent o get_concl) Cases_on >> simp []) >>
    UNDISCH_ALL >>
    Cases_on `campaign` >>
    Cases_on `campaign'` >>
    simp [get_campaign_phase_def, get_campaign_agreement_def, get_agreement_negotiation_def, set_campaign_agreement_def, set_agreement_negotiation_def, get_campaign_negotiation_def] >>
    rw [] >>
    irule phaseLemma >>
    exists_tac ``(A:Agreement)`` >>
    exists_tac ``(A':Agreement)`` >>
    exists_tac ``(N':Negotiation)`` >>
    exists_tac ``(l:Task list)`` >>
    exists_tac ``(l':Task list)`` >>
    exists_tac ``(l0:PriceChange list)`` >>
    exists_tac ``(l0':PriceChange list)`` >>
    cheat
  ,
    all_tac
  ]) >>
  cheat
QED

Theorem property_new:
∀(context:Context) (params:SCvalue list) (campaign:Campaign) (campaign':Campaign).
isFeasible(campaign)
 ⇒
(get_campaign_phase campaign = PhaseTasks)
 ⇒
(get_agreement_negotiation (get_campaign_agreement campaign) = NegotiationApproved)
Proof
  rpt gen_tac >>
  Induct_on ‘isFeasible(campaign)’ >>
  ntac 4 STRIP_TAC
  >| [
    rw [] >>
    irule property_new_l1 >>
    simp [] >>
    exists_tac ``(campaign:Campaign)`` >>
    exists_tac ``(context:Context)`` >>
    exists_tac ``(params:SCvalue list)`` >>
    simp []
  ,
    rw [] >>
    irule property_new_l2 >>
    simp [] >>
    exists_tac ``(campaign:Campaign)`` >>
    exists_tac ``(context:Context)`` >>
    exists_tac ``(dummy:SCvalue)`` >>
    exists_tac ``(params:SCvalue list)`` >>
    simp []
  ,
    cheat
  ,
    cheat
  ]
QED

(* property12 *)
Theorem property12_lemma:
   (λx. calculateLastPrice x = NONE) campaign  ⇒  ¬approvedPriceExists campaign
Proof
  simp [calculateLastPrice_def, approvedPriceExists_def] >>
  simp [oHD_def] >>
  (Cases_on `
     (dropWhile ((λy. y ≠ NegotiationApproved) ∘ get_priceChange_negotiation)
        (get_campaign_priceChanges campaign))` >> rw []  ) >>
  UNDISCH_TAC ``dropWhile
          ((λy. y ≠ NegotiationApproved) ∘ get_priceChange_negotiation)
          (get_campaign_priceChanges campaign) = []``  >>
  rw [dropWhile_eq_nil] >>
  irule listTheory.MONO_EVERY >>
  exists_tac ``((λy. y ≠ NegotiationApproved) ∘ get_priceChange_negotiation)`` >>
  rw []
QED

(*
g ‘
 ∀ params context campaign.
 ($= NONE o calculateLastPrice) campaign ⇒ readyToPerformTask context params campaign = BAD_ERR’;

g ‘ ∀ campaign.
   ($= NONE o calculateLastPrice) campaign  ⇒  ¬approvedPriceExists campaign’;
*)

Theorem readyToPerformTask1:
   ∀ params context campaign.
  ¬approvedPriceExists campaign ⇒
   ∃msg. readyToPerformTask_typed context params campaign = None msg
Proof
  simp [readyToPerformTask_typed_def] >> simp const_defs
QED

Theorem readyToPerformTask_thm:
 ∀x y task params context campaign.
  params = [SCInt x] ∧
  get_campaign_phase campaign = PhaseTasks ∧
  get_agreement_negotiation (get_campaign_agreement campaign) = NegotiationApproved ∧ (*todo*)
  approvedPriceExists campaign ∧ (*added*)
  get_task_negotiation task = NegotiationApproved ∧ (*added*)
  p_get_campaign_task_by_task_id campaign x = SOME task ∧
  ¬approvedPriceExists campaign ⇒
  ∃msg. readyToPerformTask_typed context params campaign = None msg
Proof
  simp [readyToPerformTask_typed_def] >> simp const_defs >> rw []
QED

(* (prove later)
Theorem todo:
 ∀ campaign.
   ($= NONE o calculateLastPrice) campaign  ⇒  ¬approvedPriceExists campaign
Proof
 gen_tac >>
 simp [approvedPriceExists_def] >>
 simp [calculateLastPrice_def] >>
 irule SPECL imptrans >>
 cheat
QED
*)

Theorem property_uniqueTaskID_constructor:
∀customer_id customer_name supplier_id supplier_name agreement_details bank_addr.
atid $ constructor_helper customer_id customer_name supplier_id supplier_name agreement_details bank_addr
Proof
  rpt gen_tac >>
  simp [constructor_helper_def] >> simp const_defs >>
  simp [atid_def] >>
  simp [get_campaign_tasks_def]
QED

Theorem isFesibleSimpleInductivePrinciple:
∀(isFeasible':Campaign -> bool).
(∀(context:Context) params campaign:Campaign campaign1:Campaign.
 constructor context params campaign =
 Some (SCCampaign campaign1) ⇒
 isFeasible' campaign1) ∧
(∀(context:Context) params campaign:Campaign campaign1:Campaign dummy.
 constructor context params campaign =
 Ret (SCCampaign campaign1) dummy ⇒
 isFeasible' campaign1) ∧
(∀f (context:Context) params campaign:Campaign campaign1:Campaign.
 execute f context params campaign = Some (SCCampaign campaign1) ⇒
 isFeasible' campaign1) ∧
(∀f (context:Context) params campaign:Campaign campaign1:Campaign dummy.
 execute f context params campaign =
 Ret (SCCampaign campaign1) dummy ⇒
 isFeasible' campaign1) ⇒
∀a0. isFeasible a0 ⇒ isFeasible' a0
Proof
  ASSUME_TAC isFeasible_def_ind >>
  EXACT_TAC
QED

Theorem isFesibleInductivePrinciple:
∀(isFeasible':Campaign -> bool).
 (∀(context:Context) params campaign:Campaign campaign1:Campaign.
  constructor context params campaign = Some (SCCampaign campaign1)
  ⇒ isFeasible' campaign1) ∧
 (∀(context:Context) params campaign:Campaign campaign1:Campaign dummy.
  constructor context params campaign = Ret (SCCampaign campaign1) dummy
  ⇒ isFeasible' campaign1) ∧
 (∀f (context:Context) params campaign:Campaign campaign1:Campaign.
  execute f context params campaign = Some (SCCampaign campaign1)
  ⇒ isFeasible campaign (*sic!*)
  ⇒ isFeasible' campaign1) ∧
 (∀f (context:Context) params campaign:Campaign campaign1:Campaign dummy.
  execute f context params campaign = Ret (SCCampaign campaign1) dummy
  ⇒ isFeasible campaign (*sic!*)
  ⇒ isFeasible' campaign1)
 ⇒
  ∀a0. isFeasible a0 ⇒ isFeasible' a0
Proof
  gen_tac >>
  rw [] >>
  (* then use this term:
  (SPEC ``λcampaign.(isFeasible campaign ==> isFeasible' (campaign:Campaign))`` isFeasible_def_ind)
  for Modus Ponens.
  *)
  cheat
QED

Theorem property_uniqueTaskID:
∀(campaign:Campaign).
isFeasible(campaign)
 ⇒
atid campaign
Proof
(* the following is insufficient:
  (Induct_on `isFeasible` >> simp []) >>
, so we use the other inductive principle.
*)
rpt gen_tac >>
rw [] >>
irule isFesibleInductivePrinciple >>
simp [] >>
(**)
(ntac 4 STRIP_TAC >> rpt gen_tac)
>| [
  simp [constructor_def] >> simp const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_left o get_antecedent o get_concl) Cases_on >> simp []) >>
  rw [] >>
  irule property_uniqueTaskID_constructor
,
  simp [constructor_def] >> simp const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_left o get_antecedent o get_concl) Cases_on >> simp []) >>
  rw [] >>
  irule property_uniqueTaskID_constructor
,
  let
    val eqviva = SPECL [``(f:num)``] distmnt_def;
    val q = SPECL [``(context:Context)``,``(params:SCvalue list)``,``(campaign0:Campaign)``];
  in
    simp []
  end >>
  (*IMP
  distmnt_def
  casestmnt_def >>*)
  cheat
,
  cheat
]
QED
(* property 4 *)
(*
    TaskStatus = TaskNotAccepted | TaskAccepted | TaskReadyToPerform | GasRequested | Performing | Confirmed | TaskCompleted ;
*)
(* readyToPerformTask_def *)

Theorem property4_readyToPerform:
∀(context:Context) (params:SCvalue list) (campaign0 campaign1:Campaign) (task0 task1:Task) (taskId:num).
Some (SCCampaign campaign1) = readyToPerformTask_typed (context) ((SCInt taskId)::params) campaign0
⇒
SOME task0 = p_get_campaign_task_by_task_id campaign0 taskId
⇒
SOME task1 = p_get_campaign_task_by_task_id campaign1 taskId
⇒
get_task_taskStatus task1 = TaskReadyToPerform
⇒
get_task_taskStatus task0 = TaskAccepted
Proof
  rpt gen_tac >>
  simp [readyToPerformTask_typed_def] >> simp const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  simp [scToInt_def] >>
  (use_goal (to_quotation o get_case_arg o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  (use_goal (to_quotation o get_if_cond o get_eq_right o get_antecedent o get_concl) Cases_on >> simp [])
QED

Theorem property4_new_readyToPerform:
∀(context:Context) (params:SCvalue list) (campaign0 campaign1:Campaign) (task0 task1:Task) (taskId:num).
(new_readyToPerformTask_typed ((SCInt taskId)::params)) = (return (SCCampaign campaign1))
⇒
SOME task0 = p_get_campaign_task_by_task_id campaign0 taskId
⇒
SOME task1 = p_get_campaign_task_by_task_id campaign1 taskId
⇒
get_task_taskStatus task1 = TaskReadyToPerform
⇒
get_task_taskStatus task0 = TaskAccepted
Proof
  rpt gen_tac >>
  simp [new_readyToPerformTask_typed_def] >>
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  disch_then (qspec_then `w` mp_tac) >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(num, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(Task, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp [])
QED

(* depends on proper work of p_get_campaign_task_by_task_id *)
Theorem property4_readyToPerform':
∀(context:Context) (params:SCvalue list) (campaign0 campaign1:Campaign) (task0 task1:Task) (taskId:num).
Some (SCCampaign campaign1) = readyToPerformTask_typed context params campaign0
⇒
taskId = scToInt (HD params)
⇒
SOME task0 = p_get_campaign_task_by_task_id campaign0 taskId
⇒
SOME task1 = p_get_campaign_task_by_task_id campaign1 taskId
⇒
get_task_taskStatus task1 = TaskReadyToPerform
⇒
get_task_taskStatus task0 = TaskAccepted
Proof
  rpt gen_tac >>
  simp [readyToPerformTask_typed_def] >> simp const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  (use_goal (to_quotation o get_case_arg o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  (use_goal (to_quotation o get_if_cond o get_eq_right o get_antecedent o get_concl) Cases_on >> simp [])
QED

(* work in progress here:
fun do_helper (t:term) = mk_comb (t, ``(s:State)``);

Theorem property4_new_requestGas:
∀(context:Context) (params:SCvalue list) (campaign0 campaign1:Campaign) (task0 task1:Task) (taskId:num).
(new_requestGas_typed params) = (return (SCCampaign campaign1))
⇒
taskId = scToInt (HD params)
⇒
SOME task0 = p_get_campaign_task_by_task_id campaign0 taskId
⇒
SOME task1 = p_get_campaign_task_by_task_id campaign1 taskId
⇒
get_task_taskStatus task1 = GasRequested
⇒
(get_task_taskStatus task0 = TaskReadyToPerform \/ get_task_taskStatus task0 = GasRequested)
Proof
  rpt gen_tac >>
  simp [new_requestGas_typed_def] >>


  simp [boolTheory.FUN_EQ_THM] >>
  disch_then (qspec_then `w` mp_tac) >>
  simp [get_state_def] >>
  simp [Once ml_monadBaseTheory.st_ex_bind_def] >>
  simp [Once ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp []) >>

  (use_goal (print_term o do_helper o term_by_num [2] o get_eq_left o get_antecedent o get_concl) dummy_tac) >>

  (Cases_on `((λ(s :State). ((Success s :(State, state_exn) exc),s)) s)` >> simp []) >>
simp [] >>
fs []
  (use_goal (to_quotation o do_helper o term_by_num [2] o get_eq_left o get_antecedent o get_concl) Cases_on) >>

UNDISCH_ALL >>
simp [] >>

  (Cases_on `(q :(State, state_exn) exc)` >| [UNDISCH_FIRST >> simp [] >> DISCH_TAC, UNDISCH_ALL >> simp []]) >>
cheat
disch_then ((fn x => simp []) o mp_tac)
UNDISCH_ALL >> simp []

  simp [Once ml_monadBaseTheory.st_ex_bind_def] >>

  simp [ml_monadBaseTheory.st_ex_bind_def] >>

  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>

  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(num, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(Task, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp [])
QED
*)

Theorem property4_requestGas:
∀(context:Context) (params:SCvalue list) (campaign0 campaign1:Campaign) (task0 task1:Task) (taskId:num).
Some (SCCampaign campaign1) = requestGas_typed context params campaign0
⇒
taskId = scToInt (HD params)
⇒
SOME task0 = p_get_campaign_task_by_task_id campaign0 taskId
⇒
SOME task1 = p_get_campaign_task_by_task_id campaign1 taskId
⇒
get_task_taskStatus task1 = GasRequested
⇒
(get_task_taskStatus task0 = TaskReadyToPerform \/ get_task_taskStatus task0 = GasRequested)
Proof
  rpt gen_tac >>
  simp [requestGas_typed_def] >> simp const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  (use_goal (to_quotation o get_case_arg o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  (use_goal (to_quotation o get_case_arg o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  (use_goal (to_quotation o get_case_arg o get_eq_right o get_antecedent o get_concl) Cases_on >> simp [])
QED

Theorem property4_new_performTask:
∀(context:Context) (params:SCvalue list) (campaign0 campaign1:Campaign) (task0 task1:Task) (taskId:num).
(new_performTask_typed params) = (return (SCCampaign campaign1))
⇒
taskId = scToInt (HD params)
⇒
SOME task0 = p_get_campaign_task_by_task_id campaign0 taskId
⇒
SOME task1 = p_get_campaign_task_by_task_id campaign1 taskId
⇒
get_task_taskStatus task1 = Performing
⇒
(get_task_taskStatus task0 = GasRequested)
Proof
  rpt gen_tac >>
  simp [new_performTask_typed_def] >>
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  disch_then (qspec_then `w` mp_tac) >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(num, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(Task, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp [])
QED

Theorem property4_performTask:
∀(context:Context) (params:SCvalue list) (campaign0 campaign1:Campaign) (task0 task1:Task) (taskId:num).
Some (SCCampaign campaign1) = performTask_typed context params campaign0
⇒
taskId = scToInt (HD params)
⇒
SOME task0 = p_get_campaign_task_by_task_id campaign0 taskId
⇒
SOME task1 = p_get_campaign_task_by_task_id campaign1 taskId
⇒
get_task_taskStatus task1 = Performing
⇒
(get_task_taskStatus task0 = GasRequested)
Proof
(*get_task_taskStatus task0 = TaskReadyToPerform \/ *)
  rpt gen_tac >>
  simp [performTask_typed_def] >> simp const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  (use_goal (to_quotation o get_case_arg o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  (use_goal (to_quotation o get_if_cond o get_eq_right o get_antecedent o get_concl) Cases_on >> simp [])
QED

Theorem property4_new_confirmTask:
∀(context:Context) (params:SCvalue list) (campaign0 campaign1:Campaign) (task0 task1:Task) (taskId:num).
(new_confirmTask_typed params) = (return (SCCampaign campaign1))
⇒
taskId = scToInt (HD params)
⇒
SOME task0 = p_get_campaign_task_by_task_id campaign0 taskId
⇒
SOME task1 = p_get_campaign_task_by_task_id campaign1 taskId
⇒
(get_task_taskStatus task1 = Confirmed \/ get_task_taskStatus task1 = TaskCompleted)
⇒
(get_task_taskStatus task0 = Performing)
Proof
  rpt gen_tac >>
  simp [new_confirmTask_typed_def] >>
  (* (use_goal (print_term o term_by_num [3] o get_eq_left o get_antecedent o get_concl) dummy_tac) >> *)
  simp [ml_monadBaseTheory.st_ex_bind_def] >>
  simp [ml_monadBaseTheory.st_ex_return_def] >>
  simp [boolTheory.FUN_EQ_THM] >>
  simp [get_state_def] >>
  disch_then (qspec_then `w` mp_tac) >>
  simp [ml_monadBaseTheory.st_ex_ignore_bind_def] >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(unit, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (* "use_goal ..." does the same as "Cases_on `scMToInt (HD (params :SCvalue list)) (r :State)` >>" *)
  (Cases_on `(q :(num, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(num, state_exn) exc)` >> simp []) >>
  (use_goal (to_quotation o get_case_arg  o get_eq_left o get_antecedent o get_concl) Cases_on) >>
  (Cases_on `(q :(SCvalue, state_exn) exc)` >> simp [])
QED

Theorem property4_confirmTask:
∀(context:Context) (params:SCvalue list) (campaign0 campaign1:Campaign) (task0 task1:Task) (taskId:num).
Some (SCCampaign campaign1) = confirmTask_typed context params campaign0
⇒
taskId = scToInt (HD params)
⇒
SOME task0 = p_get_campaign_task_by_task_id campaign0 taskId
⇒
SOME task1 = p_get_campaign_task_by_task_id campaign1 taskId
⇒
(get_task_taskStatus task1 = Confirmed \/ get_task_taskStatus task1 = TaskCompleted)
⇒
(get_task_taskStatus task0 = Performing)
Proof
(*get_task_taskStatus task0 = TaskReadyToPerform \/ *)
  rpt gen_tac >>
  simp $ confirmTask_typed_def :: const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  simp $ confirmTask_def :: const_defs >>
  (use_goal (to_quotation o get_if_cond o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  (use_goal (to_quotation o get_case_arg o get_eq_right o get_antecedent o get_concl) Cases_on >> simp []) >>
  rw []
QED


(* NEX PART *)
Theorem approveTaskNEX:
  ∀x params context campaign. params = [SCInt x] ∧
  (p_get_task_index_by_id (get_campaign_tasks campaign) x) = NONE ⇒ approveTask_typed context params campaign = NEX_Task
Proof
  rpt STRIP_TAC >> rw [approveTask_typed_def] >> simp const_defs >> ASM_REWRITE_TAC [base_task_fn_def] >> rw const_defs
QED

Theorem rejectTaskNEX:
  ∀x params context campaign. params = [SCInt x] ∧
  (p_get_task_index_by_id (get_campaign_tasks campaign) x) = NONE ⇒ rejectTask_typed context params campaign = NEX_Task
Proof
  rpt STRIP_TAC >> rw [rejectTask_typed_def] >> simp const_defs >> ASM_REWRITE_TAC [base_task_fn_def] >> rw const_defs
QED

Theorem acceptTaskNEX:
  ∀x params context campaign. params = [SCInt x] ∧
  (p_get_task_index_by_id (get_campaign_tasks campaign) x) = NONE ⇒ acceptTask_typed context params campaign = NEX_Task
Proof
  rpt STRIP_TAC >> ASM_REWRITE_TAC [acceptTask_typed_def] >> rw const_defs
QED

Theorem readyToPerformTaskNEX:
  ∀x params context campaign. params = [SCInt x] ∧
  p_get_campaign_task_by_task_id campaign x = NONE ∧
  get_campaign_phase campaign = PhaseTasks ∧
  get_agreement_negotiation (get_campaign_agreement campaign) = NegotiationApproved ∧ (*todo*)
  approvedPriceExists campaign ⇒ readyToPerformTask_typed context params campaign = NEX_Task
Proof
  rpt STRIP_TAC >>
  ASM_REWRITE_TAC [readyToPerformTask_typed_def] >> rw [scToInt_def] >> rw const_defs >>
  FULL_SIMP_TAC std_ss [checkTypes_def, MAP, typeOf_def]
QED

Theorem performTaskNEX:
  ∀x params context campaign. params = [SCInt x] ∧
  p_get_campaign_task_by_task_id campaign x = NONE ∧
  get_campaign_phase campaign = PhaseTasks ∧
  get_agreement_negotiation (get_campaign_agreement campaign) = NegotiationApproved ∧ (*todo*)
  approvedPriceExists campaign ⇒ performTask_typed context params campaign = NEX_Task
Proof
  rpt STRIP_TAC >>
  ASM_REWRITE_TAC [performTask_typed_def] >> rw [scToInt_def] >> rw const_defs >>
  FULL_SIMP_TAC std_ss [checkTypes_def, MAP, typeOf_def]
QED

Theorem requestGasNEX:
  ∀x y params context campaign. params = [SCInt x; SCInt y] ∧
  p_get_campaign_task_by_task_id campaign x = NONE ∧
  get_campaign_phase campaign = PhaseTasks ⇒ requestGas_typed context params campaign = NEX_Task
Proof
  rpt STRIP_TAC >>
  ASM_REWRITE_TAC [requestGas_typed_def] >> rw [scToInt_def] >> rw const_defs >>
  FULL_SIMP_TAC std_ss [checkTypes_def, MAP, typeOf_def]
QED

Theorem taskCompletedNEX:
  ∀x y params context campaign. params = [SCInt x; SCInt y] ∧
  p_get_campaign_task_by_task_id campaign x = NONE ∧
  get_campaign_phase campaign = PhaseTasks ∧
  get_agreement_negotiation (get_campaign_agreement campaign) = NegotiationApproved ∧ (*todo*)
  approvedPriceExists campaign ⇒ completeTask_typed context params campaign = NEX_Task
Proof
  rpt STRIP_TAC >>
  ASM_REWRITE_TAC [completeTask_typed_def] >> rw [scToInt_def] >> rw const_defs >>
  FULL_SIMP_TAC std_ss [checkTypes_def, MAP, typeOf_def]
QED

Theorem confirmTaskNEX:
  ∀x y params context campaign. params = [SCInt x; SCInt y] ∧
  p_get_campaign_task_by_task_id campaign x = NONE ∧
  get_agreement_negotiation (get_campaign_agreement campaign) = NegotiationApproved ∧ (*todo*)
  approvedPriceExists campaign ∧ (*added*)
  get_campaign_phase campaign = PhaseTasks ⇒ confirmTask_typed context params campaign = NEX_Task
Proof
  rpt STRIP_TAC >>
  ASM_REWRITE_TAC [confirmTask_typed_def, confirmTask_def] >> rw [scToInt_def] >> rw const_defs >>
  FULL_SIMP_TAC std_ss [checkTypes_def, MAP, typeOf_def]
QED

Theorem noConfirmWithoutGas:
  ∀x y task params context campaign. params = [SCInt x; SCInt y] ∧
  get_campaign_phase campaign = PhaseTasks ∧
  get_agreement_negotiation (get_campaign_agreement campaign) = NegotiationApproved ∧ (*todo*)
  approvedPriceExists campaign ∧ (*added*)
  get_task_negotiation task = NegotiationApproved ∧ (*added*)
  p_get_campaign_task_by_task_id campaign x = SOME task ∧
  get_task_taskStatus task ≠ Performing ∧
  isSenderCaptain context task ⇒ confirmTask_typed context params campaign = NO_GAS_REQUESTS
Proof
  rpt STRIP_TAC >> ASM_REWRITE_TAC [confirmTask_typed_def, confirmTask_def] >> rw [scToInt_def] >> rw [] >>
  FULL_SIMP_TAC std_ss [isSenderCaptain_def, checkTypes_def, MAP, typeOf_def]
QED

Theorem noConfirmOutPhaseTasks:
  ∀x y task params context campaign. params = [SCInt x; SCInt y] ∧
  get_campaign_phase campaign ≠ PhaseTasks ⇒
    confirmTask_typed context params campaign = NOT_ALLOWED_action
Proof
  rw [confirmTask_typed_def, confirmTask_def, checkTypes_def, typeOf_def]
QED

Theorem noConfirmWithoutCap:
  ∀x y task params context campaign. params = [SCInt x; SCInt y] ∧
  get_campaign_phase campaign = PhaseTasks ∧
  get_agreement_negotiation (get_campaign_agreement campaign) = NegotiationApproved ∧ (*todo*)
  approvedPriceExists campaign ∧ (*added*)
  get_task_negotiation task = NegotiationApproved ∧ (*added*)
  p_get_campaign_task_by_task_id campaign x = SOME task ∧
  ¬isSenderCaptain context task ⇒ confirmTask_typed context params campaign = ONLY_Captain
Proof
  rpt STRIP_TAC >> ASM_REWRITE_TAC [confirmTask_typed_def, confirmTask_def] >> rw [scToInt_def] >> rw [] >>
  FULL_SIMP_TAC std_ss [isSenderCaptain_def, checkTypes_def, MAP, typeOf_def] >>
  FULL_SIMP_TAC std_ss [isSenderCaptain_def, checkTypes_def, MAP, typeOf_def] >>
  FULL_SIMP_TAC std_ss [isSenderCaptain_def, checkTypes_def, MAP, typeOf_def] >>
  FULL_SIMP_TAC std_ss [isSenderCaptain_def, checkTypes_def, MAP, typeOf_def] >>
  FULL_SIMP_TAC std_ss [isSenderCaptain_def, checkTypes_def, MAP, typeOf_def]
QED

(*GOALTHMS ---------------------------------------------------------------------- *)

val r = translate ml_monadBaseTheory.st_ex_return_def;
val r = translate get_state_def;
(* st_ex_monad_bind_def == ml_monadBaseTheory.st_ex_bind_def *)
val r = translate ml_monadBaseTheory.st_ex_bind_def;
val r = translate get_context_msgSender_def;
val r = translate get_campaign_agreement_def;
val r = translate get_agreement_customer_def;
val r = translate get_agreement_supplier_def;
val r = translate get_person_id_def;

val r = translate ml_monadBaseTheory.st_ex_ignore_bind_def;
val r = translate my_raise_Fail_def;
val r = translate assert_def;

(*val r = translate SONLY_CUST_OR_SUPPL_ALLOWED_VIEW_AGREEMENT_def; *)
val w = map translate sconst_defs

val r = translate ml_monadBaseTheory.st_ex_return_def;

val r = translate my_raise_Fail_def;
val r = translate assert_def;

val r = translate new_getAgreement_typed_def;
(* val r = translate get_state_def;
don't need to uncomment this since it's already done in the
previous line, so "get_state_1_v" will be unnecessary created *)

val _ = export_theory();
