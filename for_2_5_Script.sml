local
  val wrds = ["agreement", "tasks", "negotiation",
    "priceChanges", "phase", "paymentOrders"];
  fun apl L =
    let val un = curry op^;
    in map (definition o
            un (L ^ "et_campaign_") o
            C un "_def")
    end;
in
  val campaign_setters = apl "s" wrds;
  val campaign_getters = apl "g" wrds;
end;
val execute_funcs = [
    ``getAgreement``, ``rejectAgreement``,
    ``approveAgreement``, ``changeAgreement``,
    ``getPriceChangeWithNumber``, ``getPriceChangesLength``,
    ``rejectPrice``, ``approvePrice``,
    ``declinePrice``, ``createPriceChange``,
    ``getTask``, ``approveTask``,
    ``rejectTask``, ``acceptTask``,
    ``addTask``,
    ``readyToPerformTask``, ``requestGas``,
    ``paymentCompleted``, ``performTask``,
    ``taskCompleted``, ``confirmTask``];

signature PROJECT_TOOLS =
sig
  val take_case_from_term : term -> term option
  val take_case_from_goal : goal -> term option
  val CASES_ULTIMATUM : tactic
  val ASM_CASES_ULTIMATUM : int -> tactic
  val FULL_CASES_ULTIMATUM : tactic 
  val RCases_on : term quotation -> tactic
  val rCases_on : term quotation list -> tactic
  val FCases_on : term quotation -> tactic
  val fCases_on : term quotation list -> tactic
  val for_Cases_on : (term quotation -> term quotation) -> term quotation -> int -> tactic
  val CASES_magic : tactic -> tactic
end;

structure ProjectTools : PROJECT_TOOLS =
struct
  fun take_case_from_term (x:term):term option =
    if is_var x orelse is_const x then
      NONE
    else if is_abs x then
      take_case_from_term $ snd $ dest_abs x
    else
      let val (a, b) = dest_comb x
      in
        if is_const a andalso
           String.isSuffix "_CASE" $ fst $ dest_const a then
          SOME b
        else
          let val res:term option = take_case_from_term a
          in
            if isSome res then
              res
            else
              take_case_from_term b
          end
      end;
  
  fun take_case_from_goal (x:goal):term option =
    let
      val L = snd x :: fst x;
      fun traverse [] = NONE
        | traverse (h::t) =
          let val res = take_case_from_term h
          in if isSome res then
               res
             else
               traverse t
          end
    in
      traverse L
    end;

  fun cases (SOME (term:term)) _ =
        Cases_on $ single $ ANTIQUOTE term
    | cases NONE name = raise (mk_HOL_ERR
        "ProjectTools" name "No cases found");

  fun CASES_ULTIMATUM (x:goal):goal list * validation =
    let val termop = take_case_from_term $ snd x
    in cases termop "CASES_ULTIMATUM" x
    end;
  fun ASM_CASES_ULTIMATUM (i:int) (x:goal):goal list * validation =
    let val termop = take_case_from_term $ el i $ fst x
    in cases termop "ASM_CASES_ULTIMATUM" x
    end;
  fun FULL_CASES_ULTIMATUM x =
    let val termop = take_case_from_goal x
    in cases termop "FULL_CASES_ULTIMATUM" x
    end;

  (* "Подчищающие" за собой Cases_on *)
  fun RCases_on (var:term quotation) :tactic =
      Cases_on var >> rw[];
  val rCases_on = EVERY o map RCases_on;
  fun FCases_on (var:term quotation) :tactic =
      Cases_on var >> fs[];
  val fCases_on = EVERY o map FCases_on;

  (* переделывает вложенные case-ы в i+1 цель
     nxt -- функция, показывающая, по какому значению раскладывать в следующий раз
     Для execute это: `f`->`n`->`n'`->`n`->`n'`...
  *)
  fun for_Cases_on nxt f i =
      if i <= 0 then all_tac
      else Cases_on f THEN_LT
          LASTGOAL $ for_Cases_on nxt (nxt f) (i - 1);

  fun CASES_magic tc =
    tc >> rpt (FULL_CASES_ULTIMATUM >> tc)
end;

(*THMS*)

Theorem IF_EQUALS_optionErr_1:
    ((if P then Ret a b else None c) = Ret a' b' ⇔ P ∧ a = a' ∧ b = b') ∧
    ((if P then None c else Ret a b) = Ret a' b' ⇔ ¬P ∧ a = a' ∧ b = b') ∧
    ((if P then Ret a b else None c) = Some v ⇔ F) ∧
    ((if P then None c else Ret a b) = Some v ⇔ F)
Proof
    rw[]
QED

Theorem IF_EQUALS_optionErr_2:
    ((if P then Some a else None b) = Some a' ⇔ P ∧ a = a') ∧
    ((if P then None b else Some a) = Some a' ⇔ ¬P ∧ a = a') ∧
    ((if P then Some a else None b) = Ret m n ⇔ F) ∧
    ((if P then None b else Some a) = Ret m n ⇔ F)
Proof
    rw[]
QED

Theorem IF_EQUALS_optionErr_3:
    ((if P then A else None b) = Some a ⇔ P ∧ Some a = A) ∧
    ((if P then None b else A) = Some a ⇔ ¬P ∧ Some a = A) ∧
    ((if P then A else None b) = Ret n m ⇔ P ∧ Ret n m = A) ∧
    ((if P then None b else A) = Ret n m ⇔ ¬P ∧ Ret n m = A)
Proof
    rw[EQ_SYM_EQ]
QED

Theorem IF_EQUALS:
    (if P then A else B) = C ⇔ (P ∧ A = C) ∨ (¬P ∧ B = C)
Proof
    rw[]
QED

Theorem approvedPriceExists_equivalence:
    calculateLastPrice campaign = SOME x' ⇒
    approvedPriceExists campaign
Proof
  rw[calculateLastPrice_def,
     approvedPriceExists_def,
     oHD_def] >>
  ProjectTools.FULL_CASES_ULTIMATUM >>
  fs[] >>
  CCONTR_TAC >>
  `dropWhile ($¬ ∘ $= NegotiationApproved ∘ get_priceChange_negotiation)
    (get_campaign_priceChanges campaign) = []`
      by fs[dropWhile_eq_nil] >>
  `($¬ o $= NegotiationApproved) = (λy. y ≠ NegotiationApproved)`
      by (rw[FUN_EQ_THM]) >>
  fs[] >>
  FULL_SIMP_TAC simpLib.empty_ss [o_ASSOC] >>
  fs[]
QED

(*SOME DEFS*)

fun nxt (x: term quotation): term quotation =
    if Parse.term_to_string (Term x) = "n"
    then `n'`
    else `n`;

val magic_Cases_on =
  let
    val fsif = fs[IF_EQUALS_optionErr_3]
  in
    foldr (fn (x, y) => (fsif >> Cases_on x) >> y) fsif
  end;

(* Делает список [x,...,x] длины i *)
fun replicate i x =
    let
        fun rep i = if i <= 0
                    then []
                    else x :: rep (i - 1)
    in
        rep i
    end

local
open ProjectTools;

fun assum_form (f:term) = ``
    (^f co p ca = Ret (SCCampaign ca') b) ∨
    (^f co p ca = Ret c (SCCampaign ca')) ∨
    (^f co p ca = Some (SCCampaign ca'))
    ``

Theorem getTask_saves_campaign:
    ^(assum_form ``getTask``) ⇒
    ca' = ca
Proof
    rw (getTask_def::const_defs) >> (
    fCases_on [`p`, `t`, `h`,
        `p_get_task_index_by_id (get_campaign_tasks ca) n`,
        `x`] >>
    fs[IF_EQUALS_optionErr_1])
QED

Theorem getAgreement_saves_campaign:
    ^(assum_form ``getAgreement``) ⇒
    ca' = ca
Proof
    rw[getAgreement_def]
QED

Theorem getPriceChangeWithNumber_saves_campaign:
    ^(assum_form ``getPriceChangeWithNumber``) ⇒
    ca' = ca
Proof
    rw[getPriceChangeWithNumber_def]
QED

Theorem getPriceChangesLength_saves_campaign:
    ^(assum_form ``getPriceChangesLength``) ⇒
    ca' = ca
Proof
    rw[getPriceChangesLength_def]
QED

Theorem rejectAgreement_saves_tasks:
    ^(assum_form ``rejectAgreement``) ⇒
    get_campaign_tasks ca = get_campaign_tasks ca'
Proof
    rw[rejectAgreement_def, get_campaign_tasks_def, set_campaign_agreement_def] >>
    rw[]
QED

(* Формулировка теоремы о том,
   что данная функция x сохраняет список заданий *)
fun save_tsks x = ``^(assum_form x) ⇒
    get_campaign_tasks ca = get_campaign_tasks ca'``

(* Доказательство: обычное переписывание на основе определений *)
val p_s_t =
  rw (map (definition o C (curry op^) "_def" o Parse.term_to_string) execute_funcs @ campaign_getters @ campaign_setters) >>
  rw[];

(* Сама теорема (функция может вызывать исключение) *)
fun x_s_t x = prove(save_tsks x, p_s_t);

val tacs' = map (fn x =>
        `get_campaign_tasks campaign =
        get_campaign_tasks campaign'` by
    metis_tac[x_s_t x] >>
    fs[] handle _ => all_tac)
        (List.take (execute_funcs, 16) @ List.drop (execute_funcs, 15));
val tacs = foldr (fn(x,xs) => x::x::x::xs) [] tacs';


Theorem approveAgreement_saves_tasks:
    ^(assum_form ``approveAgreement``) ⇒
    get_campaign_tasks ca = get_campaign_tasks ca'
Proof
    rw[approveAgreement_def, get_campaign_tasks_def, set_campaign_agreement_def] >>
    rw[]
QED

val LENGTH_FILTER =
    lookup "LENGTH_FILTER_LEQ" $ thms "rich_list";
val FSTSIDE_TAC =
  `LENGTH campaign'.tasks = SUC $ LENGTH campaign.tasks` by metis_tac[LENGTH];

fun thrm (f:term) = Term `
    ∀ context params v campaign campaign' newtask.
        let tasks = get_campaign_tasks campaign
        and priceChanges = get_campaign_priceChanges campaign
        and tasks' = get_campaign_tasks campaign'
        in
            ((^f context params campaign =
            Some (SCCampaign campaign')) ∨
            (^f context params campaign =
            Ret (SCCampaign campaign') v ) ∨
            (^f context params campaign =
            Ret v (SCCampaign campaign'))) ⇒

            (tasks' = newtask::tasks) ⇒
            EXISTS ($= NegotiationApproved o get_priceChange_negotiation) priceChanges
`
fun THRM (f:term) = Term `
    ∀ context params v campaign campaign'.
        let tasks = get_campaign_tasks campaign
        and priceChanges = get_campaign_priceChanges campaign
        and tasks' = get_campaign_tasks campaign'
        in
            ((^f context params campaign =
            Some (SCCampaign campaign')) ∨
            (^f context params campaign =
            Ret (SCCampaign campaign') v ) ∨
            (^f context params campaign =
            Ret v (SCCampaign campaign'))) ⇒

            (f ≠ 17 ⇒ LENGTH tasks' ≤ LENGTH tasks) ∧
            (f = 17 ⇒ LENGTH tasks' = LENGTH tasks + 1 ∧
            EXISTS ($= NegotiationApproved o get_priceChange_negotiation) priceChanges)
`
fun prf t =
    rw[] >|
    replicate 3 $
        `campaign = campaign'` by metis_tac[t] >> fs[]

fun apr_rej_acc (x:term) (y:term) =
  fs ([approveTask_def, rejectTask_def, acceptTask_def, base_task_fn_def] @ const_defs) >>
  CASES_magic (fs[]) >>
  fs[IF_EQUALS_optionErr_3] >>
  FCases_on `get_campaign_phase campaign` >>
  TRY (FCases_on `get_task_negotiation r`) >>
  fs[p_approve_task_by_rez_indx_def,
     p_reject_task_by_rez_indx_def,
     p_accept_task_by_rez_indx_def,
     p_base_task_replacing_fn_def,
     get_campaign_tasks_def,
     set_campaign_tasks_def, set_task_negotiation_def] >>
  fs[IF_EQUALS_optionErr_3] >>
  `campaign'.tasks = (campaign with tasks := LUPDATE (^x r ^y) q campaign.tasks).tasks` by metis_tac[] >>
  fs[prove(``a = b ⇒ a.tasks = b.tasks``, metis_tac[])] >>
  `LENGTH $ LUPDATE (^x r ^y) q campaign.tasks = LENGTH campaign.tasks` by metis_tac[LENGTH_LUPDATE] >>
  FULL_SIMP_TAC (simpLib.mk_simpset []) [get_campaign_tasks_def] >>
  `LENGTH $ LUPDATE (^x r ^y) q campaign.tasks = SUC $ LENGTH campaign.tasks` by metis_tac[LENGTH] >>
  fs[];

fun magic_fs_tac x = fs [x] >>
  CASES_magic (fs[IF_EQUALS_optionErr_3]) >>
  fs(campaign_setters@campaign_getters@[
    p_update_Campaign_tasks_def,
    p_update_Campaign_paymentOrders_def]);

Theorem tasks_mapping:
    campaign with tasks := MAP f campaign.tasks = campaign' ⇒
    LENGTH campaign'.tasks ≤ LENGTH campaign.tasks
Proof
    rw [] >>
    `(campaign with tasks := MAP f campaign.tasks).tasks = MAP f campaign.tasks` by rw[] >>
    rw[]
QED

Theorem tasks_mapping_1:
    campaign with <|tasks := MAP f campaign.tasks; paymentOrders := B|> = campaign' ⇒
    LENGTH campaign'.tasks ≤ LENGTH campaign.tasks
Proof
    rw [] >>
    `(campaign with <|tasks := MAP f campaign.tasks; paymentOrders := B|>).tasks = MAP f campaign.tasks` by rw[] >>
    rw[]
QED

val getTask_saves_tasks =
        prove (thrm ``getTask``,
        prf getTask_saves_campaign);
val getAgreement_saves_tasks =
        prove (thrm ``getAgreement``,
        prf getAgreement_saves_campaign);
val getPriceChangeWithNumber_saves_tasks =
        prove (thrm ``getPriceChangeWithNumber``,
        prf getPriceChangeWithNumber_saves_campaign);
val getPriceChangesLength_saves_tasks =
        prove (thrm ``getPriceChangesLength``,
        prf getPriceChangesLength_saves_campaign);

in

Theorem task_adding_cases:
    ^(THRM ``execute f``)
Proof
let
val zero_tac = for_Cases_on nxt `f` 24 >>
FULL_SIMP_TAC (simpLib.mk_simpset [])
              [execute_def] >>
rw[] >| tacs;

val first_part = [fs[createPriceChange_def,
    IF_EQUALS_optionErr_3,
    p_add_priceChange_in_Campaign_def] >>
  fs (campaign_setters @ campaign_getters),

`campaign = campaign'` by metis_tac[getTask_saves_campaign] >> fs[],

 apr_rej_acc ``set_task_negotiation`` ``NegotiationApproved``,
 apr_rej_acc ``set_task_negotiation`` ``NegotiationRejected``,
 apr_rej_acc ``set_task_taskStatus`` ``TaskAccepted``
];

val second_part =
[fs[addTask_def, IF_EQUALS_optionErr_3, p_add_task_in_Campaign_def, get_campaign_tasks_def, set_campaign_tasks_def],
fs[addTask_def, IF_EQUALS_optionErr_3, approvedPriceExists_def] ];

val third_part = [
  magic_fs_tac readyToPerformTask_def,

  magic_fs_tac requestGas_def,

  magic_fs_tac paymentCompleted_def >>
    fs[IF_EQUALS] >| [
        metis_tac[tasks_mapping_1],
        `campaign.tasks = campaign'.tasks` by rw[theorem "Campaign_accfupds"] >>
        fs[]
    ],

  magic_fs_tac performTask_def,

  magic_fs_tac taskCompleted_def,

  fs [confirmTask_def, IF_EQUALS_optionErr_3] >>
  FULL_CASES_ULTIMATUM >>
  fs [IF_EQUALS, p_update_Campaign_tasks_def,
     set_campaign_tasks_def, get_campaign_tasks_def,
     set_campaign_paymentOrders_def] >>
  rw [tasks_mapping]
];

in

    zero_tac >|
    (foldr (fn(x,xs) => x::x::x::xs) [] first_part @
    (List.concat $ replicate 3 second_part) @
    foldr (fn(x,xs) => x::x::x::xs) [] third_part)
end
QED

end;

(* 5 *)
Theorem status_checking:
    let
        taskStatus = get_task_negotiation $ THE $ FIND ($= taskId o get_task_id) $ get_campaign_tasks campaign;
        agreementStatus = get_agreement_negotiation $ get_campaign_agreement campaign;
        pcStatus = get_priceChange_negotiation $ HD $ get_campaign_priceChanges campaign
    in
        (*Agreement*)
        f ∈ {3; 4} ∧ agreementStatus ≠ WaitingSupplier ∨
        f = 5 ∧ agreementStatus = NegotiationApproved ∨
        (8 ≤ f ∧ f ≤ 11 ∨ f ≥ 13) ∧ agreementStatus ≠ NegotiationApproved ∨
        (*PriceChange*)
        f ∈ {8; 9; 10} ∧ pcStatus ≠ WaitingCustomer ∨
        f = 11 ∧ ¬(pcStatus ∈ {NegotiationApproved; NegotiationRejected}) ∨
        f ≥ 13 ∧ ¬(approvedPriceExists campaign) ∨
        (*Task*)
        f ∈ {13; 14} ∧ params = [SCInt taskId] ∧ taskStatus = NegotiationApproved ∨
        (f = 15 ∧ params = [SCInt taskId] ∨
        (f ∈ {18;19} ∨ f ≥ 21) ∧ params = (SCInt taskId)::_ ∨
        f = 20 ∧ params = (SCInt pId)::_ ∧
        taskId = get_PaymentOrder_taskId $ THE $
            p_get_paymentOrder_by_id campaign pId) ∧
        taskStatus ≠ NegotiationApproved ⇒
        ∃ v. execute f context params campaign = None v
Proof
    rw [] >>
    rw[execute_def] >>
    let val execute_func_defs = map
        (definition o C (curry op^) "_def" o
        Parse.term_to_string)
        execute_funcs 
    in 
        rw(execute_func_defs @ const_defs @ [base_task_fn_def])
    end >>
    rpt (ProjectTools.CASES_ULTIMATUM >> rw[]) >>
    fs[approvedPriceExists_equivalence,
       p_get_task_index_by_id_def,
       p_get_campaign_task_by_task_id_def,
       FIND_def, scToInt_def] >>
    rfs[p_get_paymentOrder_by_id_def] >>
    fs[]
QED
