(*START ------------------------------------------------------------------------- *)
open preamble
open basis
open ml_monad_translator_interfaceLib

open stringTheory
open wordsTheory
open listTheory

val _ = new_theory "sc1Types";
val _ = translation_extends "basisProg";
val _ = ParseExtras.temp_tight_equality ();


(*DEFINITIONS ------------------------------------------------------------------- *)
Datatype:
    Negotiation = NotSet | WaitingCustomer | WaitingSupplier | NegotiationRejected | NegotiationApproved ;
    PaymentStatus = WaitingForPayment | PaymentCompleted | PaymentRejected ;
    Phase = PhaseAgreement | PhaseTasks | PhaseDeclined ;
    TaskStatus = TaskNotAccepted | TaskAccepted | TaskReadyToPerform | GasRequested | Performing | Confirmed | TaskCompleted ;
    PaymentType = Pre | Post | Delayed
End

Datatype:
    Person = <|id:num; name:string|>;
    AgreementDetails = <|details:string; bankAddress:num|>;
    Agreement = <|negotiation:Negotiation; customer:Person; supplier:Person; details:AgreementDetails|>;
    PriceChange = <|price:num; negotiation:Negotiation; startTime:num|>;
    PaymentOrder = <|amount:num; paymentTime:num; paymentId:num; taskId:num; paymentStatus:PaymentStatus; direction:bool|>;
    Task = <|taskID:num; negotiation:Negotiation; captain:Person; worker:Person; expectedGas:num; requestedGas:num; suppliedGas:num; totalGas:num; requestTime:num; suppliedTime:num; completionTime:num; paymentTime:num; taskStatus:TaskStatus; paymentType:PaymentType|>;
    Campaign = <|agreement:Agreement; tasks:Task list; negotiation:Negotiation; priceChanges:PriceChange list; phase:Phase; paymentOrders:PaymentOrder list|>;
End

Datatype:
    SCType = TypeUnit | TypeInt | TypeString | TypeBool | TypeAgreement | TypeTask | TypeNegotiation | TypePriceChange | TypePaymentOrder | TypeCampaign | TypePerson  | TypeList  | TypePaymentStatus | TypeAgreementDetails  | TypeTaskStatus  | TypePaymentType | TypePhase
End

Datatype:
    SCvalue = SCUnit | SCInt num | SCString string | SCBool bool | SCAgreement Agreement | SCTask Task | SCNegotiation Negotiation | SCPriceChange PriceChange | SCPaymentOrder PaymentOrder | SCCampaign Campaign | SCPerson Person | SCPaymentStatus PaymentStatus  | SCTaskStatus TaskStatus  | SCAgreementDetails AgreementDetails  | SCPaymentType PaymentType | SCPhase Phase
End

Datatype:
    Context = <|msgSender:num; blockNum:num; storage:word8 list|>
End

Datatype:
    State = <| context: Context; campaign:Campaign |>
End

Datatype:
    Params = <| l: (SCvalue list) |>
End


Datatype:
    optionErr = Some 'a | Ret 'a 'a | None string
End

Datatype:
    optErrSC = Some' SCvalue | None' string
End

Datatype:
  returnType = <| state : Campaign; value : optErrSC |>
End

(*  returnType = Campaign * optErrSC *)

(*MONADIC CONFIGURATION  --------------------------------------------------------------- *)
(* Create the data type to handle the references *)
(* example:
Datatype:
  state_references = <|
                   ref1 : num ;
                   ref2 : int;
                   rarray1 : num list ;
                   rarray2 : int list;
                   farray1 : num list;
                   farray2 : int list;
                   |>
End
*)
Type state_references = ``:State``

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string (* | Subscript *)
End

(* we don't use it!
val config =  global_state_config
              |> with_state ``:state_references``
              |> with_exception ``:state_exn``
*)
            (*|> with_refs [("ref1", ``36 : num``),
                         ("ref2", ``42 : int``)]
              |> with_fixed_arrays [
                ("farray1", ``0 : num``, 12,
                  ``Subscript``, ``Subscript``),
                ("farray2", ``0 : int``, 7,
                  ``Subscript``, ``Subscript``)
              ]
              |> with_resizeable_arrays [
                ("rarray1", ``[] : num list``,
                  ``Subscript``, ``Subscript``),
                ("rarray2", ``[] : int list``,
                  ``Subscript``, ``Subscript``)
              ]*)
            (*|> with_stdio "stdio"*)
;
(* Failure :α -> (β, α) exc *)

Definition my_raise_Fail_def:
    my_raise_Fail (e1 :string) :State -> (α, state_exn) exc # State =
    (λ(state :State).
       ((Failure (Fail e1 :state_exn) :(α, state_exn) exc),state))
End

Overload failwith = ``my_raise_Fail``
Overload fail = ``failwith : string -> State -> (α, state_exn) exc # State``  (*α = SCvalue*)
(* We don't use it!
val _ = start_translation config;
*)
(* instead of base$assert *)
Definition assert_def:
  assert (errstr:string) (b:bool) : (state_references, unit, state_exn) M =
    if b then
      return ()
    else
      failwith errstr
End
val _ = export_theory();
