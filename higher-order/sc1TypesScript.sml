(*START ------------------------------------------------------------------------- *)

open arithmeticTheory listTheory stringTheory wordsTheory HolKernel boolLib Parse bossLib optionTheory llistTheory;

val _ = new_theory "sc1Types";

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
    SCType = TypeInt | TypeString | TypeBool | TypeAgreement | TypeTask | TypeNegotiation | TypePriceChange | TypePaymentOrder | TypeCampaign | TypePerson  | TypeList  | TypePaymentStatus | TypeAgreementDetails  | TypeTaskStatus  | TypePaymentType | TypePhase
End

Datatype:
    SCvalue = SCInt num | SCString string | SCBool bool | SCAgreement Agreement | SCTask Task | SCNegotiation Negotiation | SCPriceChange PriceChange | SCPaymentOrder PaymentOrder | SCCampaign Campaign | SCPerson Person | SCPaymentStatus PaymentStatus  | SCTaskStatus TaskStatus  | SCAgreementDetails AgreementDetails  | SCPaymentType PaymentType | SCPhase Phase
End

Datatype:
    Context = <|msgSender:num; blockNum:num|>
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

val _ = export_theory();
