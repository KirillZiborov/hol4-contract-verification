(* 6 *)
Definition getPriceChangeWithNumber:
  getPriceChangeWithNumber context params campaign = 
    if checkTypes params [TypeInt] ∧
       isSenderCustomer context campaign ∧
       get_campaign_phase campaign = PhaseTasks
    then
        let
            number = scToInt (HD params);
            priceChange = oEL number (get_campaign_priceChanges campaign);
        in case priceChange of
          | NONE => None "Price change does not exist."
          | SOME priceChange => Ret (SCCampaign campaign) (SCPriceChange priceChange)
    else None "Error."
End

(* 7 *)
Definition getPriceChangesLength:
  getPriceChangesLength context params campaign = 
    if isSenderCustomer context campaign ∧
       get_campaign_phase campaign = PhaseTasks
    then
        if (LENGTH (get_campaign_priceChanges campaign)) > 0 then
            Ret (SCCampaign campaign) (SCInt (LENGTH (get_campaign_priceChanges campaign)))
        else None "No price changes."
    else None "Error."
End

(* 8 *)
Definition rejectPrice:
  rejectPrice context params campaign = 
    if isSenderCustomer context campaign ∧
       get_campaign_phase campaign = PhaseTasks
    then
        let
            priceChange = (p_get_last_price_change campaign);
            priceChanges_cut = oFRONT (get_campaign_priceChanges campaign);
        in case priceChange of
            | SOME priceChange => 
                case (get_priceChange_negotiation priceChange) of 
                    | WaitingCustomer => 
                        case priceChanges_cut of 
                        | SOME priceChanges_cut => 
                            Some (SCCampaign (set_campaign_priceChanges campaign (SNOC (set_priceChange_negotiation priceChange NegotiationRejected) priceChanges_cut)))
                        | NONE => None "No price changes."
                    | _ => None "Customer is not allowed to approve at this point."
            | NONE => None "No price changes."
    else None "Error."
End

(* 9 *)
Definition approvePrice:
  approvePrice context params campaign = 
    if isSenderCustomer context campaign ∧
       get_campaign_phase campaign = PhaseTasks
    then
        let
            priceChange = (p_get_last_price_change campaign);
            priceChanges_cut = oFRONT (get_campaign_priceChanges campaign);
        in case priceChange of
            | SOME priceChange => 
                case (get_priceChange_negotiation priceChange) of 
                    | WaitingCustomer => 
                        case priceChanges_cut of 
                        | SOME priceChanges_cut => 
                            Some (SCCampaign (set_campaign_priceChanges campaign (SNOC (set_priceChange_negotiation priceChange NegotiationRejected) priceChanges_cut)))
                        | NONE => None "No price changes."
                    | _ => None "Customer is not allowed to approve at this point."
            | NONE => None "No price changes."
    else None "Error."
End

(* 10 *)
Definition declinePrice:
  declinePrice context params campaign =
    if isSenderCustomer context campaign ∧
       get_campaign_phase campaign = PhaseTasks
    then
        Some (SCCampaign (set_campaign_phase campaign PhaseDeclined))
    else
        None "Error."
End

(* 11 *)
Definition createPriceChange:
  createPriceChange context params campaign = 
    if checkTypes params [TypeInt; TypeNegotiation; TypeInt;] ∧
       isSenderSupplier context campaign ∧
       get_campaign_phase campaign = PhaseTasks
    then
        let
            price = scToInt (EL 0 params);
            negotiation = scToNegotiation (EL 1 params);
            startTime = scToInt (EL 2 params);

            last_priceChange = p_get_last_price_change campaign;
            new_priceChange = (PriceChange price negotiation startTime);
        in case last_priceChange of 
            | SOME last_priceChange =>
                if (get_priceChange_negotiation last_priceChange) = NegotiationApproved ∨ 
                    (get_priceChange_negotiation last_priceChange) = NegotiationRejected 
                then
                    Some (SCCampaign (set_campaign_priceChanges campaign (SNOC new_priceChange (get_campaign_priceChanges campaign))))
                else
                    None "The last change of price should be approved or rejected before adding new priceChange."
            | NONE => Some (SCCampaign (set_campaign_priceChanges campaign [new_priceChange]))
    else None "Error."
End

