
@[reducible] def TxIn := String
@[reducible] def Ix := Nat
@[reducible] def Slot := Nat
@[reducible] def Coin := Nat
@[reducible] def Address := String
def TxRef := TxIn × Ix
structure TxOut where
  address: Address
  value: Coin

structure UTxO where
  lookup : TxRef → Option TxOut
  remove : List TxRef → UTxO
  add : List TxOut → UTxO
notation (name := with_and_without) start:arg " - " remove:arg " + " add:arg => UTxO.add (UTxO.remove start remove) add
notation (name := between) lower:arg " ≤ " mid:arg " ≤ " upper:arg => (lower ≤ mid) ∧ (mid ≤ upper)

structure UTXOEnv where
  slot: Slot

structure UTXOState where
  utxo: UTxO
  fees: Coin

structure Transaction where
  inputs: List TxRef
  outputs: List TxOut
  valid_range: Slot × Slot
  fee: Coin

def transaction_valid (env: UTXOEnv) (state: UTXOState) (transaction: Transaction): Bool :=
  let (valid_start, valid_end) := transaction.valid_range
  let current_slot := env.slot
  let resolved_inputs := transaction.inputs.map state.utxo.lookup
  let consumed := List.sum $ List.map (λ out => if let some out := out then out.value else 0) resolved_inputs
  let produced := transaction.fee + (List.sum $ List.map (fun o => o.value) transaction.outputs)

  List.and [
    valid_start ≤ current_slot ≤ valid_end,
    transaction.fee > 0,
    resolved_inputs.all Option.isSome,
    consumed = produced
  ]

def utxo_transition
  (env: UTXOEnv)
  (state: UTXOState)
  (transaction: Transaction): UTXOState :=
  if transaction_valid env state transaction then
    { state with
        utxo := state.utxo - transaction.inputs + transaction.outputs
        fees := state.fees + transaction.fee
    }
  else
    state

def main : IO Unit := do
  -- let env: UTXOEnv := { slot := 0 }
  -- let state: UTXOState := { utxo := fun _ => { address := "", value := 0 }, fees := 0 }
  -- let transaction: Transaction := { inputs := ∅, valid_range:= (0, 2), outputs := [], fee := 0 }
  -- let newState := utxo_transition env state transaction
  -- dbg_trace "Slot: {newState.fees}"
  return ()

#eval main
