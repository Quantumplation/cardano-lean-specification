@[reducible] def TxId := String
@[reducible] def Ix := Nat
@[reducible] def Slot := Nat
@[reducible] def Coin := Nat
@[reducible] def Address := String
@[reducible] def TxRef := TxId × Ix
structure TxOut where
  address: Address
  value: Coin
instance : ToString TxOut where
  toString (out: TxOut) := s!"{out.address}: {out.value}"

class UTxO (U: Type) where
  lookup : U -> TxRef → Option TxOut
  add : U -> List (TxRef × TxOut) → U
  remove : U -> List TxRef → U

notation (name := between) lower:arg " ≤ " mid:arg " ≤ " upper:arg => (lower ≤ mid) ∧ (mid ≤ upper)

structure UTXOEnv where
  slot: Slot
instance : ToString UTXOEnv where
  toString (env: UTXOEnv) := s!"Env:
    slot: {env.slot}"

structure UTXOState (U: Type) [UTxO U] where
  utxo: U
  fees: Coin

structure Transaction where
  txId: TxId
  inputs: List TxRef
  outputs: List TxOut
  valid_range: Slot × Slot
  fee: Coin

instance : ToString Transaction where
  toString (tx: Transaction) := s!"Transaction:
    txId: {tx.txId}
    inputs: {tx.inputs}
    outputs: {tx.outputs}
    valid_range: {tx.valid_range}
    fee: {tx.fee}"

section
variable {U: Type} [UTxO U] [ToString U]

instance : ToString (UTXOState U) where
  toString (state: UTXOState U) := s!"State:
    utxo: {state.utxo}
    fees: {state.fees}"

def transaction_valid (env: UTXOEnv) (state: UTXOState U) (transaction: Transaction): Bool :=
  let (valid_start, valid_end) := transaction.valid_range
  let current_slot := env.slot
  let resolved_inputs := transaction.inputs.map (UTxO.lookup state.utxo)
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
  (state: UTXOState U)
  (transaction: Transaction): UTXOState U :=
  if transaction_valid env state transaction then
    let outputs := transaction.outputs.mapIdx (λ idx out => ((transaction.txId, idx), out))
    let utxo := state.utxo
    let utxo' := UTxO.remove utxo transaction.inputs
    let utxo'' := UTxO.add utxo' outputs
    { state with
        utxo := utxo''
        fees := state.fees + transaction.fee
    }
  else
    state

end

@[reducible] def UTXOList := List (TxRef × TxOut)
instance : UTxO UTXOList where
  lookup l r := l.find? (fun (r', _) => r == r') |>.map Prod.snd
  add l new := l ++ new
  remove l refs := l.filter (fun (r, _) => !refs.contains r)

#eval
  let env: UTXOEnv := dbgTraceVal $ { slot := 1 }
  let utxo: UTXOList := [
    (("a", 0), { address := "addr1", value := 2 }),
    (("b", 1), { address := "addr2", value := 3 })
  ]
  let state := dbgTraceVal $ { utxo := utxo, fees := 0 }
  let tx := dbgTraceVal $ {
    txId := "c",
    inputs := [("a", 0)],
    outputs := [{ address := "addr3", value := 1 }],
    valid_range := (0, 2),
    fee := 1
  }
  utxo_transition env state tx
