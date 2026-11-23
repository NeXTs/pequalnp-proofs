import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_739

-- Constant propagation follows the restriction pass of L-meta-527, itself adapted from L-meta-468.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def BinaryGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

private lemma simpBinary (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or)
    (m : ℕ) (xs : List (Bool ⊕ ℕ)) :
    ∀ q ∈ (simplifyGate g.op m xs).1, BinaryGate q := by
  intro q mem
  rcases h with e | e
  · simp only [e, simplifyGate] at mem
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at mem
    subst mem
    simp [BinaryGate]
  · simp only [e, simplifyGate] at mem
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at mem
    subst mem
    simp [BinaryGate]

private lemma elimPass_binary (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hacc : ∀ g ∈ acc.2, BinaryGate g) :
    ∀ g ∈ (elimPass m gs acc).2, BinaryGate g := by
  induction gs generalizing acc with
  | nil => exact hacc
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih _ (fun q hq => hok q (List.mem_cons_of_mem _ hq))
    intro q mem
    rcases List.mem_append.mp mem with e | e
    · exact hacc q e
    · exact simpBinary g (hok g List.mem_cons_self) _ _ q (by simpa using e)

private lemma size_folds (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons,List.length_cons]
    have lower := ih (elimStep m acc g)
    have step : (elimStep m acc g).2.length ≤ acc.2.length+1 := by
      simp only [elimStep,List.length_append]
      exact Nat.add_le_add_left (toList_opt_len_le _) _
    omega

private def initId (n : ℕ) : List (Bool ⊕ ℕ) × List Gate :=
  (List.ofFn (fun i : Fin n => Sum.inr i.val), [])

private theorem initInv (n : ℕ) (x : Fin n → Bool) :
    ElimInv n (List.ofFn x) (List.ofFn x) (initId n) := by
  refine ⟨by simp, by simp [initId], ?_⟩
  intro i
  by_cases h : i < n
  · have st : (initId n).1.getD i (.inl false) = .inr i := by
      unfold initId
      exact ofFn_getD_lt _ _ _ h
    rw [st]
    exact ⟨by simpa [statValid,initId] using h,rfl⟩
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial,rfl⟩

theorem normalizeOutputs {n m : ℕ} (D : Circuit) (o : Fin m → ℕ)
    (mono : IsMonotoneCircuit D) (fan : ∀ g ∈ D.gates, g.inputs.length ≤ 2)
    (varies : ∀ w : Fin m, ∃ x y : Fin n → Bool,
      (D.wires (List.ofFn x)).getD (o w) false ≠ (D.wires (List.ofFn y)).getD (o w) false) :
    ∃ (E : Circuit) (q : Fin m → ℕ), E.size ≤ D.size ∧
      (∀ g ∈ E.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      ∀ (x : Fin n → Bool) (w : Fin m),
        (E.wires (List.ofFn x)).getD (q w) false = (D.wires (List.ofFn x)).getD (o w) false := by
  let acc := elimPass n D.gates (initId n)
  let E : Circuit := ⟨acc.2,0⟩
  have sound (x : Fin n → Bool) (w : Fin m) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD (o w) (.inl false)) =
        (D.wires (List.ofFn x)).getD (o w) false :=
    ((elimInv_pass n (List.ofFn x) D.gates _ (initId n)
      (fun g gm => ⟨(mono g gm).imp_right Or.inl,fan g gm⟩)
      (initInv n x)).2.2 (o w)).2
  have pick (w : Fin m) : ∃ j, ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD j false = (D.wires (List.ofFn x)).getD (o w) false := by
    cases e : acc.1.getD (o w) (.inl false) with
    | inl b =>
      obtain ⟨x,y,h⟩ := varies w
      have xVal := sound x w
      have yVal := sound y w
      rw [e] at xVal yVal
      exact False.elim (h (xVal.symm.trans yVal))
    | inr j =>
      refine ⟨j,fun x => ?_⟩
      have eq := sound x w
      rw [e] at eq
      exact eq
  choose q res using pick
  refine ⟨E,q,?_,?_,fun x w => res w x⟩
  · have size := size_folds n D.gates (initId n)
    simpa [E,acc,Circuit.size,initId] using size
  · exact elimPass_binary n D.gates (initId n) mono (by simp [initId])

end PEqualNP.Outside.L_meta_739


namespace PEqualNP.Outside.L_meta_739

open PEqualNP.CircuitLowerBounds

def single {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j=i)

def pop {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i=true).card

def LineTests (P L k : ℕ) (S : Fin L → Finset (Fin P)) (C : Circuit) : Prop :=
  ∀ (x : Fin P → Bool) (y : Fin L → Bool), pop y = 1 → pop x ≤ k →
    C.eval (List.ofFn x ++ List.ofFn y) =
      decide (∃ w : Fin L, y w = true ∧ ∃ p ∈ S w, x p = true)

private theorem pop_single {n : ℕ} (i : Fin n) : pop (single i) = 1 := by
  have eq : Finset.univ.filter (fun j : Fin n => single i j=true) = {i} := by
    ext j
    simp [single]
  simp [pop,eq]

private theorem pop_off (n : ℕ) : pop (fun _ : Fin n => false) = 0 := by
  simp [pop]

private theorem test_one {P L k : ℕ} {S : Fin L → Finset (Fin P)} {C : Circuit}
    (tests : LineTests P L k S C) (x : Fin P → Bool) (w : Fin L) (few : pop x ≤ k) :
    C.eval (List.ofFn x ++ List.ofFn (single w)) = decide (∃ p ∈ S w, x p=true) := by
  rw [tests x (single w) (pop_single w) few]
  simp [single]

-- Pointwise monotonicity of an AND/OR pass follows the argument in LineDegTest.
private theorem gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (l r : List Bool) (below : ∀ i, l.getD i false=true → r.getD i false=true)
    (on : g.op.eval (g.inputs.map fun i => l.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => r.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at on ⊢ <;> simp [GateOp.eval] at on ⊢
  · intro i hi
    exact below i (on i hi)
  · obtain ⟨i,hi,it⟩ := on
    exact ⟨i,hi,below i it⟩

private theorem run_mono (gs : List Gate) (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (l r : List Bool) (length : l.length=r.length)
    (below : ∀ i, l.getD i false=true → r.getD i false=true) :
    ∀ i, (wiresFrom gs l).getD i false=true → (wiresFrom gs r).getD i false=true := by
  induction gs generalizing l r with
  | nil => exact below
  | cons g gs ih =>
    rw [wiresFrom_cons,wiresFrom_cons]
    apply ih (fun q qm => mono q (List.mem_cons_of_mem _ qm))
    · simp [length]
    · intro i h
      by_cases next : i=l.length
      · rw [getD_snoc_eq _ _ _ _ next] at h
        rw [getD_snoc_eq _ _ _ _ (next.trans length)]
        exact gate_mono g (mono g List.mem_cons_self) l r below h
      · rw [getD_snoc_ne _ _ _ _ next] at h
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact below i h

private theorem no_lines_le {P L : ℕ} {C : Circuit} (mono : IsMonotoneCircuit C)
    (x : Fin P → Bool) (y : Fin L → Bool)
    (active : C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false))=true) :
    C.eval (List.ofFn x ++ List.ofFn y)=true := by
  refine run_mono C.gates mono
    (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) (List.ofFn x ++ List.ofFn y)
      (by simp) ?_ C.output active
  intro i on
  by_cases lo : i < (List.ofFn x).length
  · rw [List.getD_append _ _ _ _ lo] at on ⊢
    exact on
  · simp only [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_of_not_gt lo)] at on
    rw [← List.getD_eq_getElem?_getD] at on
    have off : ∀ j : ℕ, (List.ofFn (fun _ : Fin L => false)).getD j false = false := by
      intro j
      by_cases h : j<L
      · rw [ofFn_getD_lt _ _ _ h]
      · exact List.getD_eq_default _ _ (by simp; omega)
    rw [off] at on
    cases on

private theorem base_off {P L k : ℕ} {S : Fin L → Finset (Fin P)} {C : Circuit}
    (mono : IsMonotoneCircuit C) (test : LineTests P L k S C) (x : Fin P → Bool)
    (w : Fin L) (few : pop x ≤ k) (away : ∀ p∈S w, x p = false) :
    C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false))=false := by
  by_contra active
  have line := no_lines_le mono x (single w) (Bool.eq_true_of_not_eq_false active)
  rw [test_one test x w few] at line
  obtain ⟨i,mi,on⟩ := of_decide_eq_true line
  rw [away i mi] at on
  cases on

private theorem singleton_base {P L k : ℕ} {S : Fin L → Finset (Fin P)} {C : Circuit}
    (mono : IsMonotoneCircuit C) (test : LineTests P L k S C)
    (hK : 1 ≤ k) (notCommon : ∀ (w : Fin L) (p : Fin P), p ∈ S w → ∃ u : Fin L, p ∉ S u)
    (w : Fin L) (p : Fin P) :
    C.eval (List.ofFn (single p) ++ List.ofFn (fun _ : Fin L => false))=false := by
  have offSome : ∃ u : Fin L, p ∉ S u := by
    by_cases mem : p ∈ S w
    · exact notCommon w p mem
    · exact ⟨w,mem⟩
  obtain ⟨u,miss⟩ := offSome
  apply base_off mono test (single p) u (by simpa only [pop_single] using hK)
  intro q mem
  have ne : q ≠ p := fun e => miss (e ▸ mem)
  simp [single,ne]

theorem lineEssential {P L k q : ℕ} {S : Fin L → Finset (Fin P)} {C : Circuit}
    (mono : IsMonotoneCircuit C) (test : LineTests P L k S C)
    (hK : 1 ≤ k) (hQ : 2 ≤ q) (same : ∀ w, (S w).card = q)
    (notCommon : ∀ (w : Fin L) (p : Fin P), p ∈ S w → ∃ u : Fin L, p ∉ S u)
    (w : Fin L) :
    ∃ x : Fin P → Bool,
      C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) = false ∧
      C.eval (List.ofFn x ++ List.ofFn (single w)) = true := by
  have positive : 0 < (S w).card := by rw [same]; omega
  obtain ⟨p,mp⟩ := Finset.card_pos.mp positive
  refine ⟨single p,singleton_base mono test hK notCommon w p,?_⟩
  rw [test_one test (single p) w (by simpa only [pop_single] using hK)]
  exact decide_eq_true ⟨p,mp,by simp [single]⟩

def CoefficientBound : Prop :=
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ),
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ i : Fin m, 2 ≤ (S i).card) →
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) →
    (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
    (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

theorem boundAfterTransposition (L0 : CoefficientBound)
    {P L k q c : ℕ} {S : Fin L → Finset (Fin P)} {C D : Circuit}
    (hK : 1 ≤ k) (hQ : 2 ≤ q) (same : ∀ w, (S w).card = q)
    (intersects : ∀ i j : Fin L, i ≠ j → (S i ∩ S j).card ≤ 1)
    (notCommon : ∀ (w : Fin L) (p : Fin P), p ∈ S w → ∃ u : Fin L, p ∉ S u)
    (mono : IsMonotoneCircuit C) (test : LineTests P L k S C)
    (Dmono : IsMonotoneCircuit D) (Dfan : ∀ g∈D.gates, g.inputs.length ≤ 2)
    (T : Finset (Fin L)) (o : Fin L → ℕ)
    (decomp : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      C.eval (List.ofFn x ++ List.ofFn y) =
        (C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) ||
          decide (∃ u : Fin L, y u = true ∧
            (u ∈ T ∨ (D.wires (List.ofFn x)).getD (o u) false = true))))
    (transCost : D.size + L ≤ C.size+1) (hcK : c ≤ k) (hcQ : c+1 ≤ q) :
    L*c+L ≤ C.size+1 := by
  let coeff (w : Fin L) (x : Fin P → Bool) := (D.wires (List.ofFn x)).getD (o w) false
  let baseline (x : Fin P → Bool) := C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false))
  have read (w : Fin L) (x : Fin P → Bool) :
      C.eval (List.ofFn x ++ List.ofFn (single w)) =
        (baseline x || decide (w ∈ T ∨ coeff w x = true)) := by
    simpa [single,baseline,coeff] using decomp x (single w)
  have loses (w : Fin L) (x : Fin P → Bool) (few : pop x ≤ k) (off : ∀ p∈S w, x p=false) :
      C.eval (List.ofFn x ++ List.ofFn (single w)) = false := by
    rw [test_one test x w few]
    apply decide_eq_false
    rintro ⟨p,pm,hp⟩
    rw [off p pm] at hp
    cases hp
  have offCoeff (w : Fin L) (x : Fin P → Bool) (few : pop x ≤ k) (off : ∀ p∈S w, x p=false) :
      coeff w x = false := by
    by_contra active
    have h := read w x
    rw [loses w x few off] at h
    simp [Bool.eq_true_of_not_eq_false active] at h
  have noT (w : Fin L) : w ∉ T := by
    intro inside
    let x : Fin P → Bool := fun _ => false
    have h := read w x
    rw [loses w x (by simp [x,pop_off]) (by intros; rfl)] at h
    simp [inside] at h
  have exactSingleton (w : Fin L) (p : Fin P) :
      coeff w (single p) = true ↔ p∈S w := by
    have e : C.eval (List.ofFn (single p) ++ List.ofFn (single w)) = decide (p∈S w) := by
      rw [test_one test (single p) w (by simpa only [pop_single] using hK)]
      simp [single]
    have shape := read w (single p)
    have b : baseline (single p) = false := singleton_base mono test hK notCommon w p
    rw [e,b] at shape
    simp only [noT w,false_or] at shape
    constructor
    · intro on
      rw [on] at shape
      exact of_decide_eq_true shape
    · intro mem
      rw [decide_eq_true mem] at shape
      exact of_decide_eq_true shape.symm
  have varies (w : Fin L) : ∃ x y : Fin P → Bool, coeff w x ≠ coeff w y := by
    have positive : 0 < (S w).card := by rw [same]; omega
    obtain ⟨p,mp⟩ := Finset.card_pos.mp positive
    have constFalse : coeff w (fun _ => false)=false := offCoeff w _ (by simp [pop_off]) (by intros; rfl)
    exact ⟨single p,fun _=>false,by rw [(exactSingleton w p).mpr mp,constFalse]; decide⟩
  obtain ⟨E,r,small,binary,ext⟩ := normalizeOutputs D o Dmono Dfan varies
  have bound := L0 P L k S E r (fun _=>c) intersects (by intro w; rw [same]; exact hQ) binary
    (by
      intro w p
      change (E.wires (List.ofFn (single p))).getD (r w) false = true ↔ p ∈ S w
      rw [ext (single p) w]
      exact exactSingleton w p)
    (fun w x few off => (ext x w).trans (offCoeff w x few off))
    (fun _ => hcK) (by intro w; rw [same]; exact hcQ)
  have scale : (∑ _ : Fin L, c)=L*c := by simp
  rw [scale] at bound
  omega

end PEqualNP.Outside.L_meta_739


namespace PEqualNP.Outside.L_meta_739

open PEqualNP.CircuitLowerBounds

def lowerIdx (t i : ℕ) : ℕ := if i < t then i else i-1

def lowerGate (t : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (lowerIdx t)⟩

def runG {α : Type*} (f : GateOp → List α → α) (d : α) (gs : List Gate) (w : List α) :=
  gs.foldl (fun w g => w ++ [f g.op (g.inputs.map fun i => w.getD i d)]) w

theorem runG_length {α : Type*} (f : GateOp → List α → α) (d : α) (gs : List Gate) :
    ∀ w, (runG f d gs w).length = w.length+gs.length := by
  induction gs with
  | nil => simp [runG]
  | cons g gs ih => intro w; unfold runG; rw [List.foldl_cons]; change (runG f d gs _).length = _; rw [ih]; simp; omega

theorem getSkip {α : Type*} (pre post : List α) (entry d : α) {i : ℕ} (h : i ≠ pre.length) :
    (pre ++ post).getD (lowerIdx pre.length i) d = ((pre ++ [entry]) ++ post).getD i d := by
  by_cases lt : i < pre.length
  · simp only [lowerIdx, ite_eq_left lt, List.getD_append _ _ _ _ lt]
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ lt]
  · rw [lowerIdx, ite_eq_right lt, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1
    simp
    omega

theorem suffixSim {α : Type*} (f : GateOp → List α → α) (d : α) (pre : List α) (entry : α)
    (gs : List Gate) : ∀ (post : List α), (∀ g ∈ gs, pre.length ∉ g.inputs) →
    ∃ extra : List α,
      runG f d gs ((pre ++ [entry]) ++ post) = (pre ++ [entry]) ++ extra ∧
      runG f d (gs.map (lowerGate pre.length)) (pre ++ post) = pre ++ extra := by
  induction gs with
  | nil => intro post _; exact ⟨post,rfl,rfl⟩
  | cons g gs ih =>
    intro post avoid
    let v := f g.op (g.inputs.map fun i => ((pre ++ [entry]) ++ post).getD i d)
    have he : (g.inputs.map (lowerIdx pre.length)).map (fun i => (pre ++ post).getD i d) =
        g.inputs.map (fun i => ((pre ++ [entry]) ++ post).getD i d) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      apply getSkip
      exact fun eq => avoid g (by simp) (eq ▸ hi)
    obtain ⟨extra,orig,new⟩ := ih (post ++ [v]) (fun h hh => avoid h (by simp [hh]))
    refine ⟨extra, ?_, ?_⟩
    · change runG f d gs ((((pre ++ [entry]) ++ post) ++ [v])) = _
      rwa [List.append_assoc (pre ++ [entry]) post]
    · change runG f d (gs.map (lowerGate pre.length))
         ((pre ++ post) ++ [f g.op ((g.inputs.map _).map _)]) = _
      rw [he, List.append_assoc pre post]
      exact new

theorem removeSim {α : Type*} (f : GateOp → List α → α) (d : α) (pre suf : List Gate) (g : Gate)
    (w : List α) (n t o : ℕ) (hn : w.length = n) (ht : t=n+pre.length)
    (avoid : ∀ h ∈ suf, t ∉ h.inputs) (ho : o ≠ t) :
    (runG f d (pre ++ suf.map (lowerGate t)) w).getD (lowerIdx t o) d =
    (runG f d (pre ++ g::suf) w).getD o d := by
  let A := runG f d pre w
  have hA : A.length = t := by simp [A,runG_length,hn,ht]
  let v := f g.op (g.inputs.map fun i => A.getD i d)
  obtain ⟨next,h₁,h₂⟩ := suffixSim f d A v suf [] (by simpa only [hA] using avoid)
  simp only [List.append_nil, hA] at h₁ h₂
  unfold runG at h₁ h₂ ⊢
  simp only [List.foldl_append, List.foldl_cons]
  change (List.foldl _ A _).getD _ d = (List.foldl _ (A++[v]) suf).getD o d
  rw [h₁,h₂, ← hA]
  exact getSkip A next v d (hA ▸ ho)

def degOp (op : GateOp) (vs : List ℕ) : ℕ :=
  @ite ℕ (op = GateOp.and) (lineDegreeGateOpDecEq _ _) vs.sum (vs.foldr max 0)

def liveRel (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ i : Fin C.gates.length, b = n+i.val ∧ a ∈ (C.gates.get i).inputs

def allLive (n : ℕ) (C : Circuit) : Prop := ∀ i : Fin C.gates.length,
  Relation.ReflTransGen (liveRel n C) (n+i.val) C.output

theorem lastDead (n : ℕ) (C : Circuit) (h : ¬ allLive n C) :
    ∃ i : Fin C.gates.length, C.output ≠ n+i.val ∧
       ∀ j : Fin C.gates.length, i.val < j.val → n+i.val ∉ (C.gates.get j).inputs := by
  classical
  let bad := Finset.univ.filter (fun i : Fin C.gates.length =>
       ¬ Relation.ReflTransGen (liveRel n C) (n+i.val) C.output)
  have nonempty : bad.Nonempty := by
    by_contra none
    apply h
    intro i
    by_contra hn
    exact none ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  let i := bad.max' nonempty
  have hi : i ∈ bad := Finset.max'_mem _ _
  have nolive := (Finset.mem_filter.mp hi).2
  refine ⟨i, fun eq => nolive (eq ▸ Relation.ReflTransGen.refl), ?_⟩
  intro j hj mem
  have next : liveRel n C (n+i.val) (n+j.val) := ⟨by omega,j,rfl,mem⟩
  have jb : j ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    fun live => nolive ((Relation.ReflTransGen.single next).trans live)⟩
  have bound := Finset.le_max' bad j jb
  exact (not_le_of_gt hj) bound


theorem removeDead (n : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (mark : Finset ℕ) (hd : ¬ allLive n C) :
    ∃ D : Circuit, D.size < C.size ∧ IsMonotoneCircuit D ∧
      (∀ g ∈ D.gates, g.inputs.length ≤ 2) ∧
      (∀ w : List Bool, w.length=n → D.eval w=C.eval w) ∧ D.lineDeg n mark = C.lineDeg n mark := by
  obtain ⟨i,ho,havoid⟩ := lastDead n C hd
  let pre := C.gates.take i.val
  let g := C.gates.get i
  let suf := C.gates.drop (i.val+1)
  let t := n+i.val
  have split : C.gates=pre++g::suf := by
    change C.gates = C.gates.take i.val ++ C.gates[i.val] :: C.gates.drop (i.val+1)
    conv_lhs => rw [← List.take_append_drop (i.val+1) C.gates]
    rw [List.take_succ_eq_append_getElem i.isLt, List.append_assoc]
    rfl
  have plen : pre.length=i.val := by simp [pre]
  have avoid : ∀ h ∈ suf, t ∉ h.inputs := by
    intro h mem
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp mem
    have hlen : j<suf.length := hj
    have total : i.val+1+j<C.gates.length := by simp [suf] at hlen; omega
    let k : Fin C.gates.length := ⟨i.val+1+j,total⟩
    have same : C.gates.get k=h := by
      change C.gates[i.val+1+j]=h
      simpa [suf,List.getElem_drop] using he
    rw [← same]
    exact havoid k (by change i.val < i.val+1+j; omega)
  let D : Circuit := ⟨pre++suf.map (lowerGate t),lowerIdx t C.output⟩
  refine ⟨D,?_,?_,?_,?_,?_⟩
  · change (pre++suf.map _).length < C.gates.length
    rw [split]
    simp
  · intro h mem
    change h ∈ pre++suf.map (lowerGate t) at mem
    rcases List.mem_append.mp mem with hp | hs
    · exact hm h (split ▸ List.mem_append_left _ hp)
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
      exact hm a (split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  · intro h mem
    change h ∈ pre++suf.map (lowerGate t) at mem
    rcases List.mem_append.mp mem with hp | hs
    · exact hf h (split ▸ List.mem_append_left _ hp)
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
      simpa [lowerGate] using hf a (split ▸ List.mem_append_right _ (List.mem_cons_of_mem _ ha))
  · intro w hw
    change (runG GateOp.eval false _ w).getD _ false = (runG GateOp.eval false C.gates w).getD C.output false
    rw [split]
    exact removeSim _ _ pre suf g w n t _ hw (by rw [plen]) avoid ho
  · let w := (List.range n).map (fun i => if i ∈ mark then 1 else 0)
    change (runG degOp 0 _ w).getD _ 0 = (runG degOp 0 C.gates w).getD C.output 0
    rw [split]
    exact removeSim _ _ pre suf g w n t _ (by simp [w]) (by rw [plen]) avoid ho

theorem pruneLive (n : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C)
    (hf : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (mark : Finset ℕ) :
    ∃ D : Circuit, D.size ≤ C.size ∧ IsMonotoneCircuit D ∧
      (∀ g ∈ D.gates, g.inputs.length ≤ 2) ∧
      (∀ w : List Bool, w.length=n → D.eval w=C.eval w) ∧
      D.lineDeg n mark = C.lineDeg n mark ∧ allLive n D := by
  classical
  by_cases live : allLive n C
  · exact ⟨C, le_rfl,hm,hf,fun _ _ => rfl,rfl,live⟩
  obtain ⟨D,lt,dm,df,de,dd⟩ := removeDead n C hm hf mark live
  obtain ⟨E,le,em,ef,ee,ed,el⟩ := pruneLive n D dm df mark
  exact ⟨E,le.trans lt.le,em,ef,fun w hw => (ee w hw).trans (de w hw),ed.trans dd,el⟩
termination_by C.size

end PEqualNP.Outside.L_meta_739

namespace PEqualNP.Outside.L_meta_739

open PEqualNP.CircuitLowerBounds

private def actualWire (C : Circuit) (x : List Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates x).getD i false

private def guardedWire (C : Circuit) (x : List Bool) (p i : ℕ) : Bool :=
  if i < p then actualWire C x i else false

-- The guarded gate computation follows L-meta-614's wire trace.
private theorem actualGate (C : Circuit) (x : List Bool) {i : ℕ} {g : Gate}
    (found : C.gates[i]? = some g) :
    actualWire C x (x.length+i) =
      g.op.eval (g.inputs.map (guardedWire C x (x.length+i))) := by
  obtain ⟨bound,gate⟩ := List.getElem?_eq_some_iff.mp found
  have split : C.gates = C.gates.take i ++ g :: C.gates.drop (i+1) := by
    have eq := List.take_append_drop i C.gates
    rw [List.drop_eq_getElem_cons bound,gate] at eq
    exact eq.symm
  let pre := wiresFrom (C.gates.take i) x
  have len : pre.length = x.length+i := by
    simp [pre,wiresFrom_length,List.length_take,Nat.min_eq_left bound.le]
  let b := g.op.eval (g.inputs.map fun a => pre.getD a false)
  have expanded : wiresFrom C.gates x = wiresFrom (C.gates.drop (i+1)) (pre ++ [b]) := by
    conv_lhs => rw [split,wiresFrom_append,wiresFrom_cons]
  have newLen : (pre ++ [b]).length = x.length+i+1 := by simp [len]
  calc
    actualWire C x (x.length+i) = b := by
      unfold actualWire
      rw [expanded,wiresFrom_getD_lt _ _ _ (by omega),getD_snoc_eq _ _ _ _ len.symm]
    _ = _ := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro a _
      by_cases earlier : a < x.length+i
      · rw [guardedWire,ite_eq_left earlier,actualWire,expanded,
          wiresFrom_getD_lt (C.gates.drop (i+1)) (pre ++ [b]) a (by omega),
          getD_snoc_lt pre b false a (by omega)]
      · rw [guardedWire,ite_eq_right earlier,List.getD_eq_default _ _ (by omega)]

private theorem goesBack (C : Circuit) (x y : List Bool) (length : x.length=y.length) (j : ℕ)
    (differs : actualWire C x j ≠ actualWire C y j) :
    ∃ i<x.length, x.getD i false ≠ y.getD i false ∧
      Relation.ReflTransGen (liveRel x.length C) i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases input : j < x.length
    · refine ⟨j,input,?_,.refl⟩
      simpa only [actualWire,wiresFrom_getD_lt _ _ _ input,
        wiresFrom_getD_lt _ _ _ (length ▸ input)] using differs
    have hb : j < x.length+C.gates.length := by
      by_contra! even
      apply differs
      unfold actualWire
      rw [List.getD_eq_default _ _ (by rwa [wiresFrom_length]),
        List.getD_eq_default _ _ (by rwa [wiresFrom_length,← length])]
    let k : Fin C.gates.length := ⟨j-x.length,by omega⟩
    let g : Gate := C.gates.get k
    have jEq : x.length+k.val=j := by dsimp [k]; omega
    have found : C.gates[k.val]?=some g := by
      rw [List.getElem?_eq_getElem k.isLt]
      rfl
    have valX : actualWire C x j = g.op.eval (g.inputs.map (guardedWire C x j)) := by
      simpa only [jEq] using actualGate C x found
    have valY : actualWire C y j = g.op.eval (g.inputs.map (guardedWire C y j)) := by
      simpa only [← length,jEq] using actualGate C y found
    have earlier : ∃ i∈g.inputs, i<j ∧ actualWire C x i ≠ actualWire C y i := by
      by_contra! same
      apply differs
      rw [valX,valY]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i mem
      by_cases h : i<j <;> simp [guardedWire,h,same i mem]
    obtain ⟨i,mem,ilt,diff⟩ := earlier
    obtain ⟨u,ui,ud,path⟩ := ih i ilt diff
    exact ⟨u,ui,ud,path.tail ⟨ilt,k,jEq.symm,mem⟩⟩

theorem lineReaches {P L k q : ℕ} {S : Fin L → Finset (Fin P)} {C : Circuit}
    (mono : IsMonotoneCircuit C) (test : LineTests P L k S C)
    (hK : 1 ≤ k) (hQ : 2 ≤ q) (same : ∀ w, (S w).card = q)
    (notCommon : ∀ (w : Fin L) (p : Fin P), p ∈ S w → ∃ u : Fin L, p ∉ S u)
    (w : Fin L) :
    Relation.ReflTransGen (liveRel (P+L) C) (P+w.val) C.output := by
  obtain ⟨x,zero,one⟩ := lineEssential mono test hK hQ same notCommon w
  let a := List.ofFn x ++ List.ofFn (fun _ : Fin L => false)
  let b := List.ofFn x ++ List.ofFn (single w)
  have len : a.length=P+L := by simp [a]
  have eqLen : a.length=b.length := by simp [a,b]
  have different : actualWire C a C.output ≠ actualWire C b C.output := by
    change C.eval a ≠ C.eval b
    rw [zero,one]
    decide
  obtain ⟨i,hi,hd,path⟩ := goesBack C a b eqLen C.output different
  have large : P ≤ i := by
    by_contra! small
    apply hd
    simp only [a,b]
    rw [List.getD_append _ _ _ _ (by simpa using small),
        List.getD_append _ _ _ _ (by simpa using small)]
  have low : i-P<L := by omega
  have source : i = P+w.val := by
    let j : Fin L := ⟨i-P,low⟩
    have hc : j=w := by
      by_contra wrong
      apply hd
      simp only [a,b]
      rw [List.getD_append_right _ _ _ _ (by simpa using large),
          List.getD_append_right _ _ _ _ (by simpa using large)]
      simp only [List.length_ofFn]
      rw [ofFn_getD_lt _ _ _ low,ofFn_getD_lt _ _ _ low]
      exact (decide_eq_false wrong).symm
    have vals := congrArg Fin.val hc
    change i-P=w.val at vals
    omega
  simpa only [len,source] using path

end PEqualNP.Outside.L_meta_739

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_739 in
theorem PEqualNP.Outside.L_meta_739 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun _ : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true)))) → ∀ (P2 L2 k2 q2 : ℕ) (S2 : Fin L2 → Finset (Fin P2)) (C2 : PEqualNP.CircuitLowerBounds.Circuit), 1 ≤ k2 → 2 ≤ q2 → (∀ w2 : Fin L2, (S2 w2).card = q2) → (∀ w3 w4 : Fin L2, w3 ≠ w4 → (S2 w3 ∩ S2 w4).card ≤ 1) → (∀ (w5 : Fin L2) (p2 : Fin P2), p2 ∈ S2 w5 → ∃ u2 : Fin L2, p2 ∉ S2 u2) → PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C2 → (∀ g2 ∈ C2.gates, g2.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P2 + L2) (Finset.Ico P2 (P2 + L2)) C2 1 → (∀ (x2 : Fin P2 → Bool) (y2 : Fin L2 → Bool), (Finset.univ.filter (fun u3 : Fin L2 => y2 u3 = true)).card = 1 → (Finset.univ.filter (fun p3 : Fin P2 => x2 p3 = true)).card ≤ k2 → C2.eval (List.ofFn x2 ++ List.ofFn y2) = decide (∃ w6 : Fin L2, y2 w6 = true ∧ ∃ p4 ∈ S2 w6, x2 p4 = true)) → ∀ c2 : ℕ, c2 ≤ k2 → c2 + 1 ≤ q2 → L2 * c2 + L2 ≤ C2.size + 1 := by
  intro L0 TR P L k q S C hK hQ same inter avoid mono fan degree test c hcK hcQ
  obtain ⟨D,small,Dmono,Dfan,Dsem,Ddegree,Dlive⟩ :=
    pruneLive (P+L) C mono fan (Finset.Ico P (P+L))
  have Dtest : LineTests P L k S D := by
    intro x y one few
    rw [Dsem _ (by simp)]
    exact test x y one few
  have Dld : HasLineDegree (P+L) (Finset.Ico P (P+L)) D 1 := by
    unfold HasLineDegree at degree ⊢
    rwa [Ddegree]
  let N : Finset (Fin L) := Finset.univ
  have reads (w : Fin L) : w ∈ N ↔
      Relation.ReflTransGen (liveRel (P+L) D) (P+w.val) D.output := by
    constructor
    · intro _
      exact lineReaches Dmono Dtest hK hQ same avoid w
    · intro _
      exact Finset.mem_univ w
  obtain ⟨E,T,o,Emono,Efan,cost,dec⟩ :=
    TR P L D N Dmono Dfan Dld Dlive reads
  have ecost : E.size + L ≤ D.size + 1 := by simpa [N] using cost
  have bound := boundAfterTransposition L0 hK hQ same inter avoid Dmono Dtest Emono Efan T o dec ecost hcK hcQ
  omega
