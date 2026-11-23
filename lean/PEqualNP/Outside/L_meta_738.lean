import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

inductive Ref where
  | fixed : Bool → Ref
  | wire : ℕ → Ref

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wires (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

theorem wires_app (gs fs : List Gate) (x : List Bool) :
    wires (gs ++ fs) x = wires fs (wires gs x) := by
  simp [wires, List.foldl_append]

theorem wires_len (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wires]
  | cons g gs ih =>
    unfold wires
    rw [List.foldl_cons]
    change (wires gs (step x g)).length = _
    rw [ih]
    simp [step]
    omega

theorem wires_read (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (wires gs (step x g)).getD i false = _
    rw [ih (step x g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

def Ref.valid (p : ℕ) (gs : List Gate) : Ref → Prop
  | .fixed _ => True
  | .wire k => k < p + gs.length

def Ref.value {p : ℕ} (gs : List Gate) (x : Fin p → Bool) : Ref → Bool
  | .fixed b => b
  | .wire k => (wires gs (List.ofFn x)).getD k false

theorem Ref.valid_append {p : ℕ} {gs : List Gate} {r : Ref}
    (h : r.valid p gs) (fs : List Gate) : r.valid p (gs ++ fs) := by
  cases r with
  | fixed => trivial
  | wire k =>
    change k < p + gs.length at h
    simp only [Ref.valid, List.length_append]
    omega

theorem Ref.value_append {p : ℕ} {gs : List Gate} {r : Ref} (h : r.valid p gs)
    (fs : List Gate) (x : Fin p → Bool) : r.value (gs ++ fs) x = r.value gs x := by
  cases r with
  | fixed => rfl
  | wire k =>
    change (wires (gs ++ fs) (List.ofFn x)).getD k false = _
    rw [wires_app]
    apply wires_read
    simpa [Ref.valid, wires_len] using h

def good (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def bop (and : Bool) : GateOp := if and then .and else .or

def combine (and : Bool) (a b : Bool) : Bool := if and then (a && b) else (a || b)

def combineFixed (and f : Bool) (r : Ref) : Ref :=
  if and then (if f then r else .fixed false) else (if f then .fixed true else r)

def emit (p : ℕ) (gs : List Gate) (and : Bool) (a b : Ref) : List Gate × Ref :=
  match a, b with
  | .fixed f, r => (gs, combineFixed and f r)
  | r, .fixed f => (gs, combineFixed and f r)
  | .wire a, .wire b => (gs ++ [⟨bop and, [a,b]⟩], .wire (p + gs.length))

theorem emit_prefix (p : ℕ) (gs : List Gate) (op : Bool) (a b : Ref) :
    ∃ fs, (emit p gs op a b).1 = gs ++ fs := by
  cases a with
  | fixed _ => exact ⟨[], by simp [emit]⟩
  | wire i =>
    cases b with
    | fixed _ => exact ⟨[], by simp [emit]⟩
    | wire j => exact ⟨[⟨bop op, [i, j]⟩], rfl⟩

theorem emit_size (p : ℕ) (gs : List Gate) (op : Bool) (a b : Ref) :
    (emit p gs op a b).1.length ≤ gs.length + 1 := by
  cases a <;> cases b <;> simp [emit]

theorem emit_and_true (p : ℕ) (gs : List Gate) (a : Ref) :
    emit p gs true a (.fixed true) = (gs, a) := by
  cases a with
  | fixed b => cases b <;> rfl
  | wire k => rfl

theorem emit_good {p : ℕ} {gs : List Gate} (h : good gs) (op : Bool) (a b : Ref) :
    good (emit p gs op a b).1 := by
  cases a <;> cases b
  all_goals try exact h
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h g hg
  · rw [List.mem_singleton] at hg
    subst g
    cases op <;> simp [bop]

theorem emit_valid {p : ℕ} {gs : List Gate} (op : Bool) {a b : Ref}
    (ha : a.valid p gs) (hb : b.valid p gs) :
    (emit p gs op a b).2.valid p (emit p gs op a b).1 := by
  cases a with
  | fixed f => cases op <;> cases f <;> first | exact hb | trivial
  | wire a =>
    cases b with
    | fixed f => cases op <;> cases f <;> first | exact ha | trivial
    | wire b => simp [emit, Ref.valid]

theorem emit_value {p : ℕ} {gs : List Gate} (op : Bool) {a b : Ref}
    (ha : a.valid p gs) (hb : b.valid p gs) (x : Fin p → Bool) :
    (emit p gs op a b).2.value (emit p gs op a b).1 x =
      combine op (a.value gs x) (b.value gs x) := by
  cases a with
  | fixed f => cases f <;> cases op <;> simp [emit, Ref.value, combineFixed, combine]
  | wire i =>
    cases b with
    | fixed f => cases f <;> cases op <;> simp [emit, Ref.value, combineFixed, combine]
    | wire j =>
      let w := wires gs (List.ofFn x)
      have length : w.length = p + gs.length := by simp [w, wires_len]
      change (wires (gs ++ [⟨bop op,[i,j]⟩]) (List.ofFn x)).getD (p+gs.length) false = _
      rw [wires_app, ← length]
      change (w ++ [(bop op).eval [w.getD i false,w.getD j false]]).getD w.length false = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
      cases op <;> simp [bop, combine, GateOp.eval, Ref.value, w]

end PEqualNP.Outside.L_meta_738_aux


namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

def Extends (gs fs : List Gate) : Prop := ∃ tail, fs = gs ++ tail

theorem extends_trans {gs fs ks : List Gate} (h : Extends gs fs) (j : Extends fs ks) : Extends gs ks := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, rfl⟩ := j
  exact ⟨a ++ b, List.append_assoc ..⟩

theorem valid_extend {p : ℕ} {gs fs : List Gate} {r : Ref}
    (h : Extends gs fs) (hr : r.valid p gs) : r.valid p fs := by
  obtain ⟨tail, rfl⟩ := h
  exact Ref.valid_append hr tail

theorem value_extend {p : ℕ} {gs fs : List Gate} {r : Ref}
    (h : Extends gs fs) (hr : r.valid p gs) (x : Fin p → Bool) : r.value fs x = r.value gs x := by
  obtain ⟨tail, rfl⟩ := h
  exact Ref.value_append hr tail x

structure Accumulator (p : ℕ) where
  gs : List Gate
  seen : Finset ℕ
  refs : ℕ → Ref
  wellFormed : good gs
  validRefs : ∀ v, (refs v).valid p gs

def ctx {p : ℕ} (s : Accumulator p) (v : ℕ) : Ref :=
  if v ∈ s.seen then s.refs v else .fixed false

def cost {p : ℕ} (s : Accumulator p) : ℕ := s.gs.length + s.seen.card

theorem ctx_valid {p : ℕ} (s : Accumulator p) (v : ℕ) : (ctx s v).valid p s.gs := by
  unfold ctx
  split
  · exact s.validRefs v
  · trivial

theorem merge {p : ℕ} (s : Accumulator p) (v : ℕ) (r : Ref) (hr : r.valid p s.gs) :
    ∃ t : Accumulator p, Extends s.gs t.gs ∧ t.seen = insert v s.seen ∧ cost t ≤ cost s + 1 ∧
      ∀ (x : Fin p → Bool) w, (ctx t w).value t.gs x =
        ((ctx s w).value s.gs x || if w = v then r.value s.gs x else false) := by
  let g := emit p s.gs false (ctx s v) r
  have ext : Extends s.gs g.1 := emit_prefix p s.gs false (ctx s v) r
  have valid : ∀ w, (Function.update s.refs v g.2 w).valid p g.1 := by
    intro w
    by_cases eq : w = v
    · subst w
      simpa only [Function.update_self] using emit_valid false (ctx_valid s v) hr
    · rw [Function.update_of_ne eq]
      exact valid_extend ext (s.validRefs w)
  let t : Accumulator p := ⟨g.1, insert v s.seen, Function.update s.refs v g.2,
    emit_good s.wellFormed false (ctx s v) r, valid⟩
  refine ⟨t, ext, rfl, ?_, ?_⟩
  · change g.1.length + (insert v s.seen).card ≤ s.gs.length + s.seen.card + 1
    by_cases h : v ∈ s.seen
    · rw [Finset.insert_eq_of_mem h]
      have size := emit_size p s.gs false (ctx s v) r
      change g.1.length ≤ s.gs.length + 1 at size
      omega
    · rw [Finset.card_insert_of_notMem h]
      cases r <;> simp [g, ctx, h, emit, combineFixed, Nat.add_assoc]
  · intro x w
    by_cases eq : w = v
    · subst w
      have e : ctx t v = g.2 := by simp [ctx, t]
      rw [e, ite_eq_left rfl]
      exact emit_value false (ctx_valid s v) hr x
    · have e : ctx t w = ctx s w := by
        simp [ctx, t, eq, Function.update_of_ne]
      rw [e, ite_eq_right eq, Bool.or_false]
      exact value_extend ext (ctx_valid s w) x

def factorCost : Ref → ℕ
  | .fixed true => 0
  | _ => 1

def portCost (port : ℕ × Ref) : ℕ := factorCost port.2 + 1

theorem send_one {p : ℕ} (s : Accumulator p) (src : Ref) (port : ℕ × Ref)
    (hs : src.valid p s.gs) (hp : port.2.valid p s.gs) :
    ∃ t : Accumulator p, Extends s.gs t.gs ∧ t.seen = insert port.1 s.seen ∧
      cost t ≤ cost s + portCost port ∧
      ∀ (x : Fin p → Bool) w, (ctx t w).value t.gs x = ((ctx s w).value s.gs x ||
        if w = port.1 then (src.value s.gs x && port.2.value s.gs x) else false) := by
  let g := emit p s.gs true src port.2
  have ext : Extends s.gs g.1 := emit_prefix p s.gs true src port.2
  let fresh : Accumulator p := ⟨g.1, s.seen, s.refs, emit_good s.wellFormed true src port.2,
    fun w => valid_extend ext (s.validRefs w)⟩
  have freshSize : g.1.length ≤ s.gs.length + factorCost port.2 := by
    rcases port with ⟨v, r⟩
    cases r with
    | fixed b =>
      cases b
      · exact emit_size _ _ _ _ _
      · simp [g, factorCost, emit_and_true]
    | wire => exact emit_size _ _ _ _ _
  obtain ⟨t, ext', seen, size, values⟩ := merge fresh port.1 g.2 (emit_valid true hs hp)
  refine ⟨t, extends_trans ext ext', seen, ?_, ?_⟩
  · change t.gs.length + t.seen.card ≤ s.gs.length + s.seen.card + (factorCost port.2 + 1)
    change t.gs.length + t.seen.card ≤ g.1.length + s.seen.card + 1 at size
    omega
  · intro x w
    rw [values]
    have same : ctx fresh w = ctx s w := rfl
    rw [same, value_extend ext (ctx_valid s w) x]
    rw [show g.2.value fresh.gs x = (src.value s.gs x && port.2.value s.gs x) from
      emit_value true hs hp x]

def matching {p : ℕ} (gs : List Gate) (x : Fin p → Bool) (w : ℕ) (ports : List (ℕ × Ref)) : Bool :=
  ports.any (fun q => decide (w = q.1) && q.2.value gs x)

theorem matching_extend {p : ℕ} {gs fs : List Gate} (ext : Extends gs fs)
    (ports : List (ℕ × Ref)) (h : ∀ q ∈ ports, q.2.valid p gs) (x : Fin p → Bool) (w : ℕ) :
    matching fs x w ports = matching gs x w ports := by
  induction ports with
  | nil => rfl
  | cons q rest ih =>
    simp only [matching, List.any_cons]
    rw [value_extend ext (h q List.mem_cons_self) x]
    exact congrArg _ (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

theorem send_many {p : ℕ} (s : Accumulator p) (src : Ref) (ports : List (ℕ × Ref))
    (hs : src.valid p s.gs) (hp : ∀ q ∈ ports, q.2.valid p s.gs) :
    ∃ t : Accumulator p, Extends s.gs t.gs ∧ t.seen = s.seen ∪ (ports.map Prod.fst).toFinset ∧
      cost t ≤ cost s + (ports.map portCost).sum ∧
      ∀ (x : Fin p → Bool) w, (ctx t w).value t.gs x =
        ((ctx s w).value s.gs x || (src.value s.gs x && matching s.gs x w ports)) := by
  induction ports generalizing s with
  | nil => exact ⟨s, ⟨[], by simp⟩, by simp, by simp, by simp [matching]⟩
  | cons port ports ih =>
    obtain ⟨t, ext, tSeen, tSize, tValues⟩ := send_one s src port hs (hp port List.mem_cons_self)
    have restValid : ∀ q ∈ ports, q.2.valid p s.gs := fun q hq => hp q (List.mem_cons_of_mem _ hq)
    obtain ⟨u, ext', uSeen, uSize, uValues⟩ := ih t (valid_extend ext hs)
      (fun q hq => valid_extend ext (restValid q hq))
    refine ⟨u, extends_trans ext ext', ?_, ?_, ?_⟩
    · rw [uSeen, tSeen]
      ext w
      simp
    · simp only [List.map_cons, List.sum_cons]
      omega
    · intro x w
      rw [uValues, tValues, value_extend ext hs x, matching_extend ext ports restValid x w]
      by_cases h : w = port.1
      · simp only [h, ite_true, matching, List.any_cons, decide_true, Bool.true_and]
        cases (ctx s port.1).value s.gs x <;> cases src.value s.gs x <;>
          cases port.2.value s.gs x <;>
          cases ports.any (fun q => decide (port.1 = q.1) && q.2.value s.gs x) <;> rfl
      · simp [h, matching]

end PEqualNP.Outside.L_meta_738_aux


namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

structure Network (p : ℕ) (Y : Type*) where
  pointProgram : List Gate
  start : ℕ
  markedInputs : Finset ℕ
  markedGates : Finset ℕ
  ports : ℕ → List (ℕ × Ref)
  residual : ℕ → (Fin p → Bool) → Prop
  original : ℕ → (Fin p → Bool) → Y → Bool
  below : ∀ j ∈ markedGates, ∀ a ∈ ports j, a.1 < j
  inputBelow : ∀ v ∈ markedInputs, v < start
  markedChild : ∀ j ∈ markedGates, ∀ a ∈ ports j, a.1 ∈ markedInputs ∨ a.1 ∈ markedGates
  present : ∀ j ∈ markedGates, ∀ a ∈ ports j, a.2.valid p pointProgram
  budget : ∀ j ∈ markedGates, ((ports j).map portCost).sum ≤ 2
  description : ∀ j ∈ markedGates, ∀ x y, original j x y = true ↔
    residual j x ∨ ∃ a ∈ ports j, a.2.value pointProgram x = true ∧ original a.1 x y = true

def allowed {p : ℕ} {Y : Type*} (m : Network p Y) (s : Accumulator p) : Prop :=
  ∀ j ∈ s.seen, j ∈ m.markedInputs ∨ j ∈ m.markedGates

def closedAbove {p : ℕ} {Y : Type*} (m : Network p Y) (s : Accumulator p) (n : ℕ) : Prop :=
  ∀ j ∈ s.seen, n ≤ j → j ∈ m.markedGates → ∀ a ∈ m.ports j, a.1 ∈ s.seen

def frontier {p : ℕ} {Y : Type*} (m : Network p Y) (s : Accumulator p)
    (cut : ℕ) (x : Fin p → Bool) (y : Y) : Prop :=
  ∃ v < cut, (ctx s v).value s.gs x = true ∧ m.original v x y = true

theorem frontier_succ {p : ℕ} {Y : Type*} (m : Network p Y) (s : Accumulator p)
    (j : ℕ) (x : Fin p → Bool) (y : Y) :
    frontier m s (j+1) x y ↔ frontier m s j x y ∨
      ((ctx s j).value s.gs x = true ∧ m.original j x y = true) := by
  constructor
  · rintro ⟨v, hv, he⟩
    by_cases h : v = j
    · exact Or.inr (h ▸ he)
    · exact Or.inl ⟨v, by omega, he⟩
  · rintro (⟨v, hv, he⟩ | he)
    · exact ⟨v, by omega, he⟩
    · exact ⟨j, by omega, he⟩

theorem frontier_send {p : ℕ} {Y : Type*} (m : Network p Y) (s t : Accumulator p)
    (j : ℕ) (x : Fin p → Bool) (y : Y) (src : Ref) (ports : List (ℕ × Ref))
    (earlier : ∀ a ∈ ports, a.1 < j)
    (values : ∀ (x : Fin p → Bool) w, (ctx t w).value t.gs x =
      ((ctx s w).value s.gs x || (src.value s.gs x && matching s.gs x w ports))) :
    frontier m t j x y ↔ frontier m s j x y ∨ (src.value s.gs x = true ∧
      ∃ a ∈ ports, a.2.value s.gs x = true ∧ m.original a.1 x y = true) := by
  constructor
  · rintro ⟨v, hv, hr, hval⟩
    rw [values, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact Or.inl ⟨v, hv, hr, hval⟩
    · rw [Bool.and_eq_true] at hr
      obtain ⟨a, ha, hbit⟩ := List.any_eq_true.mp hr.2
      rw [Bool.and_eq_true, decide_eq_true_eq] at hbit
      exact Or.inr ⟨hr.1, a, ha, hbit.2, hbit.1 ▸ hval⟩
  · rintro (⟨v, hv, hr, hval⟩ | ⟨hs, a, ha, hf, hval⟩)
    · exact ⟨v, hv, by rw [values, Bool.or_eq_true]; exact Or.inl hr, hval⟩
    · refine ⟨a.1, earlier a ha, ?_, hval⟩
      rw [values, Bool.or_eq_true, Bool.and_eq_true]
      exact Or.inr ⟨hs, List.any_eq_true.mpr ⟨a, ha, by simp [hf]⟩⟩

theorem reverse_step {p : ℕ} {Y : Type*} (m : Network p Y) (j : ℕ) (R : (Fin p → Bool) → Prop)
    (s : Accumulator p) (ext : Extends m.pointProgram s.gs) (hstart : m.start ≤ j)
    (live : allowed m s) (closed : closedAbove m s (j+1)) :
    ∃ (t : Accumulator p) (R' : (Fin p → Bool) → Prop), Extends s.gs t.gs ∧
      s.seen ⊆ t.seen ∧ cost t ≤ cost s + (if j ∈ m.markedGates then 2 else 0) ∧
      allowed m t ∧ closedAbove m t j ∧
      ∀ x y, (R x ∨ frontier m s (j+1) x y) ↔ (R' x ∨ frontier m t j x y) := by
  by_cases h : j ∈ s.seen
  · have hj : j ∈ m.markedGates := (live j h).resolve_left fun hj => Nat.not_lt_of_ge hstart (m.inputBelow j hj)
    obtain ⟨t, ext', tSeen, tSize, tValues⟩ := send_many s (ctx s j) (m.ports j) (ctx_valid s j)
      (fun a ha => valid_extend ext (m.present j hj a ha))
    have hOld : s.seen ⊆ t.seen := by rw [tSeen]; exact Finset.subset_union_left
    have hChild (a : ℕ × Ref) (ha : a ∈ m.ports j) : a.1 ∈ t.seen := by
      rw [tSeen]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map_of_mem ha))
    refine ⟨t, fun x => R x ∨ ((ctx s j).value s.gs x = true ∧ m.residual j x),
      ext', hOld, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_left hj]
      exact tSize.trans (Nat.add_le_add_left (m.budget j hj) _)
    · intro v hv
      rw [tSeen, Finset.mem_union] at hv
      rcases hv with hv | hv
      · exact live v hv
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
        exact m.markedChild j hj a ha
    · intro v hv hle hvMark a ha
      by_cases eq : v = j
      · subst v
        exact hChild a ha
      · have old : v ∈ s.seen := by
          rw [tSeen, Finset.mem_union] at hv
          rcases hv with hv | hv
          · exact hv
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
            exact (Nat.not_lt_of_ge hle (m.below j hj q hq)).elim
        exact hOld (closed v old (by omega) hvMark a ha)
    · intro x y
      rw [frontier_succ, m.description j hj x y,
        frontier_send m s t j x y (ctx s j) (m.ports j) (m.below j hj) tValues]
      have equals (a : ℕ × Ref) (ha : a ∈ m.ports j) :
          a.2.value s.gs x = a.2.value m.pointProgram x := value_extend ext (m.present j hj a ha) x
      have hpos : (∃ a ∈ m.ports j, a.2.value s.gs x = true ∧ m.original a.1 x y = true) ↔
          (∃ a ∈ m.ports j, a.2.value m.pointProgram x = true ∧ m.original a.1 x y = true) := by
        constructor <;> rintro ⟨a, ha, hbit, horig⟩
        · exact ⟨a, ha, (equals a ha).symm.trans hbit, horig⟩
        · exact ⟨a, ha, (equals a ha).trans hbit, horig⟩
      rw [hpos]
      tauto
  · refine ⟨s, R, ⟨[], by simp⟩, Finset.Subset.refl _, by omega, live, ?_, ?_⟩
    · intro v hv hle hvMark a ha
      have different : v ≠ j := fun e => h (e ▸ hv)
      exact closed v hv (by omega) hvMark a ha
    · intro x y
      rw [frontier_succ]
      simp [ctx, h, Ref.value]

theorem remove_marked {p : ℕ} {Y : Type*} (m : Network p Y) (k : ℕ)
    (R : (Fin p → Bool) → Prop) (s : Accumulator p) (ext : Extends m.pointProgram s.gs)
    (live : allowed m s) (closed : closedAbove m s (m.start+k)) :
    ∃ (t : Accumulator p) (R' : (Fin p → Bool) → Prop), Extends s.gs t.gs ∧
      s.seen ⊆ t.seen ∧ cost t ≤ cost s + 2 * (m.markedGates.filter (fun j => j < m.start+k)).card ∧
      allowed m t ∧ closedAbove m t m.start ∧
      ∀ x y, (R x ∨ frontier m s (m.start+k) x y) ↔ (R' x ∨ frontier m t m.start x y) := by
  induction k generalizing R s with
  | zero => exact ⟨s, R, ⟨[], by simp⟩, Finset.Subset.refl _, by omega, live,
      by simpa using closed, by simp⟩
  | succ k ih =>
    let j := m.start+k
    obtain ⟨s', R', ext', hsub, hsize, hlive, hclosed, hval⟩ := reverse_step m j R s ext
      (by dsimp [j]; omega) live (by simpa [j, Nat.add_assoc] using closed)
    obtain ⟨t, R'', ext'', hsub', hsize', ht, hclosed', hval'⟩ :=
      ih R' s' (extends_trans ext ext') hlive hclosed
    refine ⟨t, R'', extends_trans ext' ext'', hsub.trans hsub', ?_, ht, hclosed', ?_⟩
    · have hFilter : m.markedGates.filter (fun w => w < m.start+(k+1)) =
          if j ∈ m.markedGates then insert j (m.markedGates.filter (fun w => w < j))
          else m.markedGates.filter (fun w => w < j) := by
        ext w
        by_cases hJ : j ∈ m.markedGates <;> by_cases e : w = j
        · subst w; simp [j, hJ]
        · have ord : w < m.start+(k+1) ↔ w < j := by
            dsimp [j] at e ⊢
            omega
          simp [hJ, e, ord]
        · subst w; simp [j, hJ]
        · have ord : w < m.start+(k+1) ↔ w < j := by
            dsimp [j] at e ⊢
            omega
          simp [hJ, ord]
      have noMember : j ∉ m.markedGates.filter (fun w => w < j) := by simp
      change cost t ≤ cost s + 2 * (m.markedGates.filter (fun w => w < m.start+(k+1))).card
      rw [hFilter]
      by_cases hJ : j ∈ m.markedGates
      · rw [ite_eq_left hJ, Finset.card_insert_of_notMem noMember]
        rw [ite_eq_left hJ] at hsize
        change cost t ≤ cost s' + 2 * (m.markedGates.filter (fun w => w < j)).card at hsize'
        omega
      · rw [ite_eq_right hJ]
        rw [ite_eq_right hJ] at hsize
        change cost t ≤ cost s' + 2 * (m.markedGates.filter (fun w => w < j)).card at hsize'
        omega
    · intro x y
      exact (by simpa [j, Nat.add_assoc] using hval x y :
        (R x ∨ frontier m s (m.start+k.succ) x y) ↔ (R' x ∨ frontier m s' j x y)).trans (hval' x y)

end PEqualNP.Outside.L_meta_738_aux


namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

def foldGate {A : Type*} (f : List A → Gate → A) (gs : List Gate) (w : List A) : List A :=
  gs.foldl (fun v g => v ++ [f v g]) w

theorem fold_len {A : Type*} (f : List A → Gate → A) (gs : List Gate) (w : List A) :
    (foldGate f gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [foldGate]
  | cons g gs ih =>
    change (foldGate f gs (w ++ [f w g])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem fold_read {A : Type*} (f : List A → Gate → A) (gs : List Gate) (w : List A)
    (a : A) (i : ℕ) (h : i < w.length) : (foldGate f gs w).getD i a = w.getD i a := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (foldGate f gs (w ++ [f w g])).getD i a = _
    rw [ih (w ++ [f w g]) (by simp; omega)]
    exact List.getD_append _ _ _ _ h

theorem fold_step {A : Type*} (f : List A → Gate → A) (gs : List Gate) (w : List A)
    (a : A) (j : Fin gs.length) :
    let pre := foldGate f (gs.take j.val) w
    (foldGate f gs w).getD (w.length+j.val) a = f pre (gs.get j) ∧
    ∀ i, pre.getD i a = if i < w.length+j.val then (foldGate f gs w).getD i a else a := by
  let pre := foldGate f (gs.take j.val) w
  let v := f pre (gs.get j)
  have cut : gs = gs.take j.val ++ gs.get j :: gs.drop (j.val+1) := by
    have h := List.take_append_drop j.val gs
    rw [List.drop_eq_getElem_cons j.isLt] at h
    exact h.symm
  have full : foldGate f gs w = foldGate f (gs.drop (j.val+1)) (pre ++ [v]) := by
    unfold foldGate
    conv_lhs => rw [cut, List.foldl_append]
    rfl
  have plen : pre.length = w.length+j.val := by
    rw [show pre = foldGate f (gs.take j.val) w from rfl, fold_len, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  change (foldGate f gs w).getD (w.length+j.val) a = v ∧
    ∀ i, pre.getD i a = if i < w.length+j.val then (foldGate f gs w).getD i a else a
  constructor
  · rw [full, fold_read f _ _ _ _ (by simp [plen]), ← plen,
      List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
    simp
  · intro i
    by_cases h : i < w.length+j.val
    · have hpre : i < pre.length := by omega
      have hall : i < (pre ++ [v]).length := by simp; omega
      rw [ite_eq_left h, full, fold_read f (gs.drop (j.val+1)) (pre ++ [v]) a i hall,
        List.getD_append pre [v] a i hpre]
    · rw [ite_eq_right h, List.getD_eq_default _ _ (by omega)]

def marks (p l : ℕ) : Finset ℕ := Finset.Ico p (p+l)

def degree (C : Circuit) (p l i : ℕ) : ℕ :=
  (C.lineDegrees (p+l) (marks p l)).getD i 0

def orig (C : Circuit) {p l : ℕ} (i : ℕ) (x : Fin p → Bool) (y : Fin l → Bool) : Bool :=
  (C.wires (List.ofFn x ++ List.ofFn y)).getD i false

def guard {A : Type*} (f : ℕ → A) (a : A) (b i : ℕ) : A := if i < b then f i else a

def Reads (C : Circuit) (p l a b : ℕ) : Prop :=
  a < b ∧ ∃ j : Fin C.gates.length, b = p+l+j.val ∧ a ∈ (C.gates.get j).inputs

theorem degree_gate (C : Circuit) (p l : ℕ) (j : Fin C.gates.length) :
    letI : DecidableEq GateOp := lineDegreeGateOpDecEq
    degree C p l (p+l+j.val) =
      if (C.gates.get j).op = GateOp.and then
        ((C.gates.get j).inputs.map (guard (degree C p l) 0 (p+l+j.val))).sum
      else ((C.gates.get j).inputs.map (guard (degree C p l) 0 (p+l+j.val))).foldr max 0 := by
  let d := (List.range (p+l)).map (fun i => if i ∈ marks p l then (1 : ℕ) else 0)
  have dl : d.length = p+l := by simp [d]
  have hs := fold_step (fun w g => g.lineDegree w) C.gates d 0 j
  simp only [dl] at hs
  change (foldGate (fun w g => g.lineDegree w) C.gates d).getD (p+l+j.val) 0 = _
  rw [hs.1]
  have he : (C.gates.get j).inputs.map (fun i =>
      (foldGate (fun w g => g.lineDegree w) (C.gates.take j.val) d).getD i 0) =
      (C.gates.get j).inputs.map (guard (degree C p l) 0 (p+l+j.val)) :=
    List.map_congr_left (fun i _ => hs.2 i)
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  let f (values : List ℕ) := if (C.gates.get j).op = GateOp.and then values.sum else values.foldr max 0
  change f _ = f _
  exact congrArg f he

theorem orig_gate (C : Circuit) {p l : ℕ} (j : Fin C.gates.length)
    (x : Fin p → Bool) (y : Fin l → Bool) :
    orig C (p+l+j.val) x y = (C.gates.get j).op.eval ((C.gates.get j).inputs.map
      (guard (fun i => orig C i x y) false (p+l+j.val))) := by
  let d := List.ofFn x ++ List.ofFn y
  let f := fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false)
  have dl : d.length = p+l := by simp [d]
  have hs := fold_step f C.gates d false j
  simp only [dl] at hs
  change (foldGate f C.gates d).getD (p+l+j.val) false = _
  rw [hs.1]
  exact congrArg (C.gates.get j).op.eval (List.map_congr_left (fun i _ => hs.2 i))

theorem input_degree (C : Circuit) (p l i : ℕ) (h : i < p+l) :
    degree C p l i = if p ≤ i then 1 else 0 := by
  let d := (List.range (p+l)).map (fun q => if q ∈ marks p l then (1 : ℕ) else 0)
  change (foldGate (fun w g => g.lineDegree w) C.gates d).getD i 0 = _
  rw [fold_read _ _ _ _ _ (by simpa [d] using h)]
  simp [d, List.getD_eq_getElem?_getD, h, marks]

theorem outside_degree (C : Circuit) (p l i : ℕ) (h : p+l+C.gates.length ≤ i) :
    degree C p l i = 0 := by
  let d := (List.range (p+l)).map (fun q => if q ∈ marks p l then (1 : ℕ) else 0)
  change (foldGate (fun w g => g.lineDegree w) C.gates d).getD i 0 = _
  apply List.getD_eq_default
  simpa [fold_len, d] using h

theorem le_sum {a : ℕ} {ds : List ℕ} (h : a ∈ ds) : a ≤ ds.sum := by
  induction ds with
  | nil => simp at h
  | cons b ds ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h
      omega

theorem le_maximum {a : ℕ} {ds : List ℕ} (h : a ∈ ds) : a ≤ ds.foldr max 0 := by
  induction ds with
  | nil => simp at h
  | cons b ds ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem operand_degree (C : Circuit) (p l : ℕ) (j : Fin C.gates.length) (i : ℕ)
    (h : i ∈ (C.gates.get j).inputs) :
    guard (degree C p l) 0 (p+l+j.val) i ≤ degree C p l (p+l+j.val) := by
  rw [degree_gate]
  split
  · exact le_sum (List.mem_map_of_mem h)
  · exact le_maximum (List.mem_map_of_mem h)

theorem reads_degree {C : Circuit} {p l a b : ℕ} (h : Reads C p l a b) :
    degree C p l a ≤ degree C p l b := by
  obtain ⟨lt, j, rfl, hm⟩ := h
  simpa [guard, lt] using operand_degree C p l j a hm

theorem path_degree {C : Circuit} {p l a b : ℕ}
    (h : Relation.ReflTransGen (Reads C p l) a b) : degree C p l a ≤ degree C p l b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (reads_degree hstep)

end PEqualNP.Outside.L_meta_738_aux


namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

theorem orig_point (C : Circuit) {p l : ℕ} (i : Fin p) (x : Fin p → Bool) (y : Fin l → Bool) :
    orig C i.val x y = x i := by
  change (wires C.gates (List.ofFn x ++ List.ofFn y)).getD i.val false = _
  rw [wires_read _ _ _ (by simp <;> omega), List.getD_append _ _ _ _ (by simp)]
  simp

theorem orig_line (C : Circuit) {p l : ℕ} (i : Fin l) (x : Fin p → Bool) (y : Fin l → Bool) :
    orig C (p+i.val) x y = y i := by
  change (wires C.gates (List.ofFn x ++ List.ofFn y)).getD (p+i.val) false = _
  rw [wires_read _ _ _ (by simp <;> omega), List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem emit_gate {p : ℕ} (gs : List Gate) (hg : good gs) (op : GateOp) (args : List Ref)
    (hop : op = .and ∨ op = .or) (hsmall : args.length ≤ 2)
    (hargs : ∀ a ∈ args, a.valid p gs) :
    ∃ (fs : List Gate) (r : Ref), Extends gs fs ∧ good fs ∧ fs.length ≤ gs.length+1 ∧
      r.valid p fs ∧ ∀ (x : Fin p → Bool), r.value fs x = op.eval (args.map (Ref.value gs x)) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact ⟨gs, .fixed (op.eval []), ⟨[], by simp⟩, hg, by omega, trivial, by simp [Ref.value]⟩
  · exact ⟨gs, a, ⟨[], by simp⟩, hg, by omega, hargs a (by simp),
      fun _ => by rcases hop with rfl | rfl <;> simp [GateOp.eval]⟩
  · have ha := hargs a (by simp)
    have hb := hargs b (by simp)
    rcases hop with rfl | rfl
    · exact ⟨_, _, emit_prefix p gs true a b, emit_good hg true a b, emit_size p gs true a b,
        emit_valid true ha hb, fun x => by simpa [combine, GateOp.eval] using emit_value true ha hb x⟩
    · exact ⟨_, _, emit_prefix p gs false a b, emit_good hg false a b, emit_size p gs false a b,
        emit_valid false ha hb, fun x => by simpa [combine, GateOp.eval] using emit_value false ha hb x⟩
  · simp only [List.length_cons] at hsmall
    omega

def PointRep (C : Circuit) (p l cut : ℕ) (gs : List Gate) (r : ℕ → Ref) : Prop :=
  ∀ i < cut, degree C p l i = 0 → (r i).valid p gs ∧
    ∀ (x : Fin p → Bool) (y : Fin l → Bool), (r i).value gs x = orig C i x y

def pointGates (C : Circuit) (p l t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun j => degree C p l (p+l+j) = 0)

theorem compile_points (C : Circuit) (p l : ℕ) (mono : IsMonotoneCircuit C)
    (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (t : ℕ) (ht : t ≤ C.gates.length) :
    ∃ (gs : List Gate) (r : ℕ → Ref), good gs ∧ gs.length ≤ (pointGates C p l t).card ∧
      PointRep C p l (p+l+t) gs r := by
  induction t with
  | zero =>
    refine ⟨[], Ref.wire, by simp [good], by simp, ?_⟩
    intro i hlt hdeg
    have hi : i < p+l := by omega
    have hpoint : i < p := by
      rw [input_degree C p l i hi] at hdeg
      by_contra! h
      simp [h] at hdeg
    have hvalue (x : Fin p → Bool) : (Ref.wire i).value [] x = x ⟨i,hpoint⟩ := by
      simp [Ref.value, wires, List.getD_eq_getElem?_getD, hpoint]
    exact ⟨by simpa [Ref.valid] using hpoint, fun x y => (hvalue x).trans (orig_point C ⟨i,hpoint⟩ x y).symm⟩
  | succ t ih =>
    obtain ⟨gs, r, hGood, hSize, hRep⟩ := ih (by omega)
    let j : Fin C.gates.length := ⟨t, by omega⟩
    let v := p+l+t
    let g := C.gates.get j
    have hg : g ∈ C.gates := List.get_mem _ _
    have budget : pointGates C p l (t+1) =
        if degree C p l v = 0 then insert t (pointGates C p l t) else pointGates C p l t := by
      have extended : Finset.range (t+1) = insert t (Finset.range t) := by
        ext q
        simp only [Finset.mem_range, Finset.mem_insert]
        omega
      rw [show pointGates C p l (t+1) = (insert t (Finset.range t)).filter
        (fun j => degree C p l (p+l+j) = 0) by rw [pointGates, extended]]
      rw [Finset.filter_insert]
      rfl
    by_cases hzero : degree C p l v = 0
    · let f (i : ℕ) := guard r (.fixed false) v i
      have h(z : ℕ) (hz : z ∈ g.inputs) : (f z).valid p gs ∧
          ∀ (x : Fin p → Bool) (y : Fin l → Bool), (f z).value gs x =
            guard (fun a => orig C a x y) false v z := by
        by_cases hlt : z < v
        · have hdeg := operand_degree C p l j z hz
          change guard (degree C p l) 0 v z ≤ degree C p l v at hdeg
          rw [hzero] at hdeg
          simp [guard, hlt] at hdeg
          simpa [f, guard, hlt] using hRep z hlt hdeg
        · simp [f, guard, hlt, Ref.valid, Ref.value]
      obtain ⟨fs, a, ext, fsGood, fsSize, aValid, aValue⟩ :=
        emit_gate gs hGood g.op (g.inputs.map f) (mono g hg) (by simpa using arity g hg)
          (by intro a ha; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha; exact (h z hz).1)
      refine ⟨fs, Function.update r v a, fsGood, ?_, ?_⟩
      · rw [budget, ite_eq_left hzero, Finset.card_insert_of_notMem (by simp [pointGates])]
        omega
      · intro i hi hdeg
        by_cases eq : i = v
        · subst i
          rw [Function.update_self]
          refine ⟨aValid, fun x y => ?_⟩
          rw [aValue x, List.map_map]
          change _ = orig C (p+l+j.val) x y
          rw [orig_gate C j]
          exact congrArg g.op.eval (List.map_congr_left (fun z hz => (h z hz).2 x y))
        · have hilt : i < v := by dsimp [v] at eq ⊢; omega
          obtain ⟨old, eval⟩ := hRep i hilt hdeg
          rw [Function.update_of_ne eq]
          exact ⟨valid_extend ext old, fun x y => (value_extend ext old x).trans (eval x y)⟩
    · refine ⟨gs, r, hGood, ?_, ?_⟩
      · rw [budget, ite_eq_right hzero]
        exact hSize
      · intro i hi hdeg
        have ine : i ≠ v := fun e => hzero (e ▸ hdeg)
        exact hRep i (by dsimp [v] at ine ⊢; omega) hdeg

end PEqualNP.Outside.L_meta_738_aux


namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

def markedWires (C : Circuit) (p l : ℕ) : Finset ℕ :=
  (Finset.Ico (p+l) (p+l+C.gates.length)).filter (fun i => degree C p l i = 1)

theorem marker {C : Circuit} {p l i v : ℕ} (hv : v ≤ p+l+C.gates.length)
    (hi : guard (degree C p l) 0 v i = 1) :
    i < v ∧ (i < p+l ∨ i ∈ markedWires C p l) := by
  have ilt : i < v := by
    by_contra! h
    simp [guard, Nat.not_lt_of_ge h] at hi
  refine ⟨ilt, ?_⟩
  by_cases hin : i < p+l
  · exact Or.inl hin
  · exact Or.inr (by simp [markedWires, Finset.mem_Ico, Nat.le_of_not_gt hin,
      ilt.trans_le hv, guard, ilt] at hi ⊢; exact hi)

theorem point_factor {C : Circuit} {p l cut gate : ℕ} {gs : List Gate} {r : ℕ → Ref}
    (h : PointRep C p l cut gs r) (hg : gate ≤ cut) (i : ℕ)
    (hi : guard (degree C p l) 0 gate i = 0) :
    (guard r (.fixed false) gate i).valid p gs ∧ ∀ (x : Fin p → Bool) (y : Fin l → Bool),
      (guard r (.fixed false) gate i).value gs x = guard (fun k => orig C k x y) false gate i := by
  by_cases ilt : i < gate
  · have d : degree C p l i = 0 := by simpa [guard, ilt] using hi
    simpa [guard, ilt] using h i (ilt.trans_le hg) d
  · simp [guard, ilt, Ref.valid, Ref.value]

structure GatePorts (C : Circuit) (p l : ℕ) (gs : List Gate) (j : Fin C.gates.length) where
  data : List (ℕ × Ref)
  default : (Fin p → Bool) → Prop
  children : ∀ a ∈ data, a.1 < p+l+j.val ∧ (a.1 < p+l ∨ a.1 ∈ markedWires C p l)
  valid : ∀ a ∈ data, a.2.valid p gs
  budget : (data.map portCost).sum ≤ 2
  value : ∀ x (y : Fin l → Bool), orig C (p+l+j.val) x y = true ↔
    default x ∨ ∃ a ∈ data, a.2.value gs x = true ∧ orig C a.1 x y = true
  collects : ∀ i ∈ (C.gates.get j).inputs, guard (degree C p l) 0 (p+l+j.val) i = 1 →
    ∃ r, (i,r) ∈ data
  carries : ∀ a ∈ data, guard (degree C p l) 0 (p+l+j.val) a.1 = 1

theorem one_port {C : Circuit} {p l : ℕ} {gs : List Gate} (j : Fin C.gates.length) (a : ℕ) (r : Ref)
    (marked : guard (degree C p l) 0 (p+l+j.val) a = 1) (valid : r.valid p gs)
    (eq : ∀ (x : Fin p → Bool) (y : Fin l → Bool), orig C (p+l+j.val) x y = (r.value gs x && orig C a x y))
    (complete : ∀ i ∈ (C.gates.get j).inputs, guard (degree C p l) 0 (p+l+j.val) i = 1 → i = a) :
    Nonempty (GatePorts C p l gs j) := by
  refine ⟨⟨[(a,r)], fun _ => False, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro b hb
    rw [List.mem_singleton] at hb
    subst b
    exact marker (by omega) marked
  · intro b hb
    rw [List.mem_singleton] at hb
    subst b
    exact valid
  · cases r with
    | fixed b => cases b <;> simp [portCost, factorCost]
    | wire _ => simp [portCost, factorCost]
  · intro x y
    rw [eq]
    simp [Bool.and_eq_true]
  · intro i hi hd
    have equal := complete i hi hd
    subst i
    exact ⟨r, by simp⟩
  · intro b hb
    rw [List.mem_singleton] at hb
    subst b
    exact marked

theorem gate_ports (C : Circuit) (p l : ℕ) (gs : List Gate) (r : ℕ → Ref)
    (repr : PointRep C p l (p+l+C.gates.length) gs r)
    (j : Fin C.gates.length) (hj : degree C p l (p+l+j.val) = 1)
    (monotone : IsMonotoneCircuit C) (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    Nonempty (GatePorts C p l gs j) := by
  let g := C.gates.get j
  let index := p+l+j.val
  let deg := guard (degree C p l) 0 index
  let rv := guard r (.fixed false) index
  have pBound : index ≤ p+l+C.gates.length := by dsimp [index]; omega
  have member : g ∈ C.gates := List.get_mem ..
  have small := arity g member
  have guard_ok (i) (hi : deg i = 1) : i < index := (marker pBound hi).1
  have ed (i) (hi : i ∈ g.inputs) : deg i ≤ 1 := by
    have h := operand_degree C p l j i hi
    rwa [hj] at h
  rcases monotone g member with hand | hor
  · have count : (g.inputs.map deg).sum = 1 := by
      letI : DecidableEq GateOp := lineDegreeGateOpDecEq
      have h := degree_gate C p l j
      change degree C p l (p+l+j.val) =
        (if g.op = GateOp.and then (g.inputs.map deg).sum else (g.inputs.map deg).foldr max 0) at h
      rw [ite_eq_left hand] at h
      exact h.symm.trans hj
    cases hg : g.inputs with
    | nil => simp [hg] at count
    | cons a rest =>
      cases rest with
      | nil =>
        have ha : deg a = 1 := by simpa [hg] using count
        apply one_port j a (.fixed true) ha trivial
        · intro x y
          rw [orig_gate C j]
          change g.op.eval (g.inputs.map _) = _
          rw [hand, hg]
          simp [GateOp.eval, guard, index, guard_ok a ha, Ref.value]
        · intro i hi _
          change i ∈ g.inputs at hi
          rw [hg] at hi
          exact List.mem_singleton.mp hi
      | cons b tail =>
        have ht : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [hg, List.length_cons] at small
          omega
        subst tail
        have sum : deg a + deg b = 1 := by simpa [hg] using count
        have perm (u v : ℕ) (hu : deg u = 1) (hv : deg v = 0)
            (order : g.inputs = [u,v] ∨ g.inputs = [v,u]) : Nonempty (GatePorts C p l gs j) := by
          have hr := point_factor repr pBound v hv
          apply one_port j u (rv v) hu hr.1
          · intro x y
            rw [orig_gate C j, hr.2 x y]
            change g.op.eval (g.inputs.map _) = _
            rcases order with e | e <;> rw [hand, e] <;>
              simp [GateOp.eval, guard, index, guard_ok u hu, Bool.and_comm]
          · intro i hi hd
            change i ∈ g.inputs at hi
            have hh : i = u ∨ i = v := by rcases order with e | e <;> simpa [e, or_comm] using hi
            rcases hh with h | h
            · exact h
            · subst i; rw [show guard (degree C p l) 0 (p+l+j.val) v = deg v from rfl, hv] at hd
              omega
        rcases (show (deg a = 1 ∧ deg b = 0) ∨ (deg b = 1 ∧ deg a = 0) by omega) with h | h
        · exact perm a b h.1 h.2 (Or.inl hg)
        · exact perm b a h.1 h.2 (Or.inr hg)
  · let keep := g.inputs.filter (fun i => decide (deg i = 1))
    let ports := keep.map (fun i => (i, Ref.fixed true))
    have active (i : ℕ) : i ∈ keep ↔ i ∈ g.inputs ∧ deg i = 1 := by simp [keep]
    have fromPort (a : ℕ × Ref) (h : a ∈ ports) : ∃ i ∈ keep, a = (i, .fixed true) := by
      obtain ⟨i, hi, h⟩ := List.mem_map.mp h
      exact ⟨i, hi, h.symm⟩
    refine ⟨⟨ports, fun x => ∃ i ∈ g.inputs, deg i = 0 ∧ (rv i).value gs x = true,
      ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := fromPort a ha
      exact marker pBound ((active i).mp hi).2
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := fromPort a ha
      trivial
    · have sum : (ports.map portCost).sum = keep.length := by
        change ((keep.map fun i => (i, Ref.fixed true)).map portCost).sum = _
        induction keep with
        | nil => rfl
        | cons a l ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          rw [ih]
          simp [portCost, factorCost, Nat.add_comm]
      rw [sum]
      exact (List.length_filter_le _ _).trans small
    · intro x y
      have hval : orig C index x y = true ↔ ∃ i ∈ g.inputs,
          guard (fun k => orig C k x y) false index i = true := by
        change orig C (p+l+j.val) x y = true ↔ _
        rw [orig_gate C j]
        change g.op.eval (g.inputs.map _) = true ↔ _
        rw [hor]
        simp [GateOp.eval, List.any_eq_true, index]
      rw [hval]
      constructor
      · rintro ⟨i, hi, hv⟩
        by_cases hzero : deg i = 0
        · exact Or.inl ⟨i, hi, hzero, ((point_factor repr pBound i hzero).2 x y).trans hv⟩
        · have hd : deg i = 1 := by have := ed i hi; omega
          have hkeep := (active i).mpr ⟨hi,hd⟩
          exact Or.inr ⟨(i,.fixed true), List.mem_map_of_mem hkeep, rfl,
            by simpa [guard, guard_ok i hd] using hv⟩
      · rintro (⟨i, hi, hzero, h⟩ | ⟨a, ha, _, hv⟩)
        · exact ⟨i, hi, ((point_factor repr pBound i hzero).2 x y).symm.trans h⟩
        · obtain ⟨i, hi, rfl⟩ := fromPort a ha
          obtain ⟨hin, hd⟩ := (active i).mp hi
          exact ⟨i, hin, by simpa [guard, guard_ok i hd] using hv⟩
    · intro i hi hd
      exact ⟨.fixed true, List.mem_map_of_mem ((active i).mpr ⟨hi,hd⟩)⟩
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := fromPort a ha
      exact ((active i).mp hi).2

end PEqualNP.Outside.L_meta_738_aux


namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

theorem marked_mem {C : Circuit} {p l w : ℕ} (low : p+l ≤ w)
    (high : w < p+l+C.gates.length) (hd : degree C p l w = 1) : w ∈ markedWires C p l :=
  Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨low,high⟩,hd⟩

theorem marked_bounds {C : Circuit} {p l w : ℕ} (hw : w ∈ markedWires C p l) :
    p+l ≤ w ∧ w < p+l+C.gates.length ∧ degree C p l w = 1 := by
  obtain ⟨hi, hd⟩ := Finset.mem_filter.mp hw
  exact ⟨(Finset.mem_Ico.mp hi).1, (Finset.mem_Ico.mp hi).2, hd⟩

def markedIndex {C : Circuit} {p l w : ℕ} (h : w ∈ markedWires C p l) : Fin C.gates.length :=
  ⟨w-(p+l), by have hb := marked_bounds h; omega⟩

theorem index_marked {C : Circuit} {p l w : ℕ} (h : w ∈ markedWires C p l) :
    p+l+(markedIndex h).val = w := by
  have hb := marked_bounds h
  dsimp [markedIndex]
  omega

theorem input_mark {C : Circuit} {p l i : ℕ} (h : i < p+l) (hd : degree C p l i = 1) :
    i ∈ marks p l := by
  rw [input_degree C p l i h] at hd
  by_cases hlow : p ≤ i
  · exact Finset.mem_Ico.mpr ⟨hlow,h⟩
  · simp [hlow] at hd

noncomputable def choosePorts (C : Circuit) (p l : ℕ) (gs : List Gate) (refs : ℕ → Ref)
    (repr : PointRep C p l (p+l+C.gates.length) gs refs) (hm : IsMonotoneCircuit C)
    (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (w : ℕ) (hw : w ∈ markedWires C p l) :
    GatePorts C p l gs (markedIndex hw) :=
  Classical.choice (gate_ports C p l gs refs repr (markedIndex hw)
    (by rw [index_marked]; exact (marked_bounds hw).2.2) hm arity)

noncomputable def makeNetwork (C : Circuit) (p l : ℕ) (gs : List Gate) (refs : ℕ → Ref)
    (repr : PointRep C p l (p+l+C.gates.length) gs refs) (hm : IsMonotoneCircuit C)
    (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) : Network p (Fin l → Bool) := by
  let get := choosePorts C p l gs refs repr hm arity
  refine {
    pointProgram := gs
    start := p+l
    markedInputs := marks p l
    markedGates := markedWires C p l
    ports := fun w => if h : w ∈ markedWires C p l then (get w h).data else []
    residual := fun w x => if h : w ∈ markedWires C p l then (get w h).default x else False
    original := orig C
    below := ?_
    inputBelow := ?_
    markedChild := ?_
    present := ?_
    budget := ?_
    description := ?_ }
  · intro w hw a ha
    simp only [dite_eq_left hw] at ha
    simpa [index_marked hw] using ((get w hw).children a ha).1
  · intro i hi
    exact (Finset.mem_Ico.mp hi).2
  · intro w hw a ha
    simp only [dite_eq_left hw] at ha
    rcases ((get w hw).children a ha).2 with hi | hi
    · have le := ((get w hw).children a ha).1
      have hd := (get w hw).carries a ha
      exact Or.inl (input_mark hi (by simpa [guard, le] using hd))
    · exact Or.inr hi
  · intro w hw a ha
    simp only [dite_eq_left hw] at ha
    exact (get w hw).valid a ha
  · intro w hw
    simp only [dite_eq_left hw]
    exact (get w hw).budget
  · intro w hw x y
    simp only [dite_eq_left hw]
    simpa [index_marked hw] using (get w hw).value x y

theorem collects_read (C : Circuit) (p l : ℕ) (gs : List Gate) (refs : ℕ → Ref)
    (repr : PointRep C p l (p+l+C.gates.length) gs refs) (hm : IsMonotoneCircuit C)
    (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (a b : ℕ) (edge : Reads C p l a b)
    (ha : degree C p l a = 1) (hb : degree C p l b = 1) :
    ∃ r, (a,r) ∈ (makeNetwork C p l gs refs repr hm arity).ports b := by
  obtain ⟨lower, j, rfl, mem⟩ := edge
  have marked : p+l+j.val ∈ markedWires C p l := marked_mem (by omega) (by omega) hb
  have index : markedIndex marked = j := by
    apply Fin.ext
    simp [markedIndex]
  let data := choosePorts C p l gs refs repr hm arity (p+l+j.val) marked
  have contrib := data.collects a (by simpa [index] using mem)
    (by simpa [guard, index, lower] using ha)
  simpa [makeNetwork, marked, data] using contrib

theorem gate_count (C : Circuit) (p l : ℕ) :
    (pointGates C p l C.gates.length).card + (markedWires C p l).card ≤ C.gates.length := by
  let source := (Finset.range C.gates.length).filter (fun j => degree C p l (p+l+j) = 1)
  have shift : Finset.image (fun j => p+l+j) source = markedWires C p l := by
    ext w
    constructor
    · rintro h
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hj, hd⟩ := Finset.mem_filter.mp hj
      have hjlt := Finset.mem_range.mp hj
      exact marked_mem (by omega) (by omega) hd
    · intro hw
      obtain ⟨low, high, hd⟩ := marked_bounds hw
      have eq : p+l+(w-(p+l)) = w := by omega
      apply Finset.mem_image.mpr
      refine ⟨w-(p+l), Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, eq⟩
      rwa [eq]
  have mCard : (markedWires C p l).card = source.card := by
    rw [← shift, Finset.card_image_of_injective _ (fun a b h => by omega)]
  have disj : Disjoint (pointGates C p l C.gates.length) source := by
    rw [Finset.disjoint_left]
    intro j h0 h1
    have d0 := (Finset.mem_filter.mp h0).2
    have d1 := (Finset.mem_filter.mp h1).2
    omega
  have sub : (pointGates C p l C.gates.length) ∪ source ⊆ Finset.range C.gates.length := by
    intro j hm
    rcases Finset.mem_union.mp hm with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  rw [mCard, ← Finset.card_union_of_disjoint disj]
  simpa using Finset.card_le_card sub

end PEqualNP.Outside.L_meta_738_aux


namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

theorem orig_outside (C : Circuit) {p l i : ℕ} (hi : p+l+C.gates.length ≤ i)
    (x : Fin p → Bool) (y : Fin l → Bool) : orig C i x y = false := by
  change (wires C.gates (List.ofFn x ++ List.ofFn y)).getD i false = false
  apply List.getD_eq_default
  simpa [wires_len] using hi

theorem seen_reaches (C : Circuit) (p l : ℕ) (gs : List Gate) (r : ℕ → Ref)
    (repr : PointRep C p l (p+l+C.gates.length) gs r) (mono : IsMonotoneCircuit C)
    (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (s : Accumulator p)
    (closed : closedAbove (makeNetwork C p l gs r repr mono arity) s (p+l))
    (houtput : degree C p l C.output = 1) (root : C.output ∈ s.seen)
    (a : ℕ) (route : Relation.ReflTransGen (Reads C p l) a C.output) :
    degree C p l a = 1 → a ∈ s.seen := by
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => degree C p l a = 1 → a ∈ s.seen) route (fun _ => root) ?_
  intro a b edge tail ih ha
  have db : degree C p l b = 1 := by
    have h1 := reads_degree edge
    have h2 := path_degree tail
    omega
  have hb : b ∈ markedWires C p l := by
    obtain ⟨_, j, rfl, _⟩ := edge
    exact marked_mem (by omega) (by omega) db
  obtain ⟨factor, hfactor⟩ := collects_read C p l gs r repr mono arity a b edge ha db
  exact closed b (ih db) (marked_bounds hb).1 hb _ hfactor

def fixedTrue : Ref → Bool
  | .fixed true => true
  | _ => false

def outlet (default : ℕ) : Ref → ℕ
  | .fixed _ => default
  | .wire i => i

theorem ref_outlet {p : ℕ} (gs : List Gate) (r : Ref) (x : Fin p → Bool) :
    r.value gs x = true ↔ fixedTrue r = true ∨
      (wires gs (List.ofFn x)).getD (outlet (p+gs.length) r) false = true := by
  have no : (wires gs (List.ofFn x)).getD (p+gs.length) false = false := by
    apply List.getD_eq_default
    simp [wires_len]
  cases r with
  | fixed b =>
    change b = true ↔ fixedTrue (.fixed b) = true ∨
      (wires gs (List.ofFn x)).getD (p+gs.length) false = true
    rw [no]
    cases b <;> simp [fixedTrue]
  | wire i => simp [fixedTrue, outlet, Ref.value]

theorem run_transposition (p l : ℕ) (C : Circuit) (N : Finset (Fin l))
    (mono : IsMonotoneCircuit C) (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (degreeLe : HasLineDegree (p+l) (marks p l) C 1)
    (gateLive : ∀ j : Fin C.gates.length,
      Relation.ReflTransGen (Reads C p l) (p+l+j.val) C.output)
    (lineLive : ∀ w : Fin l, w ∈ N ↔ Relation.ReflTransGen (Reads C p l) (p+w.val) C.output) :
    ∃ (D : Circuit) (T : Finset (Fin l)) (o : Fin l → ℕ),
      IsMonotoneCircuit D ∧ (∀ h ∈ D.gates, h.inputs.length ≤ 2) ∧ D.size + N.card ≤ C.size+1 ∧
      ∀ (x : Fin p → Bool) (y : Fin l → Bool), C.eval (List.ofFn x ++ List.ofFn y) =
        (C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin l => false)) ||
         decide (∃ u : Fin l, y u = true ∧ (u ∈ T ∨ (D.wires (List.ofFn x)).getD (o u) false = true))) := by
  classical
  obtain ⟨gs, refs, baseGood, baseSize, repr⟩ := compile_points C p l mono arity C.gates.length le_rfl
  have dLeast : degree C p l C.output ≤ 1 := degreeLe
  have lineDegree (w : Fin l) : degree C p l (p+w.val) = 1 := by
    rw [input_degree C p l (p+w.val) (by omega), ite_eq_left (by omega)]
  by_cases hd : degree C p l C.output = 0
  · have empty : N = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hpath := path_degree ((lineLive w).mp hw)
      rw [lineDegree w, hd] at hpath
      omega
    refine ⟨⟨[],0⟩, ∅, fun _ => p, by simp [IsMonotoneCircuit], by simp, ?_, ?_⟩
    · simp [Circuit.size, empty]
    · intro x y
      have equal : orig C C.output x y = orig C C.output x (fun _ : Fin l => false) := by
        by_cases h : C.output < p+l+C.gates.length
        · rw [← (repr C.output h hd).2 x y, ← (repr C.output h hd).2 x (fun _ => false)]
        · rw [orig_outside C (by omega), orig_outside C (by omega)]
      have emptyRead : (wires [] (List.ofFn x)).getD p false = false := by
        apply List.getD_eq_default
        simp [wires_len]
      change orig C C.output x y = (orig C C.output x (fun _ : Fin l => false) ||
        decide (∃ u : Fin l, y u = true ∧ (u ∈ (∅ : Finset (Fin l)) ∨
          (wires [] (List.ofFn x)).getD p false = true)))
      rw [emptyRead]
      simpa using equal
  · have dOne : degree C p l C.output = 1 := by omega
    have rootIn : C.output < p+l+C.gates.length := by
      by_contra! h
      exact hd (outside_degree C p l C.output h)
    let m := makeNetwork C p l gs refs repr mono arity
    let init : Accumulator p := ⟨gs, {C.output}, fun _ => .fixed true, baseGood, fun _ => trivial⟩
    have initGood : allowed m init := by
      intro w hw
      have eq : w = C.output := Finset.mem_singleton.mp hw
      subst w
      by_cases h : C.output < p+l
      · exact Or.inl (input_mark h dOne)
      · exact Or.inr (marked_mem (by omega) rootIn dOne)
    have initClosed : closedAbove m init (m.start+C.gates.length) := by
      intro w hw hle
      have eq : w = C.output := Finset.mem_singleton.mp hw
      change p+l+C.gates.length ≤ w at hle
      omega
    obtain ⟨s, R, _, grows, totalCost, goodSeen, hClosed, expansion⟩ :=
      remove_marked m C.gates.length (fun _ => False) init
        ⟨[], by change gs = gs ++ []; simp⟩ initGood initClosed
    have rootSeen : C.output ∈ s.seen := grows (Finset.mem_singleton_self _)
    have allGates : markedWires C p l ⊆ s.seen := by
      intro w hw
      have hLive := gateLive (markedIndex hw)
      rw [index_marked hw] at hLive
      exact seen_reaches C p l gs refs repr mono arity s hClosed dOne rootSeen w hLive (marked_bounds hw).2.2
    let lines := N.image (fun w => p+w.val)
    have allLines : lines ⊆ s.seen := by
      intro i hi
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hi
      exact seen_reaches C p l gs refs repr mono arity s hClosed dOne rootSeen _
        ((lineLive w).mp hw) (lineDegree w)
    have disj : Disjoint (markedWires C p l) lines := by
      rw [Finset.disjoint_left]
      intro w hGate hLine
      obtain ⟨u, hu, eq⟩ := Finset.mem_image.mp hLine
      have := (marked_bounds hGate).1
      omega
    have lineCard : lines.card = N.card := by
      rw [show lines = N.image (fun w => p+w.val) from rfl, Finset.card_image_of_injective]
      intro u v he
      change p+u.val = p+v.val at he
      exact Fin.ext (Nat.add_left_cancel he)
    have seenCost := Finset.card_le_card (Finset.union_subset allGates allLines)
    rw [Finset.card_union_of_disjoint disj, lineCard] at seenCost
    have reduceCount : (m.markedGates.filter (fun j => j < m.start+C.gates.length)).card =
        (markedWires C p l).card := by
      apply congrArg Finset.card
      ext w
      change w ∈ ((markedWires C p l).filter (fun j => j < p+l+C.gates.length)) ↔ _
      simp only [Finset.mem_filter]
      exact ⟨And.left, fun h => ⟨h, (marked_bounds h).2.1⟩⟩
    rw [reduceCount] at totalCost
    change s.gs.length+s.seen.card ≤ gs.length+1+2*(markedWires C p l).card at totalCost
    have available := gate_count C p l
    let T : Finset (Fin l) := Finset.univ.filter (fun w => fixedTrue (ctx s (p+w.val)))
    let o (w : Fin l) := outlet (p+s.gs.length) (ctx s (p+w.val))
    refine ⟨⟨s.gs,0⟩, T, o, fun g hg => (s.wellFormed g hg).1,
      fun g hg => (s.wellFormed g hg).2, ?_, ?_⟩
    · change s.gs.length + N.card ≤ C.gates.length+1
      omega
    · have initial (x : Fin p → Bool) (y : Fin l → Bool) :
          (False ∨ frontier m init (p+l+C.gates.length) x y) ↔ orig C C.output x y = true := by
        simp only [false_or]
        constructor
        · rintro ⟨w, hw, hctx, eval⟩
          by_cases eq : w = C.output
          · exact eq ▸ eval
          · simp [ctx, init, eq, Ref.value] at hctx
        · intro h
          exact ⟨C.output, rootIn, by simp [ctx, init, Ref.value], h⟩
      have terminal (x : Fin p → Bool) (y : Fin l → Bool) : frontier m s (p+l) x y ↔
          ∃ u : Fin l, y u = true ∧ (u ∈ T ∨ (wires s.gs (List.ofFn x)).getD (o u) false = true) := by
        constructor
        · rintro ⟨w, hw, hwctx, eval⟩
          have seen : w ∈ s.seen := by by_contra h; simp [ctx, h, Ref.value] at hwctx
          have marked : w ∈ marks p l := (goodSeen _ seen).resolve_right
            (fun wMark => Nat.not_lt_of_ge (marked_bounds wMark).1 hw)
          have lower := (Finset.mem_Ico.mp marked).1
          let u : Fin l := ⟨w-p, by omega⟩
          have eq : p+u.val = w := by dsimp [u]; omega
          refine ⟨u, ?_, ?_⟩
          · rw [← orig_line C u x y]; rwa [eq]
          · have ht := (ref_outlet s.gs (ctx s (p+u.val)) x).mp (by rwa [eq])
            simpa [T, o] using ht
        · rintro ⟨u, hy, coeff⟩
          refine ⟨p+u.val, by omega, ?_, ?_⟩
          · apply (ref_outlet s.gs (ctx s (p+u.val)) x).mpr
            simpa [T, o] using coeff
          · change orig C (p+u.val) x y = true
            rwa [orig_line]
      have main (x : Fin p → Bool) (y : Fin l → Bool) :=
        (initial x y).symm.trans ((expansion x y).trans (or_congr Iff.rfl (terminal x y)))
      intro x y
      have baseline : orig C C.output x (fun _ : Fin l => false) = true ↔ R x := by
        simpa using main x (fun _ => false)
      apply Bool.eq_iff_iff.mpr
      change orig C C.output x y = true ↔ (orig C C.output x (fun _ : Fin l => false) ||
        decide (∃ u : Fin l, y u = true ∧ (u ∈ T ∨ (wires s.gs (List.ofFn x)).getD (o u) false = true))) = true
      rw [Bool.or_eq_true, decide_eq_true_eq, baseline]
      exact main x y

end PEqualNP.Outside.L_meta_738_aux

theorem PEqualNP.Outside.L_meta_738 :
    ∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true))) :=
  PEqualNP.Outside.L_meta_738_aux.run_transposition
