import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

-- Original proof by k-sandhu in PR 149.
-- The circuit evaluation and reverse cut are adapted from L-meta-270 and L-meta-782.

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_925

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

private lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  have cardP : P.card ≤ 2 :=
    (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
  refine ⟨P, cardP, fun r hr => (Finset.mem_filter.mp hr).2, ?_⟩
  intro x y hxy hx
  let read (z : Fin n → Bool) (r : ℕ) : Bool := if r < w then value C z r else false
  have move (r : ℕ) (hr : r ∈ g.inputs) : read x r = true → read y r = true := by
    unfold read
    by_cases hrange : r < w
    · simp only [ite_eq_left hrange]
      exact hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hrange⟩)
    · simp [hrange]
  have formula (z : Fin n → Bool) : value C z w = g.op.eval (g.inputs.map (read z)) :=
    gate_value C z w hn hw
  rw [formula x] at hx
  rw [formula y]
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
    intro b hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact move r hr (hx _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
    obtain ⟨b, hb, ht⟩ := hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact ⟨read y r, List.mem_map.mpr ⟨r, hr, rfl⟩, move r hr ht⟩

private lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

-- Expand true gates in reverse evaluation order, increasing the cut by at most one.
private lemma true_cut {n : ℕ} (C : Circuit) (ψ : ℕ → Bool) (G : Finset ℕ)
    (step : ∀ w ∈ G, ψ w = true →
      ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ v ∈ P, v < w ∧ ψ v = true) ∧
        ∀ x : Fin n → Bool, (∀ v ∈ P, value C x v = true) → value C x w = true)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t)
    (hψF : ∀ w ∈ F, ψ w = true) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      (∀ w ∈ B, ψ w = true) ∧
      ∀ x : Fin n → Bool, (∀ w ∈ B, value C x w = true) → ∀ w ∈ F, value C x w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., hψF, fun _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := step t hex.2 (hψF t hex.1)
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact (hP w hw).1
      have hψF' : ∀ w ∈ F', ψ w = true := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hψF w (Finset.mem_erase.mp hw).2
        · exact (hP w hw).2
      obtain ⟨B, hd, hc, hBψ, hi⟩ := ih F' hF' hψF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, hBψ, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x hx w hw
        by_cases h : w = t
        · subst w
          exact hp x fun v hv => hi x hx v (Finset.mem_union_right _ hv)
        · exact hi x hx w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hBψ, hi⟩ := ih F hF' hψF
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hBψ, hi⟩


private theorem block_union_bound {α V : Type} [DecidableEq α] [DecidableEq V]
    {q m : ℕ} (hq : 2 ≤ q) (S : Fin m → Finset V)
    (sizes : ∀ i, (S i).card = q + 1)
    (overlap : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (L : Finset α) (T : α → Finset V)
    (blocks : ∀ a ∈ L, (T a).card ≤ 1 ∨ ∃ j, T a = S j) :
    (L.biUnion T).card ≤ L.card * q + 1 := by
  classical
  by_cases anchor : ∃ a ∈ L, ∃ j, T a = S j
  · obtain ⟨a, ha, j, hj⟩ := anchor
    have rest (b : α) (hb : b ∈ L.erase a) : ((T b) \ S j).card ≤ q := by
      rcases blocks b (Finset.mem_of_mem_erase hb) with hsmall | ⟨k, hk⟩
      · have hsub := Finset.card_le_card (Finset.sdiff_subset : T b \ S j ⊆ T b)
        omega
      · rw [hk]
        by_cases hkj : k = j
        · simp [hkj]
        · have hi := overlap k j hkj
          have hsize := sizes k
          have he := Finset.card_sdiff_add_card_inter (S k) (S j)
          omega
    have incl : L.biUnion T ⊆ S j ∪ (L.erase a).biUnion (fun b => T b \ S j) := by
      intro v hv
      by_cases h : v ∈ S j
      · exact Finset.mem_union_left _ h
      · obtain ⟨b, hb, hbv⟩ := Finset.mem_biUnion.mp hv
        have hba : b ≠ a := by
          intro he
          subst b
          exact h (hj ▸ hbv)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, Finset.mem_sdiff.mpr ⟨hbv, h⟩⟩)
    have hr : ((L.erase a).biUnion (fun b => T b \ S j)).card ≤ (L.erase a).card * q := by
      refine Finset.card_biUnion_le.trans ?_
      calc
        _ ≤ ∑ _b ∈ L.erase a, q := Finset.sum_le_sum rest
        _ = _ := by simp
    calc
      _ ≤ _ := Finset.card_le_card incl
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ (q + 1) + (L.erase a).card * q := by rw [sizes]; omega
      _ = L.card * q + 1 := by
        rw [← Finset.card_erase_add_one ha, Nat.add_mul]
        omega
  · have small : ∀ a ∈ L, (T a).card ≤ q := by
      intro a ha
      rcases blocks a ha with hs | hex
      · omega
      · exact (anchor ⟨a, ha, hex⟩).elim
    calc
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ L, q := Finset.sum_le_sum small
      _ ≤ _ := by simp


private def input {n : ℕ} (U : Finset (Fin n)) : Fin n → Bool := fun u => decide (u ∈ U)

private def assigned {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter (fun w =>
    value C (input (S i)) w = true ∧ ∀ j, j ≠ i → value C (input (S j)) w = false)

private lemma count_assigned {n m q K c : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m)
    (o : ℕ) (hq : 2 ≤ q) (sizes : ∀ j, (S j).card = q + 1)
    (overlap : ∀ a b, a ≠ b → (S a ∩ S b).card = 1)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (correct : ∀ T : Finset (Fin n), T.card ≤ K → (value C (input T) o = true ↔ S i ⊆ T))
    (hc : c ≤ q) (hK : c * q < K) : c ≤ (assigned C S i).card := by
  classical
  by_contra! small
  let G := assigned C S i
  let x := input (S i)
  have enough : q + 1 ≤ K := by
    have pos : 1 ≤ c := by omega
    have h := Nat.mul_le_mul_right q pos
    simp only [Nat.one_mul] at h
    omega
  have root : value C x o = true := (correct (S i) (by rw [sizes i]; exact enough)).mpr (Finset.Subset.refl _)
  have step : ∀ w ∈ G, value C x w = true →
      ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ v ∈ P, v < w ∧ value C x v = true) ∧
        ∀ y : Fin n → Bool, (∀ v ∈ P, value C y v = true) → value C y w = true := by
    intro w hw yes
    have range := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
    obtain ⟨R, hr, past, step⟩ := gate_inputs C hG w range.1 range.2
    let P := R.filter (fun r => value C x r = true)
    refine ⟨P, (Finset.card_filter_le _ _).trans hr, ?_, ?_⟩
    · intro v hv
      exact ⟨past v (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
    · intro y holds
      exact step x y (fun v hv h => holds v (Finset.mem_filter.mpr ⟨hv, h⟩)) yes
  obtain ⟨B, disjoint, cb, truth, from_cut⟩ := true_cut C (value C x) G step (o + 1) {o}
    (fun w hw _ => by rw [Finset.mem_singleton.mp hw]; omega)
    (fun w hw => by rw [Finset.mem_singleton.mp hw]; exact root)
  have cardB : B.card ≤ c := by
    have bounded := Finset.card_filter_le G (fun w => w < o + 1)
    simp only [Finset.card_singleton] at cb
    change G.card < c at small
    omega
  have choose_patch (w : {w // w ∈ B}) : ∃ T : Finset (Fin n),
      (T.card ≤ 1 ∨ ∃ j : Fin m, j ≠ i ∧ T = S j) ∧ value C (input T) w.val = true := by
    by_cases hv : w.val < n
    · let v : Fin n := ⟨w.val, hv⟩
      refine ⟨{v}, .inl (by simp), ?_⟩
      change value C (input {v}) v = true
      simp [input_value, input]
    · by_cases hg : w.val < n + C.size
      · have absent := fun h => Finset.disjoint_left.mp disjoint w.property h
        have other : ∃ j, j ≠ i ∧ value C (input (S j)) w.val = true := by
          by_contra! no
          apply absent
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hg⟩, truth _ w.property, ?_⟩
          intro j different
          cases h : value C (input (S j)) w.val with
          | false => rfl
          | true => exact (no j different h).elim
        obtain ⟨j, diff, h⟩ := other
        exact ⟨S j, .inr ⟨j, diff, rfl⟩, h⟩
      · have yes := truth _ w.property
        rw [missing_value C x _ (by omega)] at yes
        contradiction
  choose T shape patch using choose_patch
  let P := B.attach.biUnion T
  have cardP : P.card ≤ K := by
    have direct : P.card ≤ B.attach.card * q + 1 :=
      block_union_bound hq S sizes overlap B.attach T (fun w _ =>
        (shape w).imp_right (fun ⟨j, _, eq⟩ => ⟨j, eq⟩))
    have hattach : B.attach.card ≤ c := by simpa only [Finset.card_attach] using cardB
    have hm := Nat.mul_le_mul_right q hattach
    omega
  have overlapP : (P ∩ S i).card ≤ c := by
    have points : P ∩ S i ⊆ B.attach.biUnion (fun w => T w ∩ S i) := by
      intro u hu
      obtain ⟨hp, hi⟩ := Finset.mem_inter.mp hu
      obtain ⟨w, hw, ht⟩ := Finset.mem_biUnion.mp hp
      exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_inter.mpr ⟨ht, hi⟩⟩
    have cover : ∀ w ∈ B.attach, (T w ∩ S i).card ≤ 1 := by
      intro w _
      rcases shape w with bound | ⟨j, diff, eq⟩
      · exact (Finset.card_le_card Finset.inter_subset_left).trans bound
      · rw [eq, overlap j i diff]
    refine (Finset.card_le_card points).trans ?_
    have bound := Finset.card_biUnion_le_card_mul B.attach (fun w => T w ∩ S i) 1 cover
    simpa only [Nat.mul_one, Finset.card_attach] using bound.trans (by
      simpa only [Nat.mul_one, Finset.card_attach] using cardB)
  have accepted : value C (input P) o = true := by
    apply from_cut (input P) _ o (Finset.mem_singleton_self o)
    intro w hw
    let v : {r // r ∈ B} := ⟨w, hw⟩
    apply value_mono C hG (input (T v)) (input P) _ w (patch v)
    intro u hu
    have hit : u ∈ P := Finset.mem_biUnion.mpr ⟨v, Finset.mem_attach B v, of_decide_eq_true hu⟩
    simp [input, hit]
  have cover : S i ⊆ P := (correct P cardP).mp accepted
  have contained : S i ⊆ P ∩ S i := fun u hu => Finset.mem_inter.mpr ⟨cover hu, hu⟩
  have bound := Finset.card_le_card contained
  rw [sizes i] at bound
  omega

end PEqualNP.Outside.L_meta_925

open PEqualNP.Outside.L_meta_925 in
theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq sizes overlap gates out hG eval c hc hK
  let C : Circuit := ⟨gates, 0⟩
  let G (i : Fin m) := assigned C S i
  have perf (i : Fin m) (T : Finset (Fin n)) (within : T.card ≤ K) :
      value C (input T) (out i) = true ↔ S i ⊆ T := by
    have inWeight : (Finset.univ.filter (fun u => input T u = true)) = T := by
      ext u
      simp [input]
    change (Circuit.eval ⟨gates, out i⟩ (List.ofFn (input T))) = true ↔ _
    rw [eval i (input T) (inWeight.symm ▸ within)]
    simp [input, Finset.subset_iff]
  have disjoint : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hi hj => ?_
    have t := (Finset.mem_filter.mp hi).2.1
    have f := (Finset.mem_filter.mp hj).2.2 i hij
    rw [f] at t
    contradiction
  calc
    m * c = ∑ i : Fin m, c := by simp
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ =>
      count_assigned C S i (out i) hq sizes overlap hG (perf i) hc hK
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion disjoint).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun w hw => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = gates.length := by simp [C, Circuit.size]
