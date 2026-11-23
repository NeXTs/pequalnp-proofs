import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_734

private theorem other_color : ∀ a b c : Fin 2, a ≠ b → b ≠ c → a = c := by
  decide

private theorem small_color_class {n : ℕ} (T : Set (Fin n)) (color : Fin n → Fin 2)
    (small : T.ncard ≤ 5) :
    ∃ c : Fin 2, (T.toFinite.toFinset.filter fun v => color v = c).card ≤ 2 := by
  classical
  have tcard : T.toFinite.toFinset.card ≤ 5 := by
    simpa only [← Set.ncard_eq_toFinset_card T T.toFinite] using small
  have halves := Finset.card_filter_add_card_filter_not (s := T.toFinite.toFinset) (fun v => color v = 0)
  by_cases h : (T.toFinite.toFinset.filter fun v => color v = 0).card ≤ 2
  · exact ⟨0, h⟩
  · have complement : ∀ x : Fin 2, x ≠ 0 ↔ x = 1 := by decide
    refine ⟨1, ?_⟩
    have same : {v ∈ T.toFinite.toFinset | ¬ color v = 0} =
        (T.toFinite.toFinset.filter fun v => color v = 1) := by
      ext v
      simp only [Finset.mem_filter, complement]
    rw [same] at halves
    omega

private theorem safe_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) (T : Set (Fin n))
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (degree : ∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard)
    (B : Finset (Fin n)) (few : B.card ≤ 2) (outside : ∀ b ∈ B, b ∉ T)
    (y : Fin n) (hy : y ∈ T) :
    ∃ x, G.Adj y x ∧ ∀ b ∈ B, ¬ G.Adj x b := by
  classical
  by_contra none
  let N := Finset.univ.filter (fun x => G.Adj y x)
  have Nrel (x : ↥N) : G.Adj y x := (Finset.mem_filter.mp x.property).2
  have large : 3 ≤ N.card := by
    have same : (↑N : Set (Fin n)) = {w | G.Adj y w} := by
      ext w
      simp [N]
    have d := degree y
    rwa [← same, Set.ncard_coe_finset] at d
  have blocked (x : ↥N) : ∃ b ∈ B, G.Adj x b := by
    by_contra h
    exact none ⟨x, Nrel x, fun b hb hxb => h ⟨b, hb, hxb⟩⟩
  choose root rootMem rootAdj using blocked
  let f (x : ↥N) : ↥B := ⟨root x, rootMem x⟩
  have injective : Function.Injective f := by
    intro x x' hf
    apply Subtype.ext
    have same : root x = root x' := congrArg Subtype.val hf
    have hxb : G.Adj (root x) x' := by
      rw [same]
      exact (rootAdj x').symm
    have diff : y ≠ root x := fun h => outside (root x) (rootMem x) (h ▸ hy)
    exact (noSquare y x (root x) x' (Nrel x) (rootAdj x) hxb (Nrel x').symm).resolve_left diff
  have bound := Fintype.card_le_of_injective f injective
  simp only [Fintype.card_coe] at bound
  omega

theorem closed_neighborhood {n : ℕ} (G : SimpleGraph (Fin n))
    (two : G.Colorable 2)
    (noSquare : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (degree : ∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard)
    (T : Set (Fin n)) (small : T.ncard ≤ 5)
    (hits : ∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) → ∃ t ∈ T, t ∈ I) :
    ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  classical
  by_contra failure
  have exposed (v : Fin n) (hv : v ∈ T) : ∃ w, G.Adj v w ∧ w ∉ T := by
    by_contra h
    refine failure ⟨v, hv, fun w adj => ?_⟩
    by_contra notMem
    exact h ⟨w, adj, notMem⟩
  obtain ⟨color⟩ := two
  obtain ⟨c, hc⟩ := small_color_class T color small
  let TX := T.toFinite.toFinset.filter (fun v => color v = c)
  have inT (v : ↥TX) : (v : Fin n) ∈ T :=
    T.toFinite.mem_toFinset.mp (Finset.mem_filter.mp v.property).1
  have inColor (v : ↥TX) : color v = c := (Finset.mem_filter.mp v.property).2
  have exists_pick (v : ↥TX) : ∃ w, G.Adj v w ∧ w ∉ T := exposed v (inT v)
  choose pick pickAdj pickOutside using exists_pick
  let B := (Finset.univ : Finset ↥TX).image pick
  have Bcard : B.card ≤ 2 := by
    have b : B.card ≤ (Finset.univ : Finset ↥TX).card := Finset.card_image_le
    exact b.trans (by simpa [TX] using hc)
  have bProperties (b : Fin n) (hb : b ∈ B) : b ∉ T ∧ color b ≠ c := by
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨pickOutside v, fun e => color.valid (pickAdj v) ((inColor v).trans e.symm)⟩
  have neighbors_B (v : Fin n) (hv : v ∈ TX) : ∃ b ∈ B, G.Adj v b :=
    ⟨pick ⟨v,hv⟩, Finset.mem_image_of_mem pick (Finset.mem_univ _), pickAdj ⟨v,hv⟩⟩
  let P : Set (Fin n) := {x | color x = c ∧ ∀ b ∈ B, ¬ G.Adj x b}
  let Q : Set (Fin n) := {y | color y ≠ c ∧ ∀ x ∈ P, ¬ G.Adj y x}
  have B_in_Q (b : Fin n) (hb : b ∈ B) : b ∈ Q :=
    ⟨(bProperties b hb).2, fun x hx h => hx.2 b hb h.symm⟩
  have avoidP (x : Fin n) (hx : x ∈ T) : x ∉ P := by
    intro hp
    have tx : x ∈ TX := Finset.mem_filter.mpr ⟨T.toFinite.mem_toFinset.mpr hx, hp.1⟩
    obtain ⟨b, hb, hxb⟩ := neighbors_B x tx
    exact hp.2 b hb hxb
  have avoidQ (y : Fin n) (hy : y ∈ T) : y ∉ Q := by
    intro hq
    obtain ⟨x, hxy, safe⟩ := safe_neighbor G T noSquare degree B Bcard
      (fun b hb => (bProperties b hb).1) y hy
    have hx : x ∈ P := ⟨other_color _ _ _ (color.valid hxy.symm) hq.1, safe⟩
    exact hq.2 x hx hxy
  let I := P ∪ Q
  have independent : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    intro u hu v hv h
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact color.valid h (hu.1.trans hv.1.symm)
    · exact hv.2 u hu h.symm
    · exact hu.2 v hv h
    · exact hu.1 (other_color _ _ _ (color.valid h) hv.1)
  have dominates : ∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u := by
    intro v hv
    by_cases hColor : color v = c
    · have existsB : ∃ b ∈ B, G.Adj v b := by
        by_contra h
        exact hv (Or.inl ⟨hColor, fun b hb hAdj => h ⟨b, hb, hAdj⟩⟩)
      obtain ⟨b, hb, hAdj⟩ := existsB
      exact ⟨b, Or.inr (B_in_Q b hb), hAdj⟩
    · have existsP : ∃ x ∈ P, G.Adj v x := by
        by_contra h
        exact hv (Or.inr ⟨hColor, fun x hx hAdj => h ⟨x, hx, hAdj⟩⟩)
      obtain ⟨x, hx, hAdj⟩ := existsP
      exact ⟨x, Or.inl hx, hAdj⟩
  obtain ⟨t, ht, hI⟩ := hits I independent dominates
  exact hI.elim (avoidP t ht) (avoidQ t ht)

end PEqualNP.Outside.L_meta_734

theorem PEqualNP.Outside.L_meta_734 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  G.Colorable 2 →
  (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
  (∀ v, 3 ≤ {w : Fin n | G.Adj v w}.ncard) →
  ∀ T : Set (Fin n), T.ncard ≤ 5 →
    (∀ I : Set (Fin n), (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) →
      ∃ t ∈ T, t ∈ I) →
    ∃ v ∈ T, ∀ w, G.Adj v w → w ∈ T := by
  intro n G two noSquare degree T small hits
  exact PEqualNP.Outside.L_meta_734.closed_neighborhood G two noSquare degree T small hits
