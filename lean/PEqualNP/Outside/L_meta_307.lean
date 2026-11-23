import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Preimage
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_307 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ c : ℕ, (∀ S : Finset V, (∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S) → c ≤ S.card) ↔ (∀ S : Finset (Fin N), (∀ a b, G'.Adj a b → a ∈ S ∨ b ∈ S) → c ≤ S.card) := by
  classical
  intro V G0 N num G' bounded unique corresponding c
  let active (u : V) : Prop := ∃ v : V, G0.Adj u v
  let number : Subtype active ↪ Fin N :=
    ⟨fun u => ⟨num u.val, by
      obtain ⟨v, edge⟩ := u.property
      exact bounded u.val v edge⟩, by
      intro u w equal
      obtain ⟨v, uv⟩ := u.property
      obtain ⟨z, wz⟩ := w.property
      apply Subtype.ext
      exact unique u.val v w.val z uv wz (congrArg Fin.val equal)⟩
  have imageEdge {u v : V} (edge : G0.Adj u v) :
      G'.Adj (number ⟨u, ⟨v, edge⟩⟩) (number ⟨v, ⟨u, edge.symm⟩⟩) :=
    (corresponding _ _).2 ⟨u, v, edge, rfl, rfl⟩
  constructor
  · intro lower S covers
    let pre := S.preimage number number.injective.injOn
    let covering := pre.map (Function.Embedding.subtype active)
    have sizeBound : covering.card ≤ S.card := by
      change (pre.map (Function.Embedding.subtype active)).card ≤ S.card
      rw [Finset.card_map]
      have subset : pre.map number ⊆ S := by
        intro a ha
        obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 ha
        change u ∈ S.preimage number number.injective.injOn at hu
        exact Finset.mem_preimage.1 hu
      simpa only [Finset.card_map] using Finset.card_le_card subset
    have pullMem (u : Subtype active) (hu : number u ∈ S) : u.val ∈ covering := by
      change u.val ∈ pre.map (Function.Embedding.subtype active)
      apply Finset.mem_map.2
      refine ⟨u, ?_, rfl⟩
      change u ∈ S.preimage number number.injective.injOn
      exact Finset.mem_preimage.2 hu
    apply le_trans (lower covering ?_) sizeBound
    intro u v edge
    rcases covers _ _ (imageEdge edge) with hu | hv
    · exact Or.inl (pullMem ⟨u, ⟨v, edge⟩⟩ hu)
    · exact Or.inr (pullMem ⟨v, ⟨u, edge.symm⟩⟩ hv)
  · intro lower S covers
    let covering := (S.subtype active).map number
    have sizeBound : covering.card ≤ S.card := by
      change ((S.subtype active).map number).card ≤ S.card
      rw [Finset.card_map, Finset.card_subtype]
      exact Finset.card_filter_le S active
    apply le_trans (lower covering ?_) sizeBound
    intro a b edge
    obtain ⟨u, v, original, hu, hv⟩ := (corresponding a b).1 edge
    have ha : number ⟨u, ⟨v, original⟩⟩ = a := Fin.ext hu
    have hb : number ⟨v, ⟨u, original.symm⟩⟩ = b := Fin.ext hv
    rcases covers u v original with member | member
    · left
      rw [← ha]
      exact Finset.mem_map_of_mem number (Finset.mem_subtype.2 member)
    · right
      rw [← hb]
      exact Finset.mem_map_of_mem number (Finset.mem_subtype.2 member)
