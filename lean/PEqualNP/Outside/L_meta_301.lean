import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_301 :
    ∀ (k : ℕ) (c : ℕ → Bool),
      (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) →
      k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤
        ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k c cover
  let missed : Prop := c 0 = false ∧ c (2 * k + 1) = false
  let offset : ℕ := if missed then 0 else 1
  let count : ℕ := k + (if missed then 1 else 0)
  let start (i : ℕ) : ℕ := 2 * i + offset
  let pick (i : ℕ) : ℕ := if c (start i) = true then start i else start i + 1
  have bounds (i : ℕ) : start i ≤ pick i ∧ pick i ≤ start i + 1 := by
    dsimp [pick]
    split <;> constructor <;> omega
  have injective : Function.Injective pick := by
    intro i j equal
    have hi := bounds i
    have hj := bounds j
    dsimp only [start] at hi hj
    omega
  have selected (i : ℕ) (hi : i < count) : c (pick i) = true := by
    have hstart : start i ≤ 2 * k := by
      by_cases hmiss : missed <;> simp [start, count, offset, hmiss] at hi ⊢ <;> omega
    by_cases hc : c (start i) = true
    · simp [pick, hc]
    · simpa [pick, hc] using (cover (start i) hstart).resolve_left hc
  have inner (i : ℕ) (hi : i < count) :
      pick i ∈ (Finset.Icc 1 (2 * k)).filter (fun j => c j = true) := by
    have hc := selected i hi
    have hp := bounds i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨?_, hc⟩
    dsimp only [start] at hp
    by_cases hmiss : missed
    · have hends : c 0 = false ∧ c (2 * k + 1) = false := hmiss
      have hfirst : pick i ≠ 0 := by
        intro hfirst
        simp [hfirst, hends.1] at hc
      have hlast : pick i ≠ 2 * k + 1 := by
        intro hlast
        simp [hlast, hends.2] at hc
      simp [offset, count, hmiss] at hp hi
      constructor <;> omega
    · simp [offset, count, hmiss] at hp hi
      constructor <;> omega
  have subset : (Finset.range count).image pick ⊆
      (Finset.Icc 1 (2 * k)).filter (fun j => c j = true) := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact inner i (Finset.mem_range.mp hi)
  have bound := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ injective, Finset.card_range] at bound
  exact bound
