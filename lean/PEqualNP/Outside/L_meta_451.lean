import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import PEqualNP.Defs

private theorem subdivisionRadixUnique
    {base a b r s : ℕ} (hr : r < base) (hs : s < base)
    (heq : base * a + r = base * b + s) : a = b ∧ r = s := by
  have below {lo hi dl dh : ℕ} (hlt : lo < hi) (hd : dl < base) :
      base * lo + dl < base * hi + dh := by
    have hmul := Nat.mul_le_mul_left base (show lo + 1 ≤ hi by omega)
    rw [Nat.mul_succ] at hmul
    omega
  have hab : a = b := by
    rcases lt_trichotomy a b with hlt | hequal | hgt
    · have hbad := below (dh := s) hlt hr
      omega
    · exact hequal
    · have hbad := below (dh := r) hgt hs
      omega
  subst b
  exact ⟨rfl, by omega⟩

private abbrev subdivisionVertexAt {m k : ℕ} (u v : Fin m) (p : ℕ)
    (x : Fin (m + 2 * k * (m * m))) : Prop :=
  (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
    (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)

private theorem subdivisionVertexUnique {m k : ℕ} {u v : Fin m} {p : ℕ}
    {x y : Fin (m + 2 * k * (m * m))}
    (hx : subdivisionVertexAt (k := k) u v p x)
    (hy : subdivisionVertexAt (k := k) u v p y) : x = y := by
  apply Fin.ext
  rcases hx with ⟨hxp, hxv⟩ | ⟨hxp, hxv⟩ | ⟨hxl, hxu, hxv⟩ <;>
    rcases hy with ⟨hyp, hyv⟩ | ⟨hyp, hyv⟩ | ⟨hyl, hyu, hyv⟩ <;> omega

private theorem subdivisionPositionUnique {m k : ℕ} {u v : Fin m} {p q : ℕ}
    {x : Fin (m + 2 * k * (m * m))} (huv : u < v)
    (hp : subdivisionVertexAt (k := k) u v p x)
    (hq : subdivisionVertexAt (k := k) u v q x) : p = q := by
  have huvVal : u.val < v.val := huv
  have hu := u.isLt
  have hv := v.isLt
  rcases hp with ⟨hpp, hpv⟩ | ⟨hpp, hpv⟩ | ⟨hpl, hpu, hpv⟩ <;>
    rcases hq with ⟨hqp, hqv⟩ | ⟨hqp, hqv⟩ | ⟨hql, hqu, hqv⟩ <;> omega

private theorem subdivisionInteriorUnique {m k : ℕ} {u v u' v' : Fin m} {p p' : ℕ}
    {x : Fin (m + 2 * k * (m * m))} (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2 * k)
    (hx : subdivisionVertexAt (k := k) u v p x)
    (hx' : subdivisionVertexAt (k := k) u' v' p' x) : u = u' ∧ v = v' ∧ p = p' := by
  have hval : x.val + 1 = m + 2 * k * (u.val * m + v.val) + p := by
    rcases hx with ⟨hpos, _⟩ | ⟨hpos, _⟩ | ⟨_, _, hi⟩
    · omega
    · omega
    · exact hi
  have hmin : m ≤ x.val := by omega
  rcases hx' with ⟨_, heq⟩ | ⟨_, heq⟩ | ⟨hp₁', hp₂', hval'⟩
  · have hbound := u'.isLt
    omega
  · have hbound := v'.isLt
    omega
  · have hcode :
        (2 * k) * (u.val * m + v.val) + (p - 1) =
          (2 * k) * (u'.val * m + v'.val) + (p' - 1) := by omega
    obtain ⟨hblock, hdigit⟩ := subdivisionRadixUnique
      (show p - 1 < 2 * k by omega) (show p' - 1 < 2 * k by omega) hcode
    have hblock' : m * u.val + v.val = m * u'.val + v'.val := by
      rw [Nat.mul_comm m u.val, Nat.mul_comm m u'.val]
      exact hblock
    obtain ⟨hu, hv⟩ := subdivisionRadixUnique v.isLt v'.isLt hblock'
    exact ⟨Fin.ext hu, Fin.ext hv, by omega⟩

private theorem subdivisionVertexExists {m k : ℕ} (u v : Fin m) (p : ℕ)
    (hp : p ≤ 2 * k + 1) :
    ∃ x : Fin (m + 2 * k * (m * m)), subdivisionVertexAt (k := k) u v p x := by
  have hu := u.isLt
  have hv := v.isLt
  by_cases hzero : p = 0
  · exact ⟨⟨u.val, by omega⟩, Or.inl ⟨hzero, rfl⟩⟩
  by_cases hlast : p = 2 * k + 1
  · exact ⟨⟨v.val, by omega⟩, Or.inr (Or.inl ⟨hlast, rfl⟩)⟩
  have hp₁ : 1 ≤ p := by omega
  have hp₂ : p ≤ 2 * k := by omega
  have hstride := Nat.mul_le_mul_right m (show u.val + 1 ≤ m by omega)
  rw [Nat.add_mul, Nat.one_mul] at hstride
  have hblock : u.val * m + v.val + 1 ≤ m * m := by omega
  have hend := Nat.mul_le_mul_left (2 * k) hblock
  rw [Nat.mul_add, Nat.mul_one] at hend
  let value := m + 2 * k * (u.val * m + v.val) + p - 1
  have hvalue : value < m + 2 * k * (m * m) := by
    dsimp only [value]
    omega
  refine ⟨⟨value, hvalue⟩, Or.inr (Or.inr ⟨hp₁, hp₂, ?_⟩)⟩
  change value + 1 = m + 2 * k * (u.val * m + v.val) + p
  dsimp only [value]
  omega

theorem PEqualNP.Outside.L_meta_451 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), u < v → H.Adj u v → 1 ≤ p → p ≤ 2 * k → Q u v p x → (S.neighborSet x).ncard = 2 := by
  intro m k H Q S positive hQ hAdj u v p x ordered edge interior lastInterior hx
  obtain ⟨previous, hPrevious⟩ := subdivisionVertexExists (k := k) u v (p - 1) (by omega)
  obtain ⟨following, hFollowing⟩ := subdivisionVertexExists (k := k) u v (p + 1) (by omega)
  have hPrev : Q u v (p - 1) previous := (hQ _ _ _ _).mpr hPrevious
  have hNext : Q u v (p + 1) following := (hQ _ _ _ _).mpr hFollowing
  have prevIndex : p - 1 + 1 = p := by omega
  have adjacentPrev : S.Adj x previous := by
    apply (hAdj _ _).mpr
    have atNext : Q u v (p - 1 + 1) x := by simpa only [prevIndex] using hx
    exact ⟨u, v, ordered, edge, p - 1, by omega, Or.inr ⟨hPrev, atNext⟩⟩
  have adjacentNext : S.Adj x following := by
    apply (hAdj _ _).mpr
    exact ⟨u, v, ordered, edge, p, lastInterior, Or.inl ⟨hx, hNext⟩⟩
  have distinct : previous ≠ following := by
    intro equal
    rw [← equal] at hFollowing
    have positions := subdivisionPositionUnique ordered hPrevious hFollowing
    omega
  have neighboring : S.neighborSet x = {previous, following} := by
    ext y
    change S.Adj x y ↔ y ∈ ({previous, following} : Set _)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro adjacent
      obtain ⟨a, b, _, _, r, _, positions⟩ := (hAdj _ _).mp adjacent
      have hxAt := (hQ _ _ _ _).mp hx
      rcases positions with ⟨sameX, sameY⟩ | ⟨sameY, sameX⟩
      · obtain ⟨sameA, sameB, sameR⟩ :=
          subdivisionInteriorUnique interior lastInterior hxAt ((hQ _ _ _ _).mp sameX)
        subst a
        subst b
        subst r
        exact Or.inr (subdivisionVertexUnique ((hQ _ _ _ _).mp sameY) hFollowing)
      · obtain ⟨sameA, sameB, sameR⟩ :=
          subdivisionInteriorUnique interior lastInterior hxAt ((hQ _ _ _ _).mp sameX)
        subst a
        subst b
        have rPrev : r = p - 1 := by omega
        rw [rPrev] at sameY
        exact Or.inl (subdivisionVertexUnique ((hQ _ _ _ _).mp sameY) hPrevious)
    · rintro (rfl | rfl)
      · exact adjacentPrev
      · exact adjacentNext
  rw [neighboring, Set.ncard_pair distinct]
