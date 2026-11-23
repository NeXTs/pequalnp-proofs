import Mathlib.Data.List.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 :
    ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex,
      (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  let f := PEqualNP.MetaComplexity.CoverPromise.fresh φ
  refine ⟨Sum.inl (f, false), Sum.inl (f, true), ?_⟩
  change f = f ∧ false ≠ true ∧
    f ∈ PEqualNP.MetaComplexity.CoverPromise.vars (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ)
  refine ⟨rfl, by decide, ?_⟩
  simp [f, PEqualNP.MetaComplexity.CoverPromise.vars,
    PEqualNP.MetaComplexity.CoverPromise.cvcFormula, List.flatMap_append]
