import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemOfFiniteDimensionalSpanRightTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePointsStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryCoordinateAlgebraDenseStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem rightFinite_mem_poly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (f : infU E n → ℂ), Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => fun x : infU E n => f (x * k))) → f ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} := by
  intro E _ _ _ n f hf hfin
  haveI := GlobalTheory.T.compactSpace_definiteUnitaryInfinitePoints E n
  obtain ⟨hc, hs, hsep, hinv, hcop⟩ := GlobalTheory.T.unitary_coordinate_algebra_dense E n
  haveI : T2Space (infU E n) := ⟨fun x y hxy => by
    obtain ⟨p, hp, hne⟩ := hsep x y hxy
    exact separated_by_continuous (hc p hp) hne⟩
  refine GlobalTheory.T.mem_of_finiteDimensional_span_rightTranslates' (infU E n) (Algebra.adjoin ℂ _) hc hs hsep ?_ f hf hfin
  intro p hp
  obtain ⟨m, a, b, hab, heq⟩ := hcop p hp
  refine ⟨m, fun i x => a i x⁻¹, b, fun i => ⟨hinv _ (hab i).1, hc _ (hab i).2⟩, ?_⟩
  intro x k
  exact heq x⁻¹ k

end GlobalTheory.UnitaryBC
