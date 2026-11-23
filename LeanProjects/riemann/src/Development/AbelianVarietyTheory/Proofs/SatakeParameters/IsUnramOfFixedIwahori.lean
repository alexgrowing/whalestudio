import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaAndZelevinskyPolynomialRing
open GlobalTheory.LocGL GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RoadU

namespace GlobalTheory.IwahoriSupport

theorem hasSupport_chars {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) k) V} (hi : ρ.IsIrreducible) (χ : Fin n → kˣ →* ℂˣ)
    (hχ : ∀ i, IsSmoothChar (χ i)) (h : GlobalTheory.SmGL.IsSubquotient ρ (prinSeries χ)) :
    HasSupport ρ (chars χ hχ) := by
  have H : GlobalTheory.SmGL.IsCuspSupport ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (χ a) :=
    ⟨hi, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      h.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ)⟩
  exact hasSupport_of_isCuspSupport H

end GlobalTheory.IwahoriSupport
