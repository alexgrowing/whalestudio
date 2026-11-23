import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.LinTheta

theorem infPart_of_isSplitIdem {D : D7} {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, hε, -, -⟩, h3⟩ := he
  have h4 : e = e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← h3, mul_add, h1, h2, add_zero]
  have h5 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    have h6 : fstA D.host.F ε = 0 := by rw [hε]; rfl
    simp [infPart, Algebra.TensorProduct.algebraMap_apply, h6]
  rw [h4, map_mul, h5, mul_zero]

theorem isThetaFunO_placeModel (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (ΛS : Lat S) (ΛT : Lat T)
    (e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : IsSplitIdem D e) (hf : IsThetaFunO ψ S T f₀)
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm)
    (Φ : WO S T → ℂ)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) Φ) : IsThetaFunO ψ S T (Tm Φ) :=
  GlobalTheory.DiagLiftFix.isTheta_placeModel hψ hS.1 hT.1 he.1 he.2.1 (infPart_of_isSplitIdem he) hf Tm hTm Φ hΦ

end GlobalTheory.LocMod.LinTheta
