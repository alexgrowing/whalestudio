import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

theorem isFrameFam_mul_infMat_inv : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsFrameFam V ε fr → ∀ b : GA D V,
        IsFrameFam V ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) := by
  intro D θ hθ V ε fr h b τ
  have h1 : infMat D.sp.cm.sig V.gram (θ τ) b * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ = 1 := by
    rw [← Formalism.L2.Fam.ThC.infMat_mul, mul_inv_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have h2 : infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) b = 1 := by
    rw [← Formalism.L2.Fam.ThC.infMat_mul, inv_mul_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have hu : IsUnit (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹) := IsUnit.of_mul_eq_one _ h2
  have hinv : (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ = infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ :=
    Matrix.inv_eq_right_inv h1
  refine ⟨?_, ?_⟩
  · show IsUnit (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)
    rw [hinv]
    exact (h τ).1.mul hu
  · show (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)ᴴ * Formalism.REAL.Jm (ε τ) *
        (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) = _
    rw [hinv, Matrix.conjTranspose_mul]
    have e := GlobalTheory.Doubling.infMat_isometry (V := V) hθ τ b⁻¹
    rw [← (h τ).2] at e ⊢
    simpa only [Matrix.mul_assoc] using e

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
