import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.SiegelSet

theorem isRealLine_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∀ s t, γ (s + t) = γ s * γ t := by
  intro F E _ _ _ _ _ σ hCM n J γ hγ s t
  obtain ⟨w, τ, Z, -, hγ⟩ := hγ
  obtain ⟨y1, e1, f1⟩ := hγ (s + t)
  obtain ⟨y2, e2, f2⟩ := hγ s
  obtain ⟨y3, e3, f3⟩ := hγ t
  rw [e1, e2, e3, ← map_mul]
  congr 1
  apply (archEquiv J hCM τ).injective
  apply Subtype.ext
  apply Units.ext
  rw [← GlobalTheory.Orb.archMat_eq_archEquiv, ← GlobalTheory.Orb.archMat_eq_archEquiv, map_mul, f1, f2, f3, add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl Z).smul_left s |>.smul_right t)

end GlobalTheory.SiegelSet
