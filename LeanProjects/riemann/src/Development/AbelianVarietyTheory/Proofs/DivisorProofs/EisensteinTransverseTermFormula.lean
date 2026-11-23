import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinConstantTermRationalUnipotent
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

open GlobalTheory.EisCTMid in

theorem GlobalTheory.EisCTMid.midSumReal_left_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T → ∀ ν ∈ ratPts σ J, ν ∈ unipRad σ J (col0 X) → ∀ (s : ℝ) (g : GAd σ J),
      ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h (t.1.1 * (ν * g)) ^ s) =
        ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h (t.1.1 * g) ^ s) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS T hT ν hνr hνu s g
  have hx := witt_frame_first_column_ne_zero hS.2.2.2.2.1
  have hI := hS.2.2.2.2.2.2
  let μ : ratPts σ J := ⟨ν, hνr⟩
  refine (tsum_congr fun t => ?_).trans
    ((midEquiv hT μ hνu).tsum_eq (fun t => ENNReal.ofReal (h (t.1.1 * g) ^ s)))
  rw [show ν = (μ : GAd σ J) from rfl, rep_ht hI hx hT μ t.1 g]
  rfl
