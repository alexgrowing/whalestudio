import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ConjHol.ToLie

lemma conj_mem_sgn {n : ℕ} (d : Fin n → ℂ) (hd : ∀ a, star (d a) = d a)
    (A : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ * diagonal d + diagonal d * A = 0) :
    (A.map (starRingEnd ℂ))ᴴ * diagonal d + diagonal d * A.map (starRingEnd ℂ) = 0 := by
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.zero_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply] at hij ⊢
  have := congrArg star hij
  simp only [star_add, star_mul', star_star, star_zero, hd] at this
  simpa [RCLike.star_def, add_comm, mul_comm] using this

end GlobalTheory.AdSpan.ConjHol.ToLie

open GlobalTheory.AdSpan.ConjHol GlobalTheory.HolRead.AdExt in
theorem GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ Z ∈ GlobalTheory.HolRead.unitLie C.X, (∀ ρ, (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z ρ).1 = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) ∧ GlobalTheory.AdSpan.ConjHol.toLieC C R B (I • Z) = 0 := by
  intro D S T C R B hB Z hZ
  have hfix : ∀ ρ, conjAt T ρ (B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹)
      = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹ := by
    intro ρ
    have hW := GlobalTheory.AdSpan.ConjHol.ToLie.conj_mem_sgn _ ?_ _ (hZ (C.m.e ρ))
    · have hB' : (B ρ)ᴴ * gramAt D T ρ * B ρ = diagonal fun (a : Fin T.rank) => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ) := hB ρ
      have hL := conj_mem_lie (isUnit_det_B C hB ρ) hB' hW
      exact conj_eq_of_mem_lie (R.1 ρ).2 hL
    · intro a; simp
  refine ⟨fun ρ => ?_, ?_⟩
  · show ((HolRead.AdExt.toLie R B fun ρ => C.m.e ρ) (conjL Z) ρ).1 = _
    rw [toLie_val, mat_conjL, hfix ρ]
    module
  · funext ρ
    apply Subtype.ext
    show ((HolRead.AdExt.toLie R B fun ρ => C.m.e ρ) (conjL (I • Z)) ρ).1 = (0 : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    have hc : conjL (I • Z) = I • (-(conjL Z)) := by
      funext τ a b
      simp [conjL]
    have hm : mat (-(conjL Z)) (C.m.e ρ) = -(mat (conjL Z) (C.m.e ρ)) := rfl
    have hneg : ∀ M : Matrix (Fin T.rank) (Fin T.rank) ℂ,
        conjAt T ρ (B ρ * -M * (B ρ)⁻¹) = -(conjAt T ρ (B ρ * M * (B ρ)⁻¹)) := by
      intro M; simp [conjAt]
    rw [hc, toLie_I, hm, hneg, mat_conjL, hfix ρ]
    simp
