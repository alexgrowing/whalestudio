import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory
open scoped ComplexOrder

namespace Formalism.IndefR.Fock.Norm

open Formalism.IndefR.Fock.Sk Formalism.IndefR.Fock.CCR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem conj_inv_ofReal (x : ℝ) : starRingEnd ℂ ((x : ℂ)⁻¹) = (x : ℂ)⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

open Classical in
theorem fockNormO_of (hccr : CCRTheta D) (hnorm : FockNormAbs) (hskew : DRhoSkew D) (hint : ThetaIntO D)
    (hT : ThetaDRho D) : FockNormO D := by
  intro hLine ψ θ S T sS sT BS BT pS pT hP μ 𝓕 hcov f hf hvac P Q
  have hC := hccr hLine ψ θ S T sS sT BS BT pS pT hP
  have hstd := hP.std
  have hinf := hP.inf
  have hd : ∀ τ z F, IsThetaFunO ψ S T F → IsThetaFunO ψ S T (dRho (heisO ψ S T) θ τ z F) :=
    fun τ z F hF => (hT ψ θ hstd hinf hLine S T τ z F hF).1
  have hI := hint ψ hstd S T μ 𝓕 hcov

  set ip : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun F G => ∫ w in 𝓕, F w * starRingEnd ℂ (G w) ∂μ with hip
  have lin1 : ∀ F G H (a b : ℂ), IsThetaFunO ψ S T F → IsThetaFunO ψ S T G → IsThetaFunO ψ S T H →
      ip (a • F + b • G) H = a * ip F H + b * ip G H := by
    intro F G H a b hF hG hH
    simp only [hip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : (fun w => (a * F w + b * G w) * starRingEnd ℂ (H w)) =
        fun w => a * (F w * starRingEnd ℂ (H w)) + b * (G w * starRingEnd ℂ (H w)) := by
      funext w; ring
    rw [e, integral_add ((hI F H hF hH).const_mul a) ((hI G H hG hH).const_mul b), integral_const_mul,
      integral_const_mul]
  have lin2 : ∀ F G H (a b : ℂ), IsThetaFunO ψ S T F → IsThetaFunO ψ S T G → IsThetaFunO ψ S T H →
      ip H (a • F + b • G) = starRingEnd ℂ a * ip H F + starRingEnd ℂ b * ip H G := by
    intro F G H a b hF hG hH
    simp only [hip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : (fun w => H w * starRingEnd ℂ (a * F w + b * G w)) =
        fun w => starRingEnd ℂ a * (H w * starRingEnd ℂ (F w)) + starRingEnd ℂ b * (H w * starRingEnd ℂ (G w)) := by
      funext w; simp only [map_add, map_mul]; ring
    rw [e, integral_add ((hI H F hH hF).const_mul _) ((hI H G hH hG).const_mul _), integral_const_mul,
      integral_const_mul]
  have skew : ∀ τ z F G, IsThetaFunO ψ S T F → IsThetaFunO ψ S T G →
      ip (dRho (heisO ψ S T) θ τ z F) G = -ip F (dRho (heisO ψ S T) θ τ z G) := by
    intro τ z F G hF hG
    exact hskew ψ θ hstd hinf hLine S T τ z μ 𝓕 hcov F G hF hG
  have hsesq : IsSesq {F | IsThetaFunO ψ S T F} ip := by
    intro F G H c hF hG hH
    constructor
    · have := lin1 F G H 1 c hF hG hH
      simpa using this
    · have := lin2 F G H 1 c hF hG hH
      simpa using this
  refine hnorm {F | IsThetaFunO ψ S T F} _ _ f ip hC hf ?_ hsesq ?_ ?_ P Q
  · intro k
    funext x
    simp [aMinusAll, hvac k.1 _]
  · intro k F G hF hG
    rw [aMinusAll_eq, aPlusAll_eq, lin1 _ _ _ _ _ (hd _ _ F hF) (hd _ _ F hF) hG,
      lin2 _ _ _ _ _ (hd _ _ G hG) (hd _ _ G hG) hF, skew _ _ _ _ hF hG, skew _ _ _ _ hF hG]
    simp only [map_mul, map_neg, conj_inv_ofReal, Complex.conj_I]
    ring
  · intro k F G hF hG
    rw [aMinusAll_eq, aPlusAll_eq, lin1 _ _ _ _ _ (hd _ _ F hF) (hd _ _ F hF) hG,
      lin2 _ _ _ _ _ (hd _ _ G hG) (hd _ _ G hG) hF, skew _ _ _ _ hF hG, skew _ _ _ _ hF hG]
    simp only [map_mul, map_neg, conj_inv_ofReal, Complex.conj_I]
    ring

end Formalism.IndefR.Fock.Norm

end
