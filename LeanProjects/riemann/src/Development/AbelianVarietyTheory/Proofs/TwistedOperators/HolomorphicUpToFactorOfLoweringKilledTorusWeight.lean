import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTorusEquivariantOrthonormalFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFramesOfKilledNilpotentDerivativStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelUnitFramesEqMovedOrthonormalFramesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactTorusProductRealPlacesSpecStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceDeterminantPowerMulNeZeroExpStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceDeterminantPowerMulCompactTorusElementStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFrameToRealLieAlgebraSpecStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FderivConjFrameToRealLieLoweringOperatorEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedTraceConjFrameToRealLieLoweringOperatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

open GlobalTheory.HolRead in

theorem holUpTo_of_lowKilled : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (la : Wt C.X.Ψ T.rank) (m : D.what₂.Tau → ℤ) (φ : GA D T → ℂ), LowKilled C.θ T B φ → (∀ (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T), φ (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ - la (C.m.e ρ) a : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * φ g) → HolUpTo C B la (detPow C.θ T m) φ := by
  intro D S T C B hB la m φ hL htor g
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  obtain ⟨U1, U2, U3⟩ := GlobalTheory.T.conjugateModel_unitFrames_eq_movedOrthonormalFrames D S T C B hB
  obtain ⟨dMul, dNe, dExp⟩ := GlobalTheory.T.realPlaceDeterminantPower_mul_ne_zero_exp D C.θ C.inf T m
  let F : Frame C.X.Ψ T.rank → ℂ := fun y =>
    if h : IsUnitFr C.X y then φ (g * (U2 y h).choose) / detPow C.θ T m (U2 y h).choose else 0
  have hF : ∀ a ∈ GinfC T, F (C.xB (C.mvB a B)) = φ (g * a) / detPow C.θ T m a := by
    intro a ha
    have hy := U1 a
    simp only [F, dif_pos hy]
    rw [U3 _ (U2 _ hy).choose_spec.1 a ha (U2 _ hy).choose_spec.2]
  obtain ⟨Q, Q1, Q2⟩ := GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames _ _ C.X la F (by
    intro y hy t
    obtain ⟨a, ha, rfl⟩ := U2 y hy
    let s : D.what₂.Tau → Fin T.rank → ℝ := fun ρ c => -t (C.m.e ρ) c
    obtain ⟨hk, hk2⟩ := GlobalTheory.T.compactTorusProductRealPlaces_spec D S T C B hB s
    have e1 := xB_mvB_mul C B hB a (torProd C.θ T B s) (fun τ => diagonal fun c => cexp ((t τ c : ℂ) * I)) fun ρ => ?_
    · erw [← e1]
      rw [hF _ (mul_mem ha hk), hF a ha, ← mul_assoc,
      apply_mul_torProd C.θ T B _ φ htor, apply_mul_torProd C.θ T B _ _ (GlobalTheory.T.realPlaceDeterminantPower_mul_compactTorusElement D S T C B hB m)]
      have hb : (bchar la fun τ => (diagonal fun c => cexp ((t τ c : ℂ) * I) : Matrix (Fin T.rank) (Fin T.rank) ℂ)) =
          cexp (((∑ ρ, ∑ c, ((la (C.m.e ρ) c : ℝ)) * t (C.m.e ρ) c : ℝ) : ℂ) * I) := by
        unfold bchar
        rw [← Equiv.prod_comp C.m.e]
        push_cast
        rw [Finset.sum_mul, Complex.exp_sum]
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [Finset.sum_mul, Complex.exp_sum]
        refine Finset.prod_congr rfl fun c _ => ?_
        rw [diagonal_apply_eq, ← Complex.exp_int_mul, mul_assoc]
      have hA : cexp (((∑ ρ, ∑ c, ((m ρ - la (C.m.e ρ) c : ℤ) : ℝ) * s ρ c : ℝ) : ℂ) * I) =
          cexp (((∑ ρ, ∑ c, ((m ρ : ℤ) : ℝ) * s ρ c : ℝ) : ℂ) * I) *
            cexp (((∑ ρ, ∑ c, ((la (C.m.e ρ) c : ℝ)) * t (C.m.e ρ) c : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add, ← add_mul]
        congr 2
        rw [← Complex.ofReal_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [s]; push_cast; ring
      rw [hb, hA]
      field_simp [dNe a, Complex.exp_ne_zero]
    · rw [hk2]
      show _ = B ρ * (diagonal fun c => cexp ((t (C.m.e ρ) c : ℂ) * I)).map (starRingEnd ℂ) * (B ρ)⁻¹
      rw [diagonal_map (map_zero _)]
      congr 3
      funext c
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      simp only [s]; push_cast; ring_nf)
  have hQ : ∀ a ∈ GinfC T, Q (C.xB (C.mvB a B)) = φ (g * a) / detPow C.θ T m a := fun a ha => by
    rw [Q1 _ (U1 a), hF a ha]
  refine ⟨Q, GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative _ _ C.X la Q Q2 fun y hy => ?_, Q2, fun a ha => ?_⟩
  swap
  · rw [hQ a ha]; field_simp [dNe a]
  obtain ⟨a, ha, rfl⟩ := U2 y hy
  have hs : DifferentiableAt ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 :=
    (((GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 hL.1) (g * a)).differentiable
      (by simp)) 0
  let L : Frame C.X.Ψ T.rank →L[ℝ] GlobalTheory.SmoothForms.LieN T := LinearMap.toContinuousLinearMap (toLieC C R B)
  let lam : GlobalTheory.SmoothForms.LieN T →L[ℝ] ℂ := trCL T m
  let f : GlobalTheory.SmoothForms.LieN T → ℂ := fun Y =>
    (detPow C.θ T m a)⁻¹ * (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y) * cexp (-lam Y))
  have key : ∀ Z ∈ unitLie C.X, Q (rmul (C.xB (C.mvB a B)) (expFr Z)) = f (L Z) := by
    intro Z hZ
    have he := GlobalTheory.SmoothForms.isExpFam_expInf R (L Z)
    rw [← xB_mvB_mul C B hB a _ _ fun ρ => ?_, hQ _ (mul_mem ha he.1), dMul, dExp]
    · simp only [f, lam, trCL_apply, mul_assoc, Complex.exp_neg]
      field_simp [dNe a]
    · show infMat _ _ (C.θ ρ) _ = _
      rw [he.2 ρ]
      change NormedSpace.exp ((toLieC C R B Z ρ).1) = _
      rw [(GlobalTheory.T.conjFrameToRealLieAlgebra_spec D S T C R B hB Z hZ).1 ρ,
        Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det _).2 (isUnit_det_B C hB ρ))]
      congr 2
      exact (exp_map_conj _).symm
  have h0 : (0 : Frame C.X.Ψ T.rank) ∈ unitLie C.X := fun τ => by
    have : mat (0 : Frame C.X.Ψ T.rank) τ = 0 := rfl
    simp [this]
  let Dφ := fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0
  have hE : HasFDerivAt (fun Y : GlobalTheory.SmoothForms.LieN T => cexp (-lam Y)) (cexp (-lam 0) • -lam) 0 :=
    lam.hasFDerivAt.neg.cexp
  have hfd := (hs.hasFDerivAt.mul hE).const_mul (detPow C.θ T m a)⁻¹
  have hfd' : HasFDerivAt f ((detPow C.θ T m a)⁻¹ • (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) •
      (cexp (-lam 0) • -lam) + cexp (-lam 0) • Dφ)) (L 0) := by
    have h0L : L 0 = 0 := map_zero L
    rw [h0L]; exact hfd
  refine ⟨_ , (hfd'.comp (0 : Frame C.X.Ψ T.rank) L.hasFDerivAt).hasFDerivWithinAt.congr key (key 0 h0), ?_⟩
  intro τ c d hcd Z hZ Z' hZ' e
  obtain ⟨ρ, rfl⟩ := C.m.e.surjective τ
  have hD := GlobalTheory.T.fderiv_conjFrameToRealLie_loweringOperator_eq_zero D S T C R B hB φ hL (g * a) ρ c d hcd Z Z' hZ hZ' e
  have hT := GlobalTheory.T.weightedTrace_conjFrameToRealLie_loweringOperator D S T C R B hB m ρ c d hcd Z Z' hZ hZ' e
  have hℓ : ∀ W : Frame C.X.Ψ T.rank, ((detPow C.θ T m a)⁻¹ • (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) •
      (cexp (-lam 0) • -lam) + cexp (-lam 0) • Dφ)).comp L W = (detPow C.θ T m a)⁻¹ *
      (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) * (cexp (-lam 0) * -trLin T m (toLieC C R B W)) +
        cexp (-lam 0) * Dφ (toLieC C R B W)) := fun W => rfl
  rw [hℓ, hℓ]
  linear_combination ((detPow C.θ T m a)⁻¹ * cexp (-lam 0)) * hD -
    ((detPow C.θ T m a)⁻¹ * φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) * cexp (-lam 0)) * hT

end GlobalTheory.AdSpan.ConjHol
