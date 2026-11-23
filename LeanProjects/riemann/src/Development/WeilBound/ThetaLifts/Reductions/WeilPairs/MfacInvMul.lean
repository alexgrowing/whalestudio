import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoAlt
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitCoef
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.NormModulusHeisenberg

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem heisOF_zero (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (f : WOF F E nS nT → ℂ) : heisOF σ JS JT ξ₀ ψ 0 f = f := by
  funext w
  simp [heisOF, symplOHF, symplOF, hOF]

theorem nrm_zero (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (f : WOF F E nS (nT + nT) → ℂ) :
    nrm σ JS JT ξ₀ ψ ν 𝓕 f 0 = ((‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖ ^ 2 : ℝ) : ℂ) := by
  unfold nrm
  rw [Matrix.mul_zero, heisOF_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem mfac_inv_mul {nT : ℕ} (nS : ℕ) (t : GL (Fin nT) (AF F ⊗[F] E)) :
    mfac F E nS t⁻¹ * mfac F E nS t = 1 := by
  unfold mfac
  rw [← Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), ← NNReal.coe_mul, ← map_mul, ← map_mul, ← map_mul,
    inv_mul_cancel, map_one, map_one, map_one, NNReal.coe_one, Real.one_rpow]

theorem mfac_pos' {nT : ℕ} (nS : ℕ) (t : GL (Fin nT) (AF F ⊗[F] E)) : 0 < mfac F E nS t := by
  unfold mfac
  refine Real.rpow_pos_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 fun h0 => ?_)) _
  have := map_mul (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t)) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t))⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at this
  exact one_ne_zero this

end PositivityTheory.ThKW.NormModulusHeisenberg

end

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.NormModulusHeisenberg in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ =
          mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hht f hf
  obtain ⟨μW, 𝓕W, κ, hμW, h𝓕W, hκ, hcoef⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.coef F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕
  have hωf := hωd.om_pres (1, h) f hf
  obtain ⟨c1, i1, e1⟩ := hcoef _ hωf
  obtain ⟨c0, i0, e0⟩ := hcoef f hf
  obtain ⟨cL, iL, eL⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.change F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 t _ c0 i0
  have hκ0 : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ.ne'
  have key : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (ωd (1, h) f) = fun w =>
      ((mfac F E nS t : ℝ) : ℂ) ^ 2 * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f ((t.1.map (cAF σ))ᵀ * w) := by
    refine PositivityTheory.ThKW.PhaseFourierInjectivity.finj F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 _ _ c1 (continuous_const.mul cL) i1
      (iL.const_mul _) fun y => ?_
    have hact : actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) = dC (AF F ⊗[F] E) nT * y := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 by unfold mtF; rw [map_one, Units.val_one], Matrix.mul_one,
        ← Matrix.mul_assoc, hht, Matrix.mul_assoc, ← Matrix.mul_assoc t.1, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    have u := PositivityTheory.ThKW.PhaseFourierInjectivity.unit_coef F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS ωd hωd μW 𝓕W hμW h𝓕W h
      (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) f hf
    rw [hact, e1 y, e0 ((t⁻¹).1 * y), eL y] at u
    have u' := mul_left_cancel₀ hκ0 u
    rw [u', ← integral_const_mul]
    congr 1
    funext w
    ring
  have k0 := congrFun key 0
  rw [Matrix.mul_zero, nrm_zero, nrm_zero] at k0
  have k1 : ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ ^ 2 =
      (mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖) ^ 2 := by
    rw [mul_pow]
    exact_mod_cast k0
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (mfac_pos' nS t).le (norm_nonneg _)) two_ne_zero).1 k1
