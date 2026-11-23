import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianVectorAnnihilatorEquations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffXMulOfNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalUnitMono
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtInvApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricBlockTraceInverseEqTwoMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianPhaseCriticalValueBlocksGeneral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianPairingMomentAlgebra

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.GaussInner

theorem pairing_mul_eq_exp {σ : Type} [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ)
    (E E' : MvPowerSeries σ ℂ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (hE : Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E‖ ^ 2))
    (hE' : Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E'‖ ^ 2))
    (h0 : MvPowerSeries.coeff 0 E = 1) (h0' : MvPowerSeries.coeff 0 E' = 1)
    (hd : ∀ l α, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E =
      MvPowerSeries.coeff α (x l • E + ∑ k, S l k • (MvPowerSeries.X k * E)))
    (hd' : ∀ l α, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E' =
      MvPowerSeries.coeff α (y l • E' + ∑ k, T l k • (MvPowerSeries.X k * E')))
    (D : ℝ → ℂ) (hD0 : D 0 = 1)
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧
      HasDerivAt D (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) * D t) t) :
    (∑' α : σ →₀ ℕ, (GlobalTheory.FockSeq.mfact α : ℂ) * MvPowerSeries.coeff α E * MvPowerSeries.coeff α E') * D 1 =
      Complex.exp (1 / 2 * (x ⬝ᵥ (1 - T * S)⁻¹ *ᵥ (y + T *ᵥ x) +
        y ⬝ᵥ (x + S *ᵥ ((1 - T * S)⁻¹ *ᵥ (y + T *ᵥ x))))) := by
  obtain ⟨hc, hm⟩ := moments σ S T x y E E' hE hE' hd hd'
  set f : ℝ → ℂ := fun s => ∑' α : σ →₀ ℕ, (s : ℂ) ^ α.degree *
    ((GlobalTheory.FockSeq.mfact α : ℂ) * MvPowerSeries.coeff α E * MvPowerSeries.coeff α E') with hf
  set w : ℝ → σ → ℂ := fun s => (1 - ((s : ℂ) ^ 2) • (T * S))⁻¹ *ᵥ (y + (s : ℂ) • T *ᵥ x) with hw
  set u : ℝ → σ → ℂ := fun s => x + (s : ℂ) • S *ᵥ w s with hu
  set Φ : ℝ → ℂ := fun s => (s : ℂ) / 2 * (x ⬝ᵥ w s + y ⬝ᵥ u s) with hΦ
  have hΦ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Φ (u t ⬝ᵥ w t) t := fun t ht =>
    GlobalTheory.Mem.GaussPhase.hasDerivAt_phase σ S T x y t hS hT (hD t ht).1
  have hg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun s => f s * D s * Complex.exp (-Φ s)) 0 t := by
    intro t ht
    have ht' := Set.Ioo_subset_Icc_self ht
    obtain ⟨p, q, m, n, h1, h2, h3, h4, h5⟩ := hm t ht
    have h6 := GlobalTheory.gaussian_pairing_moment_algebra σ S T x y t (f t) p q m n hS hT (hD t ht').1 h1 h2 h3 h4
    change _ = f t * (u t ⬝ᵥ w t + _) at h6
    rw [h6] at h5
    refine ((h5.fun_mul (hD t ht').2).fun_mul (hΦ' t ht').fun_neg.cexp).congr_deriv ?_
    ring
  have hgc : ContinuousOn (fun s => f s * D s * Complex.exp (-Φ s)) (Set.Icc 0 1) :=
    (hc.mul fun t ht => (hD t ht).2.continuousAt.continuousWithinAt).mul
      fun t ht => (hΦ' t ht).fun_neg.cexp.continuousAt.continuousWithinAt
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hgc hg
    intervalIntegrable_const
  have f0 : f 0 = 1 := by
    simp only [hf]
    rw [tsum_eq_single 0]
    · simp [h0, h0', GlobalTheory.FockSeq.mfact]
    · intro α hα
      have : α.degree ≠ 0 := fun h => hα ((Finsupp.degree_eq_zero_iff α).1 h)
      simp [this]
  have Φ0 : Φ 0 = 0 := by simp [hΦ]
  rw [f0, hD0, Φ0, intervalIntegral.integral_zero, Complex.exp_neg] at key
  have e : f 1 * D 1 = Complex.exp (Φ 1) := by
    have := Complex.exp_ne_zero (Φ 1)
    simp only [neg_zero, Complex.exp_zero, mul_one] at key
    field_simp at key
    linear_combination -key
  simpa [hf, hΦ, hu, hw] using e

theorem deriv_gauss {P Q : ℕ} (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (l : Ix P Q) (α : Ix P Q →₀ ℕ) :
    ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) (expPS (gaussPoly A x)) =
      MvPowerSeries.coeff α (x l • expPS (gaussPoly A x) +
        ∑ k, fromBlocks 0 A Aᵀ 0 l k • (MvPowerSeries.X k * expPS (gaussPoly A x))) := by
  rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x)]
  congr 1
  rcases l with i | j
  · rw [GlobalTheory.OscGauss.pderiv_inl_gaussPoly, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_sum]
    simp [Fintype.sum_sum_type, add_mul, Finset.sum_mul, MvPowerSeries.smul_eq_C_mul, mul_assoc]
  · rw [GlobalTheory.OscGauss.pderiv_inr_gaussPoly, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add, map_sum]
    simp [Fintype.sum_sum_type, add_mul, Finset.sum_mul, MvPowerSeries.smul_eq_C_mul, mul_assoc]

theorem posDef_smul {P Q : ℕ} {B : Matrix (Fin P) (Fin Q) ℂ} (hB : (1 - Bᴴ * B).PosDef) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : (1 - (((t : ℂ) ^ 2) • B)ᴴ * (((t : ℂ) ^ 2) • B)).PosDef := by
  have h4 : (0 : ℂ) ≤ ((1 - t ^ 4 : ℝ) : ℂ) :=
    Complex.zero_le_real.2 (sub_nonneg.2 (pow_le_one₀ ht.1 ht.2))
  have e : 1 - (((t : ℂ) ^ 2) • B)ᴴ * (((t : ℂ) ^ 2) • B) = (1 - Bᴴ * B) + ((1 - t ^ 4 : ℝ) : ℂ) • (Bᴴ * B) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : star ((t : ℂ) ^ 2) * (t : ℂ) ^ 2 = (t : ℂ) ^ 4 := by simp; ring
    rw [this]; push_cast; module
  rw [e]
  exact hB.add_posSemidef ((posSemidef_conjTranspose_mul_self B).smul h4)

theorem inner_gauss_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A B : Matrix (Fin P) (Fin Q) ℂ) (x y : Ix P Q → ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → ∀ v w : F.H, HasCoeff F v (expPS (gaussPoly A x)) → HasCoeff F w (expPS (gaussPoly B y)) → let a : Fin P → ℂ := fun i => star (x (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (x (Sum.inr j)); let c : Fin P → ℂ := fun i => y (Sum.inl i); let d : Fin Q → ℂ := fun j => y (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; inner ℂ v w = ((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c) := by
  intro P Q F A B x y hA hB v w hv hw a b c d M N
  obtain ⟨s1, hin⟩ := GlobalTheory.FockParseval.parseval _ F v w _ _ hv hw
  obtain ⟨s2, -⟩ := GlobalTheory.FockParseval.parseval _ F w w _ _ hw hw
  have hU : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det := fun t ht => by
    simpa only [Matrix.mul_smul] using
      GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions P Q A _ hA (posDef_smul hB ht)
  have hU1 : IsUnit (1 - Aᴴ * B).det := by simpa using hU 1 ⟨zero_le_one, le_rfl⟩
  have hy : y = Sum.elim c d := by ext (i | j) <;> rfl
  have key := pairing_mul_eq_exp (fromBlocks 0 Aᴴᵀ Aᴴ 0) (fromBlocks 0 B Bᵀ 0) (Sum.elim a b) y
    (MvPowerSeries.map (starRingEnd ℂ) (expPS (gaussPoly A x))) (expPS (gaussPoly B y))
    (by simp [fromBlocks_transpose]) (by simp [fromBlocks_transpose]) (by simpa using s1) s2
    (by rw [MvPowerSeries.coeff_map]; simp [expPS, MvPowerSeries.coeff_apply]) (by simp [expPS, MvPowerSeries.coeff_apply])
    (fun l α => by
      have := congrArg (starRingEnd ℂ) (deriv_gauss A x l α)
      rw [← MvPowerSeries.coeff_map (f := starRingEnd ℂ) (n := α)] at this
      rcases l with i | j <;>
        simpa [MvPowerSeries.smul_eq_C_mul, Fintype.sum_sum_type, a, b] using this)
    (deriv_gauss B y) (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det) (by simp)
    (fun t ht => GlobalTheory.FockDetDer.hasDerivAt_det_one_sub_sq P Q A B t (hU t ht))
  have hb := GlobalTheory.gaussian_phase_critical_value_blocks P Q A B a c b d hU1
  simp only [← hy] at hb
  rw [hb] at key
  simp only [MvPowerSeries.coeff_map, Complex.ofReal_one, one_pow, one_smul] at key
  rw [hin, ← key, mul_comm, mul_assoc, mul_inv_cancel₀ hU1.ne_zero, mul_one]

end GlobalTheory.GaussInner
