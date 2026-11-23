import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormCoeffSeqExpDecayAtEveryCuspStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnFdImPowMulExp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuous

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem petInt_mp (γ : SL(2, ℤ)) : MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
  have h := measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  convert h using 1
  ext z
  simp

theorem petInt_emb (γ : SL(2, ℤ)) : MeasurableEmbedding (fun z : ℍ => γ • z) := by
  have h := measurableEmbedding_const_smul (α := ℍ) ((γ : GL (Fin 2) ℝ))
  convert h using 1
  ext z
  simp

theorem petInt_fd_meas : MeasurableSet ModularGroup.fd := by
  unfold ModularGroup.fd
  apply IsClosed.measurableSet
  apply IsClosed.inter
  · exact isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  · exact isClosed_le (continuous_abs.comp (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)) continuous_const

theorem petInt_im_bd (γ : SL(2, ℤ)) (σ : ℍ) (hσ : σ ∈ ModularGroup.fd) :
    (γ • σ).im ≤ 2 * σ.im ∧
      ((γ • σ).im)⁻¹ ≤ (3 * ((γ 1 0 : ℤ) : ℝ) ^ 2 + 8 * ((γ 1 1 : ℤ) : ℝ) ^ 2) * σ.im := by
  have hy : 3 ≤ 4 * σ.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hσ
  have hx : |σ.re| ≤ 1 / 2 := hσ.2
  have hyp : 0 < σ.im := σ.im_pos
  have hx2 : σ.re ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg σ.re, sq_abs σ.re]
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hcd : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 ∨ (((γ 1 0 : ℤ) : ℝ) = 0 ∧ ((γ 1 1 : ℤ) : ℝ) ^ 2 = 1) := by
    by_cases h0 : (γ 1 0 : ℤ) = 0
    · right
      rw [h0, mul_zero, sub_zero, mul_comm] at hdet
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;>
        simp [h0, h]
    · left
      have h1 : (1 : ℤ) ≤ (γ 1 0 : ℤ) ^ 2 := by
        rcases lt_or_gt_of_ne h0 with h | h <;> nlinarith
      exact_mod_cast h1
  have hN : Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) σ) =
      (((γ 1 0 : ℤ) : ℝ) * σ.re + ((γ 1 1 : ℤ) : ℝ)) ^ 2 + (((γ 1 0 : ℤ) : ℝ) * σ.im) ^ 2 := by
    rw [ModularGroup.denom_apply]
    simp [Complex.normSq_apply]
    ring
  rw [ModularGroup.im_smul_eq_div_normSq, hN]
  generalize ((γ 1 0 : ℤ) : ℝ) = c at *
  generalize ((γ 1 1 : ℤ) : ℝ) = d at *
  have hhalf : 1 / 2 ≤ (c * σ.re + d) ^ 2 + (c * σ.im) ^ 2 := by
    rcases hcd with h | ⟨hc, hd⟩
    · nlinarith [sq_nonneg (c * σ.re + d), mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ c ^ 2)]
    · subst hc
      nlinarith
  have hNpos : 0 < (c * σ.re + d) ^ 2 + (c * σ.im) ^ 2 := by linarith
  constructor
  · rw [div_le_iff₀ hNpos]
    nlinarith
  · rw [inv_div, div_le_iff₀ hyp]
    nlinarith [sq_nonneg (c * σ.re - d), mul_le_mul_of_nonneg_left hx2 (sq_nonneg c),
      mul_le_mul_of_nonneg_left hy (sq_nonneg c), mul_le_mul_of_nonneg_left hy (sq_nonneg d)]

theorem petInt_real (k A : ℕ) (r q f t y C C' K δ : ℝ) (hr1 : r ≤ 1) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (ht : 0 < t) (ht1 : t ≤ 2 * y) (ht2 : t⁻¹ ≤ K * y)
    (hdec : q ^ 2 * t ^ k ≤ C * Real.exp (-δ * y)) (hF : f ≤ C' * (t ^ A + (t ^ A)⁻¹)) :
    r * (q * f * t ^ k) ≤ C / 2 * (y ^ 0 * Real.exp (-(δ / 2) * y)) +
      (|C'| * (2 ^ A + K ^ A)) ^ 2 * 2 ^ k / 2 * (y ^ (2 * A + k) * Real.exp (-(δ / 2) * y)) := by
  have hy : 0 < y := by linarith
  have hKy : 0 < K * y := lt_of_lt_of_le (inv_pos.mpr ht) ht2
  set E := Real.exp (-(δ / 2) * y) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (-δ * y) = E * E := by
    rw [hE, ← Real.exp_add]
    ring_nf
  have htk : 0 < t ^ k := pow_pos ht k
  have hS : t ^ A + (t ^ A)⁻¹ ≤ (2 ^ A + K ^ A) * y ^ A := by
    have h1 : t ^ A ≤ (2 * y) ^ A := pow_le_pow_left₀ ht.le ht1 A
    have h2 : (t ^ A)⁻¹ ≤ (K * y) ^ A := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) ht2 A
    rw [mul_pow] at h1 h2
    linarith
  have hSpos : 0 ≤ t ^ A + (t ^ A)⁻¹ := by positivity
  have hf' : f ≤ |C'| * ((2 ^ A + K ^ A) * y ^ A) :=
    le_trans hF (le_trans (mul_le_mul_of_nonneg_right (le_abs_self C') hSpos)
      (mul_le_mul_of_nonneg_left hS (abs_nonneg _)))
  have hf2 : f ^ 2 ≤ (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) := by
    calc f ^ 2 ≤ (|C'| * ((2 ^ A + K ^ A) * y ^ A)) ^ 2 := pow_le_pow_left₀ hf hf' 2
      _ = (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) := by
        rw [mul_comm 2 A, pow_mul]
        ring
  have htk2 : t ^ k ≤ 2 ^ k * y ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ ht.le ht1 k
  have key : 2 * (q * f * t ^ k) * E ≤ (C * E + f ^ 2 * t ^ k * E) * E := by
    rw [hE2] at hdec
    nlinarith [mul_nonneg (sq_nonneg (q - f * E)) htk.le]
  have key2 : 2 * (q * f * t ^ k) ≤ C * E + f ^ 2 * t ^ k * E := le_of_mul_le_mul_right key hEpos
  have hft : f ^ 2 * t ^ k ≤ (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) * (2 ^ k * y ^ k) :=
    mul_le_mul hf2 htk2 htk.le (by positivity)
  have hP : 0 ≤ q * f * t ^ k := by positivity
  refine le_trans (mul_le_of_le_one_left hP hr1) ?_
  rw [pow_zero, one_mul, pow_add]
  nlinarith [mul_le_mul_of_nonneg_right hft hEpos.le]

theorem integrable_pet_integrand : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (ρ : ℍ → ℝ) (F : ℍ → ℂ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → CF k L' (ch ε) a → AEStronglyMeasurable F → Mod F → Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k)) := by
  intro k L L' N ε a ρ F hk hL' hN hW hCF hFm hMod
  set g : ℍ → ℂ := fun τ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k) with hg
  have hρ1 : ∀ τ, ρ τ ≤ 1 := by
    intro τ
    have h := le_hasSum (hW.sum τ) 1 (fun j _ => hW.nonneg _)
    simpa using h
  have hqc : Continuous (qs a) := (qs_summable_continuous a hCF.1.1).2
  have hgm : AEStronglyMeasurable g volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp hW.meas).aestronglyMeasurable
    · refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ hFm) ?_
      · exact (Complex.continuous_conj.comp hqc).aestronglyMeasurable
      · exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow k).aestronglyMeasurable
  obtain ⟨S, hS⟩ := hW.supp
  obtain ⟨C', A, hC'⟩ := hMod
  have hsupp : Function.support g ⊆ ⋃ γ ∈ S, {τ : ℍ | γ • τ ∈ ModularGroup.fd} := by
    intro τ hτ
    have hρ : ρ τ ≠ 0 := by
      intro h0
      apply hτ
      simp [hg, h0]
    obtain ⟨γ, hγS, hγ⟩ := hS τ hρ
    exact Set.mem_biUnion hγS hγ
  rw [← integrableOn_iff_integrable_of_support_subset hsupp, integrableOn_finset_iUnion]
  intro γ hγS
  have hpre : (fun σ : ℍ => γ⁻¹ • σ) ⁻¹' {τ : ℍ | γ • τ ∈ ModularGroup.fd} = ModularGroup.fd := by
    ext σ
    simp
  rw [← (petInt_mp γ⁻¹).integrableOn_comp_preimage (petInt_emb γ⁻¹), hpre]
  obtain ⟨C, δ, hδ, hdec⟩ := GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp k L' N ε a γ⁻¹ hk hL' hN hCF
  set K : ℝ := 3 * (((γ⁻¹ : SL(2, ℤ)) 1 0 : ℤ) : ℝ) ^ 2 + 8 * (((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ℝ) ^ 2 with hK
  refine Integrable.mono' (g := fun σ : ℍ => C / 2 * (σ.im ^ 0 * Real.exp (-(δ / 2) * σ.im)) +
      (|C'| * (2 ^ A + K ^ A)) ^ 2 * 2 ^ k / 2 * (σ.im ^ (2 * A + k) * Real.exp (-(δ / 2) * σ.im))) ?_ ?_ ?_
  · exact ((integrableOn_fd_im_pow_mul_exp (δ / 2) 0 (by positivity)).const_mul _).add
      ((integrableOn_fd_im_pow_mul_exp (δ / 2) (2 * A + k) (by positivity)).const_mul _)
  · exact (hgm.comp_measurePreserving (petInt_mp γ⁻¹)).restrict
  · refine (ae_restrict_iff' petInt_fd_meas).mpr (Filter.Eventually.of_forall fun σ hσ => ?_)
    have hy : 1 / 2 ≤ σ.im := by
      have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hσ
      nlinarith [σ.im_pos]
    obtain ⟨hb1, hb2⟩ := petInt_im_bd γ⁻¹ σ hσ
    have ht := (γ⁻¹ • σ).im_pos
    have hn : ‖g (γ⁻¹ • σ)‖ = ρ (γ⁻¹ • σ) * (‖qs a (γ⁻¹ • σ)‖ * ‖F (γ⁻¹ • σ)‖ * (γ⁻¹ • σ).im ^ k) := by
      simp only [hg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj,
        abs_of_nonneg (hW.nonneg _), abs_of_pos ht]
    rw [Function.comp_apply, hn]
    exact petInt_real k A _ _ _ _ σ.im C C' K δ (hρ1 _) (norm_nonneg _) (norm_nonneg _) ht hb1 hb2
      (hdec σ hy) (hC' _)

end GlobalTheory.EisM
