import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.ContinuousLev

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem height_lv {K : Type} [Field K] [NumberField K] (m₁ m₂ : G1 K 2) :
    AutomorphicForm.height ((lv m₁ m₂ 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ≤ heightConst K (2 + 2) *
      AutomorphicForm.height (m₁ : AdelicGLn.AdelicGL K 2) * AutomorphicForm.height (m₂ : AdelicGLn.AdelicGL K 2) := by
  have z : zt K 0 = 1 := by
    rw [zt, ← map_one (centralSection K 2)]
    congr 1
    exact Subtype.ext Real.exp_zero
  have hs : ∀ r s : ℕ, GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv := fun r s => by
    ext (x | x) <;> simp
  rw [(blkLaws (K := K)).1, neg_zero, z, mul_one, mul_one]
  refine le_of_eq_of_le (congrArg _ (Units.ext ?_)) (UpperTheory.ConvolutionTheory.BW.Pair.height_lev (E := K) (r := 2) (s := 2) m₁ m₂)
  rw [GlobalTheory.CompanionTheory.CTFin.lev, GlobalTheory.SmGL.val_emb₂, hs]
  rfl

private theorem near {K : Type} [Field K] [NumberField K] {n : ℕ} (m : G1 K n) :
    ∃ γ ∈ Gam K n, AutomorphicForm.height ((γ * m : G1 K n) : AdelicGLn.AdelicGL K n) ≤ 2 * qht m := by
  have h1 := UpperTheory.ConvolutionTheory.BW.Pair.one_le_qht m
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (show qht m < 2 * qht m by linarith)
  exact ⟨γ, γ.2, hγ.le⟩

private theorem num {c x y g a b p q R : ℝ} (hc : 0 ≤ c) (h1 : x ≤ c * y * g) (h2 : y ≤ c * a * b) (h3 : a ≤ 2 * p)
    (h4 : b ≤ 2 * q) (h5 : g ≤ R) (hb : 0 ≤ b) (hg : 0 ≤ g) (hp : 0 ≤ p) (hq : 0 ≤ q) : x ≤ c * c * 4 * R * (p * q) := by
  refine h1.trans ((mul_le_mul (mul_le_mul_of_nonneg_left (h2.trans
    (mul_le_mul (mul_le_mul_of_nonneg_left h3 hc) h4 hb (by positivity))) hc) h5 hg (by positivity)).trans (le_of_eq ?_))
  ring

private theorem num2 {x y w B A p q C D : ℝ} {M : ℕ} (h : w ≤ B * (A * (p * q)) ^ M) (h1 : x * p ^ M ≤ C) (h2 : y * q ^ M ≤ D)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 ≤ p) (hq : 0 ≤ q) (hB : 0 ≤ B) (hA : 0 ≤ A) : x * y * w ≤ B * A ^ M * (C * D) :=
  calc _ ≤ x * y * (B * (A * (p * q)) ^ M) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = B * A ^ M * (x * p ^ M * (y * q ^ M)) := by rw [mul_pow, mul_pow p]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)) (by positivity)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.ctBd :
    ∀ {K : Type} [Field K] [NumberField K] (Φ W : G1 K (2 + 2) → ℂ) (φ₁ φ₂ : G1 K 2 → ℂ), Continuous Φ →
      (∃ (N : ℕ) (C : ℝ), ∀ g : G1 K (2 + 2), ‖Φ g‖ ≤ C * AutomorphicForm.height (g : AdelicGLn.AdelicGL K (2 + 2)) ^ N) →
      (∀ g, W g = ∫ X in unipFundamentalDomain K (2 + 2) 2, Φ (nn X * g) ∂unipMeasure K (2 + 2) 2) →
      (∀ γ₁ ∈ Gam K 2, ∀ γ₂ ∈ Gam K 2, ∀ g, W (lv γ₁ γ₂ 0 * g) = W g) →
      (∀ N : ℕ, ∃ C : ℝ, ∀ m, ‖φ₁ m‖ * qht m ^ N ≤ C) → (∀ N : ℕ, ∃ C : ℝ, ∀ m, ‖φ₂ m‖ * qht m ^ N ≤ C) →
      Continuous W ∧ ∀ C : Set (G1 K (2 + 2)), IsCompact C → ∃ B : ℝ, ∀ m₁ m₂, ∀ g ∈ C, ‖φ₁ m₁‖ * ‖φ₂ m₂‖ * ‖W (lv m₁ m₂ 0 * g)‖ ≤ B := by
  intro K _ _ Φ W φ₁ φ₂ hc ⟨N, C, hN⟩ hW hrat h₁ h₂
  classical
  constructor
  · have e : W = fun g : G1 K (2 + 2) => constantTerm 2 (fun x => Φ (retractOne x)) (g : AdelicGLn.AdelicGL K (2 + 2)) := by
      funext g
      rw [hW]
      refine integral_congr_ae (Eventually.of_forall fun X => ?_)
      exact congrArg Φ (retractOne_coe (nn X * g)).symm
    rw [e]
    exact (UpperTheory.continuous_constantTerm K _ 2 _ (hc.comp continuous_retractOne)).comp continuous_subtype_val
  · intro D hD
    obtain ⟨B, M, hB⟩ := UpperTheory.hasModerateGrowth_constantTerm K (2 + 2) 2 (fun x => if h : x ∈ normOneGL K (2 + 2) then Φ ⟨x, h⟩ else 0)
      ⟨|C|, N, fun g => by
        have hp := pow_nonneg (height_pos g).le N
        beta_reduce
        split_ifs with h
        · exact (hN ⟨g, h⟩).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
        · rw [norm_zero]
          positivity⟩
    have hB' : ∀ g : G1 K (2 + 2), ‖W g‖ ≤ |B| * AutomorphicForm.height (g : AdelicGLn.AdelicGL K (2 + 2)) ^ M := fun g => by
      refine le_of_eq_of_le (congrArg _ ?_) ((hB g).trans
        (mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg (height_pos _).le M)))
      rw [hW]
      refine integral_congr_ae (Eventually.of_forall fun X => ?_)
      have h : unipGL X * (g : AdelicGLn.AdelicGL K (2 + 2)) ∈ normOneGL K (2 + 2) := (nn X * g).2
      beta_reduce
      rw [dif_pos h]
      rfl
    obtain ⟨R, hR⟩ := exists_height_le_of_isCompact (hD.image continuous_subtype_val)
    obtain ⟨C₁, hC₁⟩ := h₁ M
    obtain ⟨C₂, hC₂⟩ := h₂ M
    have h0 : 0 ≤ heightConst K (2 + 2) := zero_le_one.trans one_le_heightConst
    obtain ⟨c, hc'⟩ : ∃ c, c = heightConst K (2 + 2) := ⟨_, rfl⟩
    refine ⟨|B| * (c * c * 4 * |R|) ^ M * (C₁ * C₂), fun m₁ m₂ g hg => ?_⟩
    obtain ⟨γ₁, hγ₁, e₁⟩ := near m₁
    obtain ⟨γ₂, hγ₂, e₂⟩ := near m₂
    have q₁ := zero_le_one.trans (UpperTheory.ConvolutionTheory.BW.Pair.one_le_qht m₁)
    have q₂ := zero_le_one.trans (UpperTheory.ConvolutionTheory.BW.Pair.one_le_qht m₂)
    have e3 : AutomorphicForm.height ((lv (γ₁ * m₁) (γ₂ * m₂) 0 * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ≤
        c * c * 4 * |R| * (qht m₁ * qht m₂) := by
      have a1 := height_mul_le ((lv (γ₁ * m₁) (γ₂ * m₂) 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) g
      have a2 := height_lv (γ₁ * m₁) (γ₂ * m₂)
      have a3 : AutomorphicForm.height (g : AdelicGLn.AdelicGL K (2 + 2)) ≤ |R| := (hR _ ⟨g, hg, rfl⟩).trans (le_abs_self R)
      rw [← hc'] at a1 a2 h0
      rw [Subgroup.coe_mul]
      exact num h0 a1 a2 e₁ e₂ a3 (height_pos _).le (height_pos _).le q₁ q₂
    have e4 : ‖W (lv m₁ m₂ 0 * g)‖ ≤ |B| * (c * c * 4 * |R| * (qht m₁ * qht m₂)) ^ M := by
      rw [← hrat γ₁ hγ₁ γ₂ hγ₂, ← mul_assoc, (blkLaws (K := K)).2.1, add_zero]
      exact (hB' _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le e3 M) (abs_nonneg B))
    exact num2 e4 (hC₁ m₁) (hC₂ m₂) (norm_nonneg _) (norm_nonneg _) q₁ q₂ (abs_nonneg B)
      (mul_nonneg (mul_nonneg (mul_self_nonneg c) (by norm_num)) (abs_nonneg R))
