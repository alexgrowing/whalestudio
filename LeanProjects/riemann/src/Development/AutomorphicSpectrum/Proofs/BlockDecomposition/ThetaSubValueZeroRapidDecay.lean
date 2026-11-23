import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLeNormInfCModuleSectionMul
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailFurther
set_option maxSynthPendingDepth 1

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap nonZeroDivisors Pointwise
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis
  GlobalTheory.CompanionTheory.EisRk1

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisThCDecay

noncomputable section

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mulVec_scalC_mul (a : IdeleGroup k) (h : GL ι 𝔸[k]) (v : ι → 𝔸[k]) :
    ((scalC a * h : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ v =
      (a : 𝔸[k]) • ((h : Matrix ι ι 𝔸[k]) *ᵥ v) := by
  have h1 : ∀ x : ι → 𝔸[k], ((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ x = (a : 𝔸[k]) • x := by
    intro x
    funext i
    have : ((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = Matrix.scalar ι (a : 𝔸[k]) := rfl
    rw [this, Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rfl
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]

theorem apply_eq_of_mulVec (h : GL ι 𝔸[k]) (v : ι → 𝔸[k]) (j : ι) :
    v j = ∑ i, ((h⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i * ((h : Matrix ι ι 𝔸[k]) *ᵥ v) i := by
  have h1 : ((h⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ((h : Matrix ι ι 𝔸[k]) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  conv_lhs => rw [← h1]
  simp only [Matrix.mulVec, dotProduct]

omit [DecidableEq ι] in

theorem summable_prod_coord {f : k → ℝ} (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) :
    Summable fun ξ : ι → k ↦ ∏ i, f (ξ i) :=
  _root_.UpperTheory.Reformulated.B.Yva3.main hf h0

omit [DecidableEq ι] in

theorem decay_real_bound {A B Z t κ : ℝ} {X : ι → ℝ} {m n r : ℕ} (hA : 0 ≤ A) (hB : 0 < B)
    (hX : ∀ j, 0 < X j) (ht : 0 < t) (hκ : 0 < κ) (hZ : 0 < Z) (h₀ : ∀ j, X j / B ≤ Z)
    (h₂ : t * κ ≤ Z ^ n) :
    A * (Z ^ (Fintype.card ι * m + n * r))⁻¹ ≤
      (t ^ r)⁻¹ * (A * B ^ (Fintype.card ι * m) * (κ ^ r)⁻¹ * ∏ j, ((X j) ^ m)⁻¹) := by
  have htκ : 0 < t * κ := mul_pos ht hκ
  have g₁ : ∏ _j : ι, (Z ^ m)⁻¹ ≤ ∏ j, ((X j / B) ^ m)⁻¹ :=
    Finset.prod_le_prod (fun _ _ ↦ by positivity) fun j _ ↦
      inv_anti₀ (pow_pos (div_pos (hX j) hB) m) (pow_le_pow_left₀ (div_pos (hX j) hB).le (h₀ j) m)
  have e₁ : ∏ _j : ι, (Z ^ m)⁻¹ = (Z ^ (Fintype.card ι * m))⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, inv_pow, ← pow_mul, mul_comm m]
  have e₂ : ∏ j, ((X j / B) ^ m)⁻¹ = B ^ (Fintype.card ι * m) * ∏ j, ((X j) ^ m)⁻¹ := by
    have : ∀ j, ((X j / B) ^ m)⁻¹ = B ^ m * ((X j) ^ m)⁻¹ := fun j ↦ by
      rw [div_pow, inv_div, div_eq_mul_inv]
    simp only [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm m]
  have g₂ : ((Z ^ n) ^ r)⁻¹ ≤ ((t * κ) ^ r)⁻¹ :=
    inv_anti₀ (pow_pos htκ r) (pow_le_pow_left₀ htκ.le h₂ r)
  rw [e₁, e₂] at g₁
  have hP : 0 ≤ ∏ j, ((X j) ^ m)⁻¹ :=
    Finset.prod_nonneg fun j _ ↦ inv_nonneg.2 (pow_pos (hX j) m).le
  calc A * (Z ^ (Fintype.card ι * m + n * r))⁻¹
      = A * ((Z ^ (Fintype.card ι * m))⁻¹ * ((Z ^ n) ^ r)⁻¹) := by
        rw [pow_add, pow_mul Z n r, mul_inv]
    _ ≤ A * ((B ^ (Fintype.card ι * m) * ∏ j, ((X j) ^ m)⁻¹) * ((t * κ) ^ r)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        exact mul_le_mul g₁ g₂ (by positivity) (by positivity)
    _ = (t ^ r)⁻¹ * (A * B ^ (Fintype.card ι * m) * (κ ^ r)⁻¹ * ∏ j, ((X j) ^ m)⁻¹) := by
        rw [mul_pow, mul_inv]
        ring

theorem infC_sum {α : Type} (s : Finset α) (f : α → 𝔸[k]) :
    infC (∑ i ∈ s, f i) = ∑ i ∈ s, infC (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, infC, homeomorphMixedSpace_apply]
    exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace k)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, infC_add, ih]

open scoped Classical in

theorem exists_decay_boundC_tensor (w : InfinitePlace k) (φ : 𝓢(ι → mixedSpace k, ℂ))
    (I : (FractionalIdeal (𝓞 k)⁰ k)ˣ) (b : ι → 𝔸ᶠ[k]) {C : Set (GL ι 𝔸[k])}
    (hC : IsCompact C) (r : ℕ) :
    ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ∀ ξ : ι → k, ξ ≠ 0 →
        ‖schwartzBruhatTensorPi φ (finiteTensor fun i ↦ cosetIndicator I (b i))
          (((scalC (moduleSection w t) * h : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)‖ ≤
            ((t : ℝ) ^ r)⁻¹ * u ξ := by
  classical

  have hinv : Continuous fun h : GL ι 𝔸[k] ↦ ((h⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) :=
    Units.continuous_coe_inv
  set Ci : Set (Matrix ι ι 𝔸[k]) :=
    (fun h : GL ι 𝔸[k] ↦ ((h⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) '' C
  have hCi : IsCompact Ci := hC.image hinv

  set T : ι → Set 𝔸ᶠ[k] := fun i ↦ b i +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[k])
  have hT : ∀ i, IsCompact (T i) := fun i ↦ (isCompact_idealFiniteAdeles I).vadd (b i)
  have hTpi : IsCompact (Set.pi Set.univ T) := isCompact_univ_pi hT
  have hent : ∀ i j, Continuous fun M : Matrix ι ι 𝔸[k] ↦ (M i j).2 := fun i j ↦
    continuous_snd.comp (continuous_id.matrix_elem i j)
  set S : Set 𝔸ᶠ[k] := ⋃ j : ι,
    (fun p : Matrix ι ι 𝔸[k] × (ι → 𝔸ᶠ[k]) ↦ ∑ i, (p.1 j i).2 * p.2 i) '' (Ci ×ˢ Set.pi Set.univ T)
  have hS : IsCompact S := isCompact_iUnion fun j ↦ (hCi.prod hTpi).image
    (continuous_finset_sum _ fun i _ ↦ ((hent j i).comp continuous_fst).mul
      ((continuous_apply i).comp continuous_snd))
  obtain ⟨J, κ₀, hκ₀, hJ, hN⟩ := exists_ideal_of_isCompact hS

  have hcont : Continuous fun M : Matrix ι ι 𝔸[k] ↦ ∑ j, ∑ i, ‖infC (M j i)‖ :=
    continuous_finset_sum _ fun j _ ↦ continuous_finset_sum _ fun i _ ↦
      continuous_norm.comp (continuous_infC.comp (continuous_id.matrix_elem j i))
  obtain ⟨B, hB⟩ := hCi.exists_bound_of_continuousOn hcont.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  have hBj : ∀ h ∈ C, ∀ j : ι, ∑ i,
      ‖infC (((h⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i)‖ ≤ B' := by
    intro h hh j
    have h1 := hB _ ⟨h, hh, rfl⟩
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      norm_nonneg _)] at h1
    exact (Finset.single_le_sum (f := fun j ↦ ∑ i,
      ‖infC (((h⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i)‖)
      (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)).trans
      (h1.trans (le_max_left _ _))
  set m := Module.finrank ℤ (idealLattice k J) + 1
  set n := Module.finrank ℚ k
  set N := Fintype.card ι
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ (N * m + n * r)
  set κ := κ₀ * (B' ^ n)⁻¹
  have hκ : 0 < κ := mul_pos hκ₀ (inv_pos.2 (pow_pos hB'0 n))
  set u₁ : k → ℝ := fun a ↦
    if a ∈ (J : FractionalIdeal (𝓞 k)⁰ k) then ((1 + ‖mixedEmbedding k a‖) ^ m)⁻¹ else 0
  have hu₁ : Summable u₁ := summable_ite_mem_of_summable_idealLattice J
    (h := fun x ↦ ((1 + ‖x‖) ^ m)⁻¹) (summable_inv_one_add_norm_pow_idealLattice J)
  have hu₁0 : ∀ a, 0 ≤ u₁ a := fun a ↦ by
    simp only [u₁]
    split_ifs
    · positivity
    · exact le_rfl
  have hc0 : 0 ≤ A * B' ^ (N * m) * (κ ^ r)⁻¹ := by positivity
  refine ⟨fun ξ ↦ A * B' ^ (N * m) * (κ ^ r)⁻¹ * ∏ i, u₁ (ξ i),
    (summable_prod_coord hu₁ hu₁0).mul_left _, ?_⟩
  intro h hh t ht ξ hξ0
  have ht0 : (0 : ℝ) < t := t.2
  set s := moduleSection w t
  set v : ι → 𝔸[k] := ratV ξ
  set y := (h : Matrix ι ι 𝔸[k]) *ᵥ v
  set hi := ((h⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])
  set e := infC ((s : IdeleGroup k) : 𝔸[k])
  rw [mulVec_scalC_mul]
  set z := infPartPi (((s : IdeleGroup k) : 𝔸[k]) • y)
  have hz : ∀ i, z i = e * infC (y i) := fun i ↦ infC_mul _ _
  have hfin : finPartPi (((s : IdeleGroup k) : 𝔸[k]) • y) = finPartPi y := by
    funext i
    have h1 : (((s : IdeleGroup k) : 𝔸[k])).2 = 1 := by
      rw [coe_moduleSection]
    change (((s : IdeleGroup k) : 𝔸[k])).2 * (y i).2 = (y i).2
    rw [h1, one_mul]
  have hP0 : 0 ≤ ∏ i, u₁ (ξ i) := Finset.prod_nonneg fun i _ ↦ hu₁0 _
  have hnn : 0 ≤ ((t : ℝ) ^ r)⁻¹ * (A * B' ^ (N * m) * (κ ^ r)⁻¹ * ∏ i, u₁ (ξ i)) :=
    mul_nonneg (by positivity) (mul_nonneg hc0 hP0)
  rw [schwartzBruhatTensorPi, hfin, finiteTensor]
  by_cases hm : ∀ i, (y i).2 ∈ T i
  · have hrec : ∀ j, algebraMap k 𝔸[k] (ξ j) = ∑ i, hi j i * y i := fun j ↦
      apply_eq_of_mulVec h v j

    have hξJ : ∀ j, ξ j ∈ (J : FractionalIdeal (𝓞 k)⁰ k) := by
      intro j
      refine hJ _ (Set.mem_iUnion.2 ⟨j, (hi, fun i ↦ (y i).2),
        ⟨⟨h, hh, rfl⟩, fun i _ ↦ hm i⟩, ?_⟩)
      have h1 := congrArg Prod.snd (hrec j)
      rw [adeleRing_algebraMap_snd] at h1
      have h2 : (∑ i, hi j i * y i).2 = ∑ i, (hi j i).2 * (y i).2 :=
        map_sum (RingHom.snd (InfiniteAdeleRing k) 𝔸ᶠ[k]) (fun i ↦ hi j i * y i) Finset.univ
      rw [h1]
      exact h2.symm

    have hmul : ∀ j, e * mixedEmbedding k (ξ j) = ∑ i, infC (hi j i) * z i := by
      intro j
      rw [← infC_algebraMap, hrec j, infC_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [infC_mul, hz]
      ring
    have hbd : ∀ j, ‖e * mixedEmbedding k (ξ j)‖ ≤ B' * ‖z‖ := by
      intro j
      have h1 := hBj h hh j
      have h2 : ∀ i, ‖z i‖ ≤ ‖z‖ := fun i ↦ norm_le_pi_norm z i
      calc ‖e * mixedEmbedding k (ξ j)‖
          ≤ ∑ i, ‖infC (hi j i)‖ * ‖z i‖ := by
            rw [hmul j]
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ norm_mul_le _ _)
        _ ≤ ∑ i, ‖infC (hi j i)‖ * ‖z‖ := Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_left (h2 i) (norm_nonneg _)
        _ = (∑ i, ‖infC (hi j i)‖) * ‖z‖ := by rw [Finset.sum_mul]
        _ ≤ B' * ‖z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have hemb : ∀ j, (1 + ‖mixedEmbedding k (ξ j)‖) / B' ≤ 1 + ‖z‖ := by
      intro j
      have h1 := (norm_le_norm_infC_moduleSection_mul w ht (mixedEmbedding k (ξ j))).trans (hbd j)
      rw [div_le_iff₀ hB'0]
      nlinarith [norm_nonneg z]

    have hnorm : (t : ℝ) * κ ≤ (1 + ‖z‖) ^ n := by
      obtain ⟨j, hj⟩ : ∃ j, ξ j ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hξ0 (funext hcon)
      have h1 : (t : ℝ) * κ₀ ≤ mixedEmbedding.norm (e * mixedEmbedding k (ξ j)) := by
        rw [map_mul, norm_infC_moduleSection]
        exact mul_le_mul_of_nonneg_left (hN _ (hξJ j) hj) ht0.le
      have h2 := h1.trans (mixedEmbedding_norm_le_norm_pow _)
      have h3 : ‖e * mixedEmbedding k (ξ j)‖ ^ n ≤ (B' * (1 + ‖z‖)) ^ n :=
        pow_le_pow_left₀ (norm_nonneg _) ((hbd j).trans
          (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg z]) hB'0.le)) n
      have h4 := h2.trans h3
      rw [mul_pow] at h4
      have hBn : 0 < B' ^ n := pow_pos hB'0 n
      calc (t : ℝ) * κ = (t : ℝ) * κ₀ * (B' ^ n)⁻¹ := by rw [mul_assoc]
        _ ≤ B' ^ n * (1 + ‖z‖) ^ n * (B' ^ n)⁻¹ :=
            mul_le_mul_of_nonneg_right h4 (inv_nonneg.2 hBn.le)
        _ = (1 + ‖z‖) ^ n := by field_simp
    have hone : ∏ i, cosetIndicator I (b i) (finPartPi y i) = 1 :=
      Finset.prod_eq_one fun i _ ↦ by
        rw [cosetIndicator]
        exact Set.indicator_of_mem (hm i) _
    rw [hone, mul_one]
    have hu : ∏ i, u₁ (ξ i) = ∏ i, ((1 + ‖mixedEmbedding k (ξ i)‖) ^ m)⁻¹ :=
      Finset.prod_congr rfl fun i _ ↦ by
        simp only [u₁]
        rw [if_pos (hξJ i)]
    beta_reduce
    rw [hu]
    exact (hφ z).trans (decay_real_bound hA hB'0 (X := fun j ↦ 1 + ‖mixedEmbedding k (ξ j)‖)
      (fun j ↦ by positivity) ht0 hκ (by positivity) hemb hnorm)
  · push_neg at hm
    obtain ⟨i, hi'⟩ := hm
    have hprod : ∏ i, cosetIndicator I (b i) (finPartPi y i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by
        rw [cosetIndicator]
        exact Set.indicator_of_notMem hi' _)
    rw [hprod, mul_zero, norm_zero]
    exact hnn

theorem exists_decay_boundC (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) (r : ℕ) :
    ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ∀ ξ : ι → k, ξ ≠ 0 →
        ‖F (((scalC (moduleSection w t) * h : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)‖ ≤
          ((t : ℝ) ^ r)⁻¹ * u ξ := by
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_decay_boundC_tensor w φ I b hC r
  | zero => exact ⟨0, summable_zero, fun _ _ _ _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨v, hv, hHv⟩ := hH
    refine ⟨u + v, hu.add hv, fun a ha t ht ξ hξ ↦ ?_⟩
    rw [Pi.add_apply, Pi.add_apply, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hGu a ha t ht ξ hξ) (hHv a ha t ht ξ hξ))
  | smul c G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖c‖ * u ξ, hu.mul_left _, fun a ha t ht ξ hξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hGu a ha t ht ξ hξ) (norm_nonneg c)

theorem exists_norm_thetaC_sub_le : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) (r : ℕ), ∃ M : ℝ, ∀ h ∈ C,
      ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaC F (scalC (moduleSection w t) * h) - F 0‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  intro k _ _ ι _ _ w F hF C hC r
  classical
  obtain ⟨u, hu, hFu⟩ := exists_decay_boundC w hF hC r
  refine ⟨∑' ξ, |u ξ|, fun h hh t ht ↦ ?_⟩
  have ht0 : 0 < ((t : ℝ) ^ r)⁻¹ := inv_pos.2 (pow_pos t.2 r)
  have hb : ∀ ξ : ι → k, ξ ≠ 0 →
      ‖F (((scalC (moduleSection w t) * h : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)‖ ≤
        ((t : ℝ) ^ r)⁻¹ * |u ξ| := fun ξ hξ ↦
    (hFu h hh t ht ξ hξ).trans (mul_le_mul_of_nonneg_left (le_abs_self _) ht0.le)
  have hs : Summable fun ξ : ι → k ↦
      F (((scalC (moduleSection w t) * h : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ) := by
    refine Summable.of_norm_bounded_eventually (hu.abs.mul_left ((t : ℝ) ^ r)⁻¹) ?_
    filter_upwards [(Set.finite_singleton (0 : ι → k)).compl_mem_cofinite] with ξ hξ
    exact hb ξ hξ
  have h0 : F (((scalC (moduleSection w t) * h : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ
      ratV (0 : ι → k)) = F 0 := by
    congr 1
    have : ratV (0 : ι → k) = (0 : ι → 𝔸[k]) := by
      funext i
      simp [ratV]
    rw [this, Matrix.mulVec_zero]
  rw [thetaC, hs.tsum_eq_add_tsum_ite 0, h0, add_sub_cancel_left, ← tsum_mul_left]
  refine tsum_of_norm_bounded ((hu.abs.mul_left _).hasSum) fun ξ ↦ ?_
  split_ifs with h'
  · rw [norm_zero]
    exact mul_nonneg ht0.le (abs_nonneg _)
  · exact hb ξ h'

end

end GlobalTheory.CompanionTheory.EisThCDecay
