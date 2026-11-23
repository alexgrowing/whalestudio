import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRamifiedCharDetSingularMatrixCosetEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
import Development.AutomorphicArithmetic.DivisorFrames.ExistsMemKOEqStdFrameMulOfIsPrimFrameFin
import Development.AutomorphicArithmetic.DivisorFrames.HaarVolKOLeResCardPowOfCongruenceLe
import Development.AutomorphicArithmetic.DivisorFrames.UnramifiedCharacterInvariant

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel Matrix

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat

namespace GlobalTheory.ConjSize

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {K : Type} [Field K] {ι τ : K →+* ℂ}

theorem one_le_q : (1 : ℝ) ≤ resCard k := by
  have h := GlobalTheory.FlipMatch.FourierInv.card_res_pow k 1
  have hp : 0 < Fintype.card (Res k 1) := Fintype.card_pos
  rw [h, pow_one] at hp
  exact_mod_cast hp

theorem card_res_fun (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (e : ℕ) :
    Fintype.card (A → B → Res k e) = resCard k ^ (e * Fintype.card A * Fintype.card B) := by
  rw [Fintype.card_fun, Fintype.card_fun, GlobalTheory.FlipMatch.FourierInv.card_res_pow, ← pow_mul, ← pow_mul]
  congr 1; ring

theorem sz_fourierSum {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → Un ι τ (ψ x : ℂ))
    {Φ : Matrix A D k → ℂ} {B : ℝ} (hΦ : ∀ X, Sz ι τ (Φ X) B) (Y : Matrix A D k) : Sz ι τ (fourierSum ψ ϖ e P Φ Y) B := by
  rw [fourierSum_apply]
  have hB0 : 0 ≤ B := (hΦ Y).nonneg
  split_ifs with hY
  · have hsum : Sz ι τ (∑ T : A → P → Res k e, Φ (setCols P Y (liftRes T)) * (ψ (pairCols P Y (liftRes T)) : ℂ))
        ((Finset.univ : Finset (A → P → Res k e)).card * B) := by
      apply Sz.sum_card
      intro T _
      apply Sz.mul_un (hΦ _)
      apply hψ
      have hm : ((ϖ ^ e : kˣ) : k) * pairCols P Y (liftRes T) ∈ 𝒪[k] := by
        simp only [pairCols, Finset.mul_sum]
        refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
        rw [mul_left_comm]
        exact Subring.mul_mem _ (liftRes_mem T i j) (hY i j j.2)
      exact (Valuation.mem_integer_iff _ _).mp hm
    have hinv := Sz.inv_nat (ι := ι) (τ := τ) (resCard k ^ (e * Fintype.card A * P.card))
    push_cast at hinv
    refine (hinv.mul hsum).mono ?_
    have hc : (Finset.univ : Finset (A → P → Res k e)).card = resCard k ^ (e * Fintype.card A * P.card) := by
      rw [Finset.card_univ, card_res_fun, Fintype.card_coe]
    rw [hc]
    have hq : (0:ℝ) < resCard k := lt_of_lt_of_le one_pos one_le_q
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  · exact Sz.zero hB0

theorem sz_invFourierSum {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → Un ι τ (ψ x : ℂ))
    {Φ : Matrix A D k → ℂ} {B : ℝ} (hΦ : ∀ X, Sz ι τ (Φ X) B) (T : Matrix A D k) :
    Sz ι τ (invFourierSum ψ⁻¹ ϖ e P Φ T) ((resCard k : ℝ) ^ (e * Fintype.card A * P.card) * B) := by
  rw [invFourierSum_inv_apply]
  have hB0 : 0 ≤ B := (hΦ T).nonneg
  have hq : (0:ℝ) < resCard k := lt_of_lt_of_le one_pos one_le_q
  split_ifs with hT
  · have hc : (Finset.univ : Finset (A → P → Res k e)).card = resCard k ^ (e * Fintype.card A * P.card) := by
      rw [Finset.card_univ, card_res_fun, Fintype.card_coe]
    have hsum := Sz.sum_card (ι := ι) (τ := τ) (Finset.univ : Finset (A → P → Res k e))
      (f := fun S => Φ (setCols P T ((ϖ ^ e)⁻¹ • liftRes S)) * (ψ (pairCols P T ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ))
      (B := B) (by
        intro S _
        apply Sz.mul_un (hΦ _)
        apply hψ
        have key : ((ϖ ^ e : kˣ) : k) * pairCols P T ((ϖ ^ e)⁻¹ • liftRes S) = pairCols P T (liftRes S) := by
          simp only [pairCols, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
        have hm : pairCols P T (liftRes S) ∈ 𝒪[k] := by
          simp only [pairCols]
          exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
            Subring.mul_mem _ (liftRes_mem S i j) (hT i j j.2)
        rw [key]
        exact (Valuation.mem_integer_iff _ _).mp hm)
    rw [hc] at hsum
    push_cast at hsum
    exact hsum
  · exact Sz.zero (mul_nonneg (by positivity) hB0)

variable [MeasurableSpace k] [BorelSpace k]

private theorem res_eq_of_liftRes_sub_valuation_le {A : Type} {ϖ : kˣ} (hϖ : IsUnif ϖ) {e : ℕ} (T T' : A → A → Res k e)
    (h : ∀ i j, valuation k (liftRes T i j - liftRes T' i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) : T = T' := by
  funext i j
  have h1 := (Model.val_le_iff_mem hϖ e ((T i j).out - (T' i j).out)).mpr (by simpa [liftRes] using h i j)
  rw [← Ideal.Quotient.mk_out (T i j), ← Ideal.Quotient.mk_out (T' i j)]
  exact Ideal.Quotient.eq.mpr h1

private theorem exists_res_approx_of_entries_integral {A : Type} {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (x : Matrix A A k)
    (hx : ∀ i j, x i j ∈ 𝒪[k]) :
    ∃ T : A → A → Res k e, ∀ i j, valuation k (x i j - liftRes T i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  refine ⟨fun i j => Ideal.Quotient.mk _ ⟨x i j, hx i j⟩, fun i j => ?_⟩
  have h1 : (⟨x i j, hx i j⟩ : 𝒪[k]) - (Ideal.Quotient.mk (𝓂[k] ^ e) ⟨x i j, hx i j⟩ : Res k e).out ∈ 𝓂[k] ^ e := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  have h2 := (Model.val_le_iff_mem hϖ e _).mp h1
  simpa [liftRes] using h2

theorem sz_zeta {A : Type} [Fintype A] [DecidableEq A] {J : Subgroup (GL A k)} (hJo : IsOpen (J : Set (GL A k)))
    (hJK : J ≤ KO k A) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hJ : glLatCong (ϖ ^ e) (SplitFlip.stdLat k A) ≤ J)
    (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν) (hνU : ∀ u, Un ι τ (ν u : ℂ)) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι)
    (n : ℕ) {φ : Matrix A A k → ℂ} (hφ : IsNatDatum ϖ e φ) {B : ℝ} (hB : ∀ X, Sz ι τ (φ X) B) :
    Sz ι τ (∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2) ∂(haarVol J))
      ((resCard k : ℝ) ^ (2 * e * Fintype.card A * Fintype.card A) * B) := by
  haveI := isHaarMeasure_haarVol hJo hJK
  have hB0 : 0 ≤ B := (hB 0).nonneg
  set S : (A → A → Res k e) → Set (GL A k) := fun T =>
    {g | ∀ i j, valuation k ((g : Matrix A A k) i j - liftRes T i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)} with hS
  have hSm : ∀ T, MeasurableSet (S T) := fun T =>
    ((GlobalTheory.SmallFInF.isOpen_cosetM (ϖ ^ e) (liftRes T)).preimage Units.continuous_val).measurableSet
  have hconst : ∀ T, ∀ g ∈ S T, φ (g : Matrix A A k) = φ (liftRes T) := by
    intro T g hg
    have := hφ.2 (liftRes T) ((g : Matrix A A k) - liftRes T)
      (GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.mpr (fun i j => hg i j))
    rw [add_sub_cancel] at this
    exact this
  have hzero : ∀ g : GL A k, ¬ (∀ i j, (g : Matrix A A k) i j ∈ 𝒪[k]) → φ (g : Matrix A A k) = 0 := by
    intro g hg
    apply hφ.1
    rwa [mem_matLat_stdLat]
  set f : GL A k → ℂ := fun g => (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2) with hf
  have hF : (fun g : GL A k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2)) =
      fun g => ∑ T, (S T).indicator (fun g => φ g.val * f g) g := by
    funext g
    by_cases hg : ∀ i j, (g : Matrix A A k) i j ∈ 𝒪[k]
    · obtain ⟨T0, hT0⟩ := exists_res_approx_of_entries_integral hϖ e (g : Matrix A A k) hg
      rw [Finset.sum_eq_single T0]
      · rw [Set.indicator_apply, if_pos (show g ∈ S T0 from hT0), mul_assoc]
      · intro T _ hT
        rw [Set.indicator_apply, if_neg]
        intro hgT
        apply hT
        apply res_eq_of_liftRes_sub_valuation_le hϖ
        intro i j
        rw [show liftRes T i j - liftRes T0 i j =
          ((g : Matrix A A k) i j - liftRes T0 i j) + (liftRes T i j - (g : Matrix A A k) i j) by ring]
        exact Valuation.map_add_le _ (hT0 i j) (by rw [Valuation.map_sub_swap]; exact hgT i j)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h0 : φ g.val = 0 := hzero g hg
      simp [Set.indicator_apply, h0]
  by_cases hint : Integrable (fun g : GL A k => φ g.val * f g) (haarVol J)
  · have hI : ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2) ∂(haarVol J) =
        ∑ T, φ (liftRes T) * ∫ g in S T, f g ∂(haarVol J) := by
      rw [hF, integral_finset_sum _ (fun T _ => hint.indicator (hSm T))]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [integral_indicator (hSm T)]
      rw [setIntegral_congr_fun (hSm T) (g := fun g => φ (liftRes T) * f g) (fun g hg => by
        show φ g.val * f g = φ (liftRes T) * f g
        rw [hconst T g hg])]
      exact integral_const_mul _ _
    rw [hI]
    have hvol := UpperTheory.haarVol_KO_le_resCard_pow_of_congruence_le hJo hJK hϖ hJ
    have hterm : ∀ T, Sz ι τ (φ (liftRes T) * ∫ g in S T, f g ∂(haarVol J))
        (B * (resCard k : ℝ) ^ (e * Fintype.card A * Fintype.card A)) := by
      intro T
      refine (hB _).mul ?_
      by_cases hsing : ∃ y : Matrix A A k,
          (∀ i j, valuation k (y i j - liftRes T i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) ∧ y.det = 0
      · obtain ⟨y, hy, hdet⟩ := hsing
        have hSy : S T = {g : GL A k | ∀ i j,
            valuation k ((g : Matrix A A k) i j - y i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)} := by
          ext g
          simp only [hS, Set.mem_setOf_eq]
          constructor
          · intro hg i j
            rw [show (g : Matrix A A k) i j - y i j =
              ((g : Matrix A A k) i j - liftRes T i j) + (liftRes T i j - y i j) by ring]
            exact Valuation.map_add_le _ (hg i j) (by rw [Valuation.map_sub_swap]; exact hy i j)
          · intro hg i j
            rw [show (g : Matrix A A k) i j - liftRes T i j =
              ((g : Matrix A A k) i j - y i j) + (y i j - liftRes T i j) by ring]
            exact Valuation.map_add_le _ (hg i j) (hy i j)
        have h0 : ∫ g in S T, f g ∂(haarVol J) = 0 := by
          rw [hSy]
          exact GlobalTheory.CosetVanish.integral_coset_singular_eq_zero (haarVol J) ν ((n : ℂ) / 2) hram (ϖ ^ e) y hdet
        rw [h0]
        exact Sz.zero (by positivity)
      · have h1 := UpperTheory.unramified_character_invariant ι τ hJo hJK ν hϖ hν hνU habs n (liftRes T)
          (fun i j => (Valuation.mem_integer_iff _ _).mp (liftRes_mem T i j))
          (fun y hy hdet => hsing ⟨y, hy, hdet⟩)
        exact h1.mono hvol
    have hsum := Sz.sum_card (ι := ι) (τ := τ) (Finset.univ : Finset (A → A → Res k e)) (fun T _ => hterm T)
    refine hsum.mono (le_of_eq ?_)
    rw [Finset.card_univ, card_res_fun]
    push_cast
    rw [show 2 * e * Fintype.card A * Fintype.card A =
      e * Fintype.card A * Fintype.card A + e * Fintype.card A * Fintype.card A by ring, pow_add]
    ring
  · rw [integral_undef]
    · exact Sz.zero (mul_nonneg (by positivity) hB0)
    · intro h
      apply hint
      simpa only [mul_assoc] using h

omit [MeasurableSpace k] [BorelSpace k] in
theorem row_mul' {A B C : Type} [Fintype B] (Y : Matrix A B k) (M : Matrix B C k) (i : A) : (Y * M).row i = Y.row i ᵥ* M := by
  ext j
  rfl

omit [MeasurableSpace k] [BorelSpace k] in

theorem isNatDatum_comp {A A' D : Type} [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D)
    {ϖ : kˣ} {e : ℕ} (c : D → kˣ) {Ψ : Matrix A' D k → ℂ} (hΨ : HasDepth ϖ e (diagLat c) Ψ) {κ : GL D k} (hκ : κ ∈ KO k D) :
    IsNatDatum ϖ e fun g : Matrix A' A' k => Ψ (g * (Y0 k σ * (κ * diagGL c).val)) := by
  have hrow : ∀ (M : Matrix A' D k) (i : A') (b d : D → kˣ), (∀ j, d j = b j * c j) →
      ((M * (κ * diagGL c : GL D k).val).row i ∈ diagLat d ↔ (M * (κ : Matrix D D k)).row i ∈ diagLat b) := by
    intro M i b d hd
    rw [Units.val_mul, diagGL_val, ← Matrix.mul_assoc, row_mul', ← diagGL_val]
    exact GlobalTheory.FrameDepth.vecMul_diagGL_mem b c d hd _
  have hYκ : ∀ a j, (Y0 k σ * (κ : Matrix D D k)) a j ∈ 𝒪[k] := by
    intro a j
    rw [frameMatrixSecondColumnBlock_mul_apply]
    exact ((mem_KO_iff κ).mp hκ).1 _ _
  refine ⟨?_, ?_⟩
  · intro g hg
    by_contra hne
    apply hg
    have hm : g * (Y0 k σ * (κ * diagGL c : GL D k).val) ∈ matLat A' (diagLat c) := by
      by_contra h
      exact hne (hΨ.1 _ h)
    have hall : g * Y0 k σ * (κ : Matrix D D k) ∈ matLat A' (stdLat k D) := by
      intro i
      have hi := hm i
      rw [← Matrix.mul_assoc, hrow (g * Y0 k σ) i 1 c (fun j => by simp)] at hi
      exact hi
    have h1 : ((1 : GL A' k) : Matrix A' A' k) * (g * Y0 k σ) * (κ : Matrix D D k) ∈ matLat A' (stdLat k D) := by
      rw [Units.val_one, Matrix.one_mul]
      exact hall
    have h1' := (mul_mul_mem_matLat_iff (g := (1 : GL A' k)) (h := κ) (KO k A').one_mem hκ (g * Y0 k σ)).mp h1
    rw [mem_matLat_stdLat] at h1'
    rw [mem_matLat_stdLat]
    intro i a
    have h2 := h1' i (σ (Sum.inr a))
    have h3 : (g * Y0 k σ) i (σ (Sum.inr a)) = g i a := by
      simp [Matrix.mul_apply, Y0]
    rwa [h3] at h2
  · intro X Z hZ
    show Ψ ((X + Z) * (Y0 k σ * (κ * diagGL c : GL D k).val)) = Ψ (X * (Y0 k σ * (κ * diagGL c : GL D k).val))
    rw [Matrix.add_mul]
    apply hΨ.2
    rw [smul_diagLat]
    intro i
    rw [← Matrix.mul_assoc, hrow (Z * Y0 k σ) i (fun _ => ϖ ^ e) (fun j => ϖ ^ e * c j) (fun j => rfl)]
    have hC : GlobalTheory.FunObj.GivenAdm.CongM (ϖ ^ e) (Z * Y0 k σ * (κ : Matrix D D k)) := by
      rw [Matrix.mul_assoc]
      exact GlobalTheory.FunObj.GivenAdm.CongM.mul_right (GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.mp hZ) hYκ
    have hm := GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.mpr hC i
    rw [show stdLat k D = diagLat 1 from rfl, smul_diagLat] at hm
    simpa using hm

theorem sz_phiA {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {a' : ℕ}
    {J : Subgroup (GL (Fin a') k)} (hJo : IsOpen (J : Set (GL (Fin a') k))) (hJK : J ≤ KO k (Fin a')) (σ : A ⊕ Fin a' ≃ D)
    (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hJ : glLatCong (ϖ ^ e) (SplitFlip.stdLat k (Fin a')) ≤ J)
    (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν) (hνU : ∀ u, Un ι τ (ν u : ℂ)) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι)
    (P : Finset D) {Ψ : Matrix (Fin a') D k → ℂ} (hΨ : HasDepth ϖ e (blockLat ϖ e P) Ψ) {B : ℝ} (hB : ∀ Y, Sz ι τ (Ψ Y) B)
    (X : Matrix A D k) : Sz ι τ (phiA (haarVol J) σ ν ϖ e (blockLat ϖ e P) Ψ X)
      ((resCard k : ℝ) ^ (e * a' * Fintype.card D + 2 * e * a' * a') * B) := by
  haveI := isHaarMeasure_haarVol hJo hJK
  have hB0 : 0 ≤ B := (hB 0).nonneg
  have hq : (1:ℝ) ≤ resCard k := one_le_q
  unfold phiA
  split_ifs with hX
  swap
  · exact Sz.zero (by positivity)
  rw [latA_blockLat] at hX
  have hlat : ∀ x : D → k, x ᵥ* (((blockScale ϖ e Pᶜ)⁻¹ : GL D k) : Matrix D D k) ∈ stdLat k D ↔
      x ∈ blockLat ϖ e Pᶜ := by
    intro x
    rw [← vecMul_blockScale_mem ϖ e Pᶜ, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]
  obtain ⟨κ, hκ, hκX⟩ := UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame_fin σ _ (Model.isPrimFrame_mul hX (blockScale ϖ e Pᶜ)⁻¹ hlat)
  have hinvT : invT (diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)) = blockScale ϖ e Pᶜ := by
    apply Units.ext
    show ((((diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j))⁻¹ : GL D k) : Matrix D D k))ᵀ = _
    have h1 : (((diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j))⁻¹ : GL D k) : Matrix D D k) =
        diagonal fun j => (((ϖ ^ e * blockUnits ϖ e P j)⁻¹ : kˣ) : k) := rfl
    rw [h1, Matrix.diagonal_transpose, blockScale, diagGL_val]
    congr 1
    funext j
    by_cases hj : j ∈ P <;> simp [blockUnits, hj]
  have hXeq : X = X0 k σ * ((invT (κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)) : GL D k) : Matrix D D k) := by
    rw [map_mul, hinvT, Units.val_mul, ← Matrix.mul_assoc, ← hκX, Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.mul_one]
  rw [hXeq, splitTheta_fFun_frameFirstBlock_mul]
  have hY : Y0 k σ * ((κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j) : GL D k) : Matrix D D k) =
      ((diagGL (fun _ : Fin a' => ϖ ^ e) : GL (Fin a') k) : Matrix (Fin a') (Fin a') k) *
        (Y0 k σ * ((κ * diagGL (blockUnits ϖ e P) : GL D k) : Matrix D D k)) := by
    have hd : ((diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j) : GL D k) : Matrix D D k) =
        ((ϖ ^ e : kˣ) : k) • ((diagGL (blockUnits ϖ e P) : GL D k) : Matrix D D k) := by
      rw [diagGL_val, diagGL_val]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [diagGL_val, Units.val_mul, Units.val_mul, hd, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.smul_eq_diagonal_mul]
  have hmulL := smallF_mul_left (haarVol J) ν Ψ (diagGL (fun _ : Fin a' => ϖ ^ e))
    (Y0 k σ * ((κ * diagGL (blockUnits ϖ e P) : GL D k) : Matrix D D k))
  rw [← hY] at hmulL
  have hsmall : smallF (haarVol J) ν Ψ (Y0 k σ * ((κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j) : GL D k) : Matrix D D k)) =
      (ν (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) : ℂ)⁻¹ *
        (apow (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) ((Fintype.card D : ℂ) / 2))⁻¹ *
        smallF (haarVol J) ν Ψ (Y0 k σ * ((κ * diagGL (blockUnits ϖ e P) : GL D k) : Matrix D D k)) := by
    rw [← hmulL]
    have h1 : (ν (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) : ℂ) ≠ 0 := Units.ne_zero _
    have h2 := apow_ne_zero (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) ((Fintype.card D : ℂ) / 2)
    field_simp
  rw [hsmall]
  have hzeta := sz_zeta (ι := ι) (τ := τ) hJo hJK ν hϖ hJ hν hram hνU habs (Fintype.card D)
    (isNatDatum_comp σ (blockUnits ϖ e P) hΨ hκ) (fun X => hB _)
  simp only [Fintype.card_fin] at hzeta
  have hdet0 : gdet (diagGL (fun _ : Fin a' => ϖ ^ e)) = (ϖ ^ e) ^ a' := by
    ext
    simp [gdet, diagGL_val, Matrix.det_diagonal]
  have hnabs : nabs k (gdet (diagGL (fun _ : Fin a' => ϖ ^ e)))⁻¹ = (resCard k : ℝ) ^ (e * a') := by
    have hn : ((distribHaarChar k ϖ : NNReal) : ℝ) = (resCard k : ℝ)⁻¹ :=
      GlobalTheory.SplitWeil.nabs_uniformiser hϖ.irreducible rfl
    rw [hdet0]
    unfold nabs
    rw [map_inv, map_pow, map_pow]
    push_cast
    rw [hn, ← pow_mul, inv_pow, inv_inv]
  have hA : Sz ι τ (apow (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))) ((Fintype.card D : ℂ) / 2))⁻¹
      (((resCard k : ℝ) ^ (e * a')) ^ Fintype.card D) := by
    rw [← apow_neg, ← apow_inv]
    exact sz_apow_nat_half _ (habs _) _ (one_le_pow₀ hq) hnabs.le
  have hdh : valuation k ((gdet (κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)) : kˣ) : k) ≤ 1 := by
    rw [gdet_mul, Units.val_mul, map_mul, valuation_gdet_of_mem_KO hκ, one_mul]
    have hp : ((gdet (diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)) : kˣ) : k) =
        ∏ j, (((ϖ ^ e * blockUnits ϖ e P j) : kˣ) : k) := by
      simp [gdet, diagGL_val, Matrix.det_diagonal]
    rw [hp, map_prod]
    apply Finset.prod_le_one'
    intro j _
    by_cases hj : j ∈ P
    · simp [blockUnits, hj]
    · simp only [blockUnits, hj, if_false, mul_one, Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one' ((Valuation.mem_integer_iff _ _).mp (IsUnif.mem hϖ)) _
  have hH : Sz ι τ (apow (gdet (κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j))) ((Fintype.card D : ℂ) / 2)) 1 :=
    sz_apow_of_le_one _ (habs _) _ hdh
  have hfinal := (hνU (gdet (κ * diagGL (fun j => ϖ ^ e * blockUnits ϖ e P j)))).mul_sz
    (hH.mul ((Un.inv (hνU (gdet (diagGL (fun _ : Fin a' => ϖ ^ e))))).mul_sz (hA.mul hzeta)))
  refine Sz.mono (B := 1 * (((resCard k : ℝ) ^ (e * a')) ^ Fintype.card D * ((resCard k : ℝ) ^ (2 * e * a' * a') * B))) ?_ ?_
  · convert hfinal using 1
    simp only [smallF]
    ring
  · rw [one_mul, ← pow_mul, ← mul_assoc, ← pow_add]

theorem sz_flipTensor {G : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → Un ι τ (ψ x : ℂ)) {i j M : ℕ}
    (hM : G.rank (i + 1, j + 1) ≤ M)
    (hν : CondLE ϖ e (G.nu i j)) (hram : ¬ IsUnram (G.nu i j)) (hνU : ∀ u, Un ι τ (G.nu i j u : ℂ)) {J : G.Level}
    (hJ : IsOpen (J (i, j) : Set (GL (Fin (G.rank (i, j))) k))) (hK : J (i, j) ≤ KO k _)
    (hC : glLatCong (ϖ ^ e) (SplitFlip.stdLat k _) ≤ J (i, j)) {γ : List Edge}
    (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) {B : ℝ}
    (hB : ∀ x, Sz ι τ (T x) B) (x : G.Args) :
    Sz ι τ (G.flipTensor .one ψ ϖ e i j J T x) ((resCard k : ℝ) ^ (6 * e * M ^ 2) * B) := by
  have hq : (1:ℝ) ≤ resCard k := one_le_q
  have hB0 : 0 ≤ B := (hB x).nonneg
  have hJ' := isOpen_map_invT hJ hK
  have hC' : glLatCong (ϖ ^ e) (SplitFlip.stdLat k (Fin (G.rank (i, j)))) ≤ Subgroup.map invT (J (i, j)) := by
    intro g hg
    exact ⟨invT g, hC (GlobalTheory.FunObj.GivenAdm.invT_mem_glLatCong hg), invT_invT g⟩
  have hdep := (FourierDepth.fourier_exchange k (Fin (G.rank (i, j))) (G.Cols i j) ψ ϖ e
      (Assignment.one.block (Fin (G.rank (i, j + 1))) (Fin (G.rank (i + 1, j)))) hϖ hψc).1 _
      (GlobalTheory.FunObj.isNatDatum_sliceB hT h1 h2 x)
  unfold Grid.flipTensor squareFlip
  refine Sz.mono (sz_invFourierSum ψ ϖ e _ hψ (fun X => sz_phiA hJ'.1 hJ'.2 _ (G.nu i j) hϖ hC' hν hram hνU habs _
    hdep (fun Y => sz_fourierSum ψ ϖ e _ hψ (fun Z => hB _) Y) X) _) ?_
  rw [← mul_assoc, ← pow_add]
  apply mul_le_mul_of_nonneg_right _ hB0
  apply pow_le_pow_right₀ hq
  have hcard : Fintype.card (G.Cols i j) = G.rank (i + 1, j + 1) + G.rank (i, j) := by
    simp only [Grid.Cols, Fintype.card_sum, Fintype.card_fin]
    exact (G.rank_square i j).symm
  have hc := Finset.card_le_univ (Assignment.one.block (Fin (G.rank (i, j + 1))) (Fin (G.rank (i + 1, j))))ᶜ
  have h00 : G.rank (i, j) ≤ G.rank (i + 1, j + 1) := by
    simp only [Grid.rank]
    nlinarith
  simp only [Fintype.card_fin]
  rw [hcard] at hc ⊢
  generalize (Assignment.one.block (Fin (G.rank (i, j + 1))) (Fin (G.rank (i + 1, j))))ᶜ.card = c at hc ⊢
  generalize G.rank (i + 1, j + 1) = a at hM h00 hc ⊢
  generalize G.rank (i, j) = b at h00 hc ⊢
  have hbM : b ≤ M := le_trans h00 hM
  have e1 : a * c ≤ M * (M + M) := Nat.mul_le_mul hM (by omega)
  have e2 : b * (a + b) ≤ M * (M + M) := Nat.mul_le_mul hbM (by omega)
  have e3 : b * b ≤ M * M := Nat.mul_le_mul hbM hbM
  have f1 := Nat.mul_le_mul_left e e1
  have f2 := Nat.mul_le_mul_left e e2
  have f3 := Nat.mul_le_mul_left e e3
  nlinarith

theorem sz_flips {G : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → Un ι τ (ψ x : ℂ)) (M : ℕ) :
    ∀ (l : List (ℕ × ℕ)) (S : G.PiLocalization₂) (B : ℝ),
      (∀ x ∈ l, G.rank (x.1 + 1, x.2 + 1) ≤ M ∧ CondLE ϖ e (G.nu x.1 x.2) ∧ ¬ IsUnram (G.nu x.1 x.2) ∧
        ∀ u, Un ι τ (G.nu x.1 x.2 u : ℂ)) →
      CanFlip S.path l → (∀ X, IsOpen (S.level X : Set (GL (Fin (G.rank X)) k)) ∧ S.level X ≤ KO k _ ∧
        glLatCong (ϖ ^ e) (SplitFlip.stdLat k _) ≤ S.level X) →
      G.IsTensor ϖ e S.path S.tensor → (∀ z, Sz ι τ (S.tensor z) B) →
      ∀ z, Sz ι τ ((S.flips .one ψ ϖ e l).tensor z) ((resCard k : ℝ) ^ (6 * e * M ^ 2 * l.length) * B) := by
  intro l
  induction l with
  | nil =>
    intro S B _ _ _ _ hB z
    simpa [Grid.PiLocalization₂.flips] using hB z
  | cons x l ih =>
    intro S B hl hcan hlev hT hB z
    obtain ⟨hMx, hνx, hramx, hνUx⟩ := hl x (List.mem_cons_self ..)
    cases hcan with
    | cons hpass hcan' =>
      have hth : Edge.theta x.1 x.2 ∈ S.path := hpass.subset (by simp)
      have hex : Edge.ex x.1 x.2 ∈ S.path := hpass.subset (by simp)
      obtain ⟨hJo, hJK, hJC⟩ := hlev (x.1, x.2)
      have key := ih (S.flip .one ψ ϖ e x) ((resCard k : ℝ) ^ (6 * e * M ^ 2) * B)
        (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hcan'
        (by
          intro X
          rcases eq_or_ne X (x.1 + 1, x.2 + 1) with rfl | hne
          · simp only [Grid.PiLocalization₂.flip, Grid.flipLevel, Function.update_self]
            exact ⟨isOpen_KO, le_rfl, fun g hg => (GlobalTheory.FunObj.GivenAdm.mem_glLatCong.mp hg).1⟩
          · simp only [Grid.PiLocalization₂.flip, Grid.flipLevel, Function.update_of_ne hne]
            exact hlev X)
        (GlobalTheory.FunObj.isTensor_flipTensor hϖ hψc he hνx hJo hJK hth hex hT)
        (fun w => sz_flipTensor hϖ hψc habs hψ hMx hνx hramx hνUx hJo hJK hJC hth hex hT hB w) z
      have hlen : 6 * e * M ^ 2 * (x :: l).length = 6 * e * M ^ 2 * l.length + 6 * e * M ^ 2 := by
        simp only [List.length_cons]
        ring
      rw [hlen, pow_add, mul_assoc]
      exact key

end GlobalTheory.ConjSize

end
