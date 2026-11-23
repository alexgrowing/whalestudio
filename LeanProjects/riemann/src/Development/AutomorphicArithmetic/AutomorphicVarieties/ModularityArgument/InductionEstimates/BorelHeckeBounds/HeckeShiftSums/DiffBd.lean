import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DiffBound
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsArchConv
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate Pointwise Manifold ContDiff

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_bump {K : Type} [Field K] [NumberField K] {n : ℕ} {L : Set (ArchMatrix K n)}
    (hL : IsCompact L) (hLu : L ⊆ {x | IsUnit x}) :
    ∃ χ : ArchMatrix K n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x ∈ L, χ x = 1) ∧
      tsupport χ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := by
  obtain ⟨M, hM, hLM, hMu⟩ := exists_compact_between hL Units.isOpen hLu
  obtain ⟨f, h1, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (n := ⊤)
    𝓘(ℝ, ArchMatrix K n) hL.isClosed hLM
  have hsub : tsupport f ⊆ M :=
    closure_minimal (fun x hx => by_contra fun h => hx (h0 x h)) hM.isClosed
  refine ⟨f, f.contMDiff.contDiff, hM.of_isClosed_subset (isClosed_tsupport _) hsub,
    fun x hx => (h1.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds, fun x hx => ?_⟩
  obtain ⟨u, rfl⟩ := hMu (hsub hx)
  exact ⟨u, rfl⟩

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_test {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) {χ : ArchMatrix K n → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχu : tsupport χ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)) :
    (isExpLieAlgebra K n).IsTestFunction
      (fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a) := by
  refine ⟨((isExpLieAlgebra K n).isSmoothFun_iff).2 fun g => ?_, ?_⟩
  · refine ContDiff.mul ?_ (((isExpLieAlgebra K n).isSmoothFun_iff).1 hf g)
    have e : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun Y : archLie K n =>
        (((g * (isExpLieAlgebra K n).expG Y : archGroup K n) : ArchUnits K n) : ArchMatrix K n) := by
      have : (fun Y : archLie K n =>
          (((g * (isExpLieAlgebra K n).expG Y : archGroup K n) : ArchUnits K n) : ArchMatrix K n)) =
          fun Y : archLie K n => ((g : ArchUnits K n) : ArchMatrix K n) * NormedSpace.exp (Y : ArchMatrix K n) := by
        funext Y
        simp only [Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
      rw [this]
      exact contDiff_const.mul ((contDiff_exp ℝ (ArchMatrix K n)).comp (archLie K n).subtypeL.contDiff)
    exact Complex.ofRealCLM.contDiff.comp (hχ.comp e)
  · refine HasCompactSupport.intro
      ((isCompact_unitsSupport hχc hχu).image (archGroupEquiv K n).symm.continuous) fun a ha => ?_
    have : ((a : ArchUnits K n) : ArchMatrix K n) ∉ tsupport χ := fun h =>
      ha ⟨(a : ArchUnits K n), h, (archGroupEquiv K n).symm_apply_apply a⟩
    rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_local {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) {T : Set (archGroup K n)} (hT : IsCompact T) (k : ℕ) (R : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) →
      ∀ A ∈ T, ‖∑ ε, (altSign ε : ℂ) * f ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩‖ ≤ c * ∏ i, ‖Y i‖ := by
  set T₀ : Set (ArchUnits K n) := (fun a : archGroup K n => (a : ArchUnits K n)) '' T with hT₀
  have hT₀c : IsCompact T₀ := hT.image continuous_subtype_val
  set T₁ : Set (ArchUnits K n) := (unipBall (K := K) (n := n) (k * R))⁻¹ * T₀ with hT₁
  have hT₁c : IsCompact T₁ := (isCompact_unipBall _).inv.mul hT₀c
  set L : Set (ArchMatrix K n) := (Units.val : ArchUnits K n → ArchMatrix K n) '' T₁ with hLdef
  have hLc : IsCompact L := hT₁c.image Units.continuous_val
  have hLu : L ⊆ {x | IsUnit x} := by
    rintro _ ⟨u, -, rfl⟩
    exact u.isUnit
  obtain ⟨χ, hχ, hχc, hχ1, hχu⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_bump hLc hLu
  have hκ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_test hf hχ hχc hχu
  obtain ⟨B, hB⟩ := exists_norm_altSum_le (contDiff_matExt hκ) (hasCompactSupport_matExt hκ.2) k
  obtain ⟨Rt, hRt⟩ := hT₀c.exists_bound_of_continuousOn
    (Units.continuous_val (M := ArchMatrix K n)).continuousOn
  refine ⟨max B 0 * max Rt 0 ^ k, mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _),
    fun Y hY hR C hC A hA => ?_⟩
  have hAT₀ : (A : ArchUnits K n) ∈ T₀ := ⟨A, hA, rfl⟩
  set v : Fin k → ArchMatrix K n := fun i => -(Y i * ((A : ArchUnits K n) : ArchMatrix K n)) with hv
  have hsum : ∑ ε, (altSign ε : ℂ) * f ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩ =
      altSum k (matExt K n fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a) v
        ((A : ArchUnits K n) : ArchMatrix K n) := by
    rw [altSum_eq_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [← val_inv_mul_eq hY (hC ε) (A : ArchUnits K n), zsmul_eq_mul]
    have hm := matExt_val (K := K) (n := n)
      (fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a)
      ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩
    have hin : (((C ε)⁻¹ * (A : ArchUnits K n) : ArchUnits K n) : ArchMatrix K n) ∈ L :=
      ⟨_, ⟨(C ε)⁻¹, Set.inv_mem_inv.2 (mem_unipBall_of_val_eq hY hR (hC ε)), _, hAT₀, rfl⟩, rfl⟩
    simp only at hm
    rw [hm, hχ1 _ hin, Complex.ofReal_one, one_mul]
  rw [hsum]
  refine (hB v _).trans ?_
  have hA' : ‖((A : ArchUnits K n) : ArchMatrix K n)‖ ≤ max Rt 0 := (hRt _ hAT₀).trans (le_max_left _ _)
  have hprod : ∏ i, ‖v i‖ ≤ (∏ i, ‖Y i‖) * max Rt 0 ^ k := by
    rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [hv, norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hA' (norm_nonneg _))
  calc B * ∏ i, ‖v i‖ ≤ max B 0 * ∏ i, ‖v i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ ≤ max B 0 * ((∏ i, ‖Y i‖) * max Rt 0 ^ k) := mul_le_mul_of_nonneg_left hprod (le_max_right _ _)
    _ = max B 0 * max Rt 0 ^ k * ∏ i, ‖Y i‖ := by ring

private def UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.DiffBdOn {K : Type} [Field K] [NumberField K] {n : ℕ} (a : CC K n) (k : ℕ) (R : ℝ)
    (s : Set (G1 K n)) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
    ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) →
    ∀ w ∈ s, ‖∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w)‖ ≤ c * ∏ i, ‖Y i‖

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_split {K : Type} [Field K] [NumberField K] {n : ℕ} {g : G1 K n}
    {u : AdelicGLn.integralFiniteGL K n} (hu : finPart K n (g : AdelicGLn.AdelicGL K n) = u) :
    g = finOne K n u * archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) := by
  have hd : detA K n (infPart K n (g : AdelicGLn.AdelicGL K n)) = 1 :=
    detA_infPart (hu ▸ u.2)
  have hp : (archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) : AdelicGLn.AdelicGL K n) =
      infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n)) := by
    rw [← retract_infEmb, coe_retractOne]
    have : detModule K n (infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n))) = 1 := hd
    rw [this, map_one, inv_one, mul_one]
  rw [← archimedeanProjection_mul_finiteEmbedding_comm]
  ext1
  rw [Subgroup.coe_mul, hp, coe_finOne, ← hu, infEmb_infPart_mul_finEmb_finPart]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (a : CC K n), IsLeftSmooth a → ∀ (k : ℕ) (R : ℝ), ∃ c : ℝ, ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) → ∀ w : G1 K n,
        ‖∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w)‖ ≤ c * ∏ i, ‖Y i‖ := by
  intro K _ _ n a ha k R
  obtain ⟨hsm, U, hUo, hU⟩ := ha
  set Ω : Set (G1 K n) := (archProj K n '' unipBall (K := K) (n := n) (k * R)) * tsupport a with hΩdef
  have hΩ : IsCompact Ω :=
    ((isCompact_unipBall _).image continuous_archProj).mul a.hasCompactSupport
  have key : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.DiffBdOn a k R Ω := by
    refine hΩ.induction_on ?_ ?_ ?_ ?_
    · exact ⟨0, le_rfl, fun _ _ _ _ _ w hw => absurd hw (Set.notMem_empty w)⟩
    · rintro s t hst ⟨c, hc, h⟩
      exact ⟨c, hc, fun Y hY hR C hC w hw => h Y hY hR C hC w (hst hw)⟩
    · rintro s t ⟨c, hc, h⟩ ⟨d, hd, h'⟩
      refine ⟨max c d, le_max_of_le_left hc, fun Y hY hR C hC w hw => ?_⟩
      have hp : 0 ≤ ∏ i, ‖Y i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      rcases hw with hw | hw
      · exact (h Y hY hR C hC w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
      · exact (h' Y hY hR C hC w hw).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)
    · intro x _
      have hcm : Continuous fun w : G1 K n => w * x⁻¹ := continuous_id.mul continuous_const
      set V : Set (G1 K n) := (fun w : G1 K n => w * x⁻¹) ⁻¹' finUSet U hUo with hV
      have hVc : IsClopen V := (isClopen_finUSet U hUo).preimage hcm
      have hxV : x ∈ V := by
        show x * x⁻¹ ∈ finUSet U hUo
        rw [mul_inv_cancel]
        show finPart K n ((1 : G1 K n) : AdelicGLn.AdelicGL K n) ∈ (finOpenSubgroup U hUo : Set _)
        rw [Subgroup.coe_one, map_one]
        exact one_mem (finOpenSubgroup U hUo)
      refine ⟨Ω ∩ V, inter_mem_nhdsWithin _ (hVc.isOpen.mem_nhds hxV), ?_⟩
      have hTc : IsCompact ((fun w : G1 K n => infPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)) '' (Ω ∩ V)) :=
        (hΩ.inter_right hVc.isClosed).image
          (continuous_infPart.comp (continuous_subtype_val.comp hcm))
      obtain ⟨c, hc, h⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_local (hsm x) hTc k R
      refine ⟨c, hc, fun Y hY hR C hC w hw => ?_⟩
      have hwV : finPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) ∈
          (finOpenSubgroup U hUo : Set (AdelicGLn.FiniteAdelicGL K n)) := hw.2
      rw [coe_openSubgroupOf] at hwV
      obtain ⟨u, huU, hu⟩ := hwV
      have hg := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_split hu.symm
      obtain ⟨b, hbdef⟩ : ∃ b, b = infPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) := ⟨_, rfl⟩
      rw [← hbdef] at hg
      have hb := h Y hY hR C hC b ⟨w, hw, hbdef.symm⟩
      have hw' : w = finOne K n u * archP K n b * x := by
        rw [← hg, inv_mul_cancel_right]
      have hterm : ∀ ε, a ((archProj K n (C ε))⁻¹ * w) =
          a (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) := by
        intro ε
        have hpb : archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ =
            (archProj K n (C ε))⁻¹ * archP K n b := by
          rw [archimedeanProjection_apply, map_mul, map_inv, archimedeanProjection_apply]
        have e : (archProj K n (C ε))⁻¹ * w =
            finOne K n u * (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) := by
          rw [hpb, hw', ← mul_assoc, ← mul_assoc, ← mul_assoc, archProj_inv_mul_finOne]
          simp only [mul_assoc]
        rw [e, hU u huU]
      have hs : ∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w) =
          ∑ ε, (altSign ε : ℂ) * a (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) :=
        Finset.sum_congr rfl fun ε _ => by rw [hterm ε]
      rw [hs]
      exact hb
  obtain ⟨c, hc, h⟩ := key
  refine ⟨c, fun Y hY hR C hC w => ?_⟩
  by_cases hw : w ∈ Ω
  · exact h Y hY hR C hC w hw
  · have hz : ∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w) = 0 := by
      refine Finset.sum_eq_zero fun ε _ => ?_
      have : (archProj K n (C ε))⁻¹ * w ∉ tsupport a := fun hs =>
        hw ⟨archProj K n (C ε), ⟨C ε, mem_unipBall_of_val_eq hY hR (hC ε), rfl⟩, _, hs, mul_inv_cancel_left _ _⟩
      rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
    rw [hz, norm_zero]
    exact mul_nonneg hc (Finset.prod_nonneg fun i _ => norm_nonneg _)
