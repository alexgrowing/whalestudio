import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisSlash

noncomputable section

open UpperHalfPlane EisensteinSeries CongruenceSubgroup Matrix Filter Complex ModularForm
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Sd

private def gS (S : Set (Fin 2 → ℤ)) (k : ℤ) (z : ℍ) : ℂ := ∑' x : S, eisSummand k x z

private lemma gS_tendsto {k : ℤ} (hk : 3 ≤ k) (S : Set (Fin 2 → ℤ)) :
    TendstoLocallyUniformly (fun (s : Finset S) ↦ (∑ x ∈ s, eisSummand k x ·))
      (gS S k ·) Filter.atTop := by
  have hk' : (2 : ℝ) < k := by norm_cast
  have p_sum : Summable fun x : S ↦ ‖x.val‖ ^ (-k) :=
    mod_cast (summable_one_div_norm_rpow hk').subtype (· ∈ S)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, gS]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  refine (tendstoUniformlyOn_tsum (hu := p_sum.mul_left <| r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))
    (fun p z hz ↦ ?_)).mono HABK
  simpa only [eisSummand, one_div, ← _root_.zpow_neg, norm_zpow, ← Real.rpow_intCast,
    Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) p hB hz

private lemma gS_tendstoOn {k : ℤ} (hk : 3 ≤ k) (S : Set (Fin 2 → ℤ)) :
    TendstoLocallyUniformlyOn (fun (s : Finset S) ↦
      ↑ₕ(fun (z : ℍ) ↦ ∑ x ∈ s, eisSummand k x z)) (↑ₕ(gS S k))
          Filter.atTop {z : ℂ | 0 < z.im} := by
  rw [← upperHalfPlaneSet, ← range_coe, ← Set.image_univ]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    apply gS_tendsto hk
  · simp only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ,
      Set.mapsTo_range_iff, Set.mem_univ, forall_const]

private lemma gS_mdiff {k : ℤ} (hk : 3 ≤ k) (S : Set (Fin 2 → ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gS S k) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  exact (gS_tendstoOn hk S).differentiableOn
    (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun _ _ ↦ eisSummand_extension_differentiableOn _ _) isOpen_upperHalfPlaneSet

private def vE (γ : SL(2, ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun v := v ᵥ* γ.1
  invFun v := v ᵥ* (γ⁻¹).1
  left_inv v := by
    have : γ.1 * (γ⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel γ)
    simp only [vecMul_vecMul, this, vecMul_one]
  right_inv v := by
    have : (γ⁻¹).1 * γ.1 = 1 := congrArg Subtype.val (inv_mul_cancel γ)
    simp only [vecMul_vecMul, this, vecMul_one]

private lemma gS_slash (S : Set (Fin 2 → ℤ)) (k : ℤ) (γ : SL(2, ℤ)) :
    gS S k ∣[k] γ = gS (vE γ '' S) k := by
  ext1 z
  simp_rw [SL_slash_apply, _root_.zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    gS, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (Equiv.Set.image (vE γ) S (vE γ).injective).tsum_eq (eisSummand k · z)

private lemma gS_norm_le (S : Set (Fin 2 → ℤ)) (k : ℤ) (hk : 3 ≤ k) (z : ℍ) :
    ‖gS S k z‖ ≤ ∑' (x : Fin 2 → ℤ), ‖eisSummand k x z‖ := by
  unfold gS
  exact le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (Summable.tsum_subtype_le (fun x : Fin 2 → ℤ => ‖eisSummand k x z‖) _ (fun _ => norm_nonneg _)
      (summable_norm_eisSummand hk z))

private lemma tsum_norm_eisenstein_translate (k n : ℤ) (z : ℍ) :
    ∑' (x : Fin 2 → ℤ), ‖eisSummand k x (ModularGroup.T ^ n • z)‖ =
      ∑' (x : Fin 2 → ℤ), ‖eisSummand k x z‖ := by
  have key : ∀ x : Fin 2 → ℤ, eisSummand k x (ModularGroup.T ^ n • z) =
      eisSummand k (vE (ModularGroup.T ^ n) x) z := by
    intro x
    have hx : vE (ModularGroup.T ^ n) x = ![x 0, x 0 * n + x 1] := by
      ext i
      fin_cases i <;> simp [vE, ModularGroup.coe_T_zpow, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Matrix.vecHead, Matrix.vecTail]
    rw [hx]
    simp only [eisSummand, ModularGroup.coe_T_zpow_smul_eq]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_add,
      Int.cast_mul]
    ring
  simp_rw [key]
  exact (vE (ModularGroup.T ^ n)).tsum_eq (fun y => ‖eisSummand k y z‖)

private lemma gS_bdd (S : Set (Fin 2 → ℤ)) {k : ℤ} (hk : 3 ≤ k) : IsBoundedAtImInfty (gS S k) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hk' : (2 : ℝ) < k := by norm_cast
  refine ⟨∑' (x : Fin 2 → ℤ), r ⟨⟨(1 : ℝ), 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := ModularGroup_T_zpow_mem_verticalStrip z (N := 1) Nat.one_pos
  simp only [Nat.cast_one, one_mul] at hn
  apply le_trans (gS_norm_le S k hk z)
  rw [← tsum_norm_eisenstein_translate k n z]
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
  · exact_mod_cast (summable_one_div_norm_rpow hk').mul_left <|
      r ⟨⟨(1 : ℝ), 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right 1 hz hn)

private lemma eisFun_eq (N k : ℕ) (a : ZMod N) :
    eisFun N k a = ((N : ℂ) ^ k / lipC k) •
      gS {v : Fin 2 → ℤ | (v 0 : ZMod N) = 0 ∧ (v 1 : ZMod N) = a} k := by
  funext z
  simp only [eisFun, gS, Pi.smul_apply, smul_eq_mul]
  congr 1
  let e : {v : ℤ × ℤ // ((v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = a)} ≃
      {v : Fin 2 → ℤ | (v 0 : ZMod N) = 0 ∧ (v 1 : ZMod N) = a} :=
    (finTwoArrowEquiv ℤ).symm.subtypeEquiv fun v => by simp
  rw [← e.tsum_eq]
  congr 1

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.eisMF :
    UpperTheory.V.Sd.EisMF := by
  intro N k _ hk a
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  refine ⟨{ toFun := eisFun N k a, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨A, (hA : A ∈ Gamma1 N), rfl⟩
    have h := eisSlash N k hk a A (Gamma1_in_Gamma0 N hA)
    rw [((Gamma1_mem N A).mp hA).2.1, mul_one] at h
    exact h
  · show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (eisFun N k a)
    rw [eisFun_eq]
    exact (gS_mdiff hk' _).const_smul _
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    show IsBoundedAtImInfty (eisFun N k a ∣[(k : ℤ)] γ)
    rw [eisFun_eq, SL_smul_slash, gS_slash]
    exact (gS_bdd _ hk').smul _
