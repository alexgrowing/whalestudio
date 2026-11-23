import Mathlib
import GroundTheory.AutomorphicForms.ReductionHeight
import GroundTheory.AutomorphicForms.ReductionIdele
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.GlobalFields.IdeleGroups.Restricted
import GroundTheory.GlobalFields.IdeleGroups.UnitBound

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem isOpen_setOf_forall_not_mem_imp (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen {g : AdelicGLn.AdelicGL K n |
      ∀ v, v ∉ S → finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n} := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) => GL (Fin n) (v.adicCompletion K))
    (A := fun v => (GLnLocal.integralGL (v.adicCompletion K) n : Set _))
    (fun v => GLnLocal.isOpen_integralGL (v.adicCompletion K) n) (p := fun v => v ∉ S)
  exact (h.preimage continuous_snd).preimage (AdelicGLn.restrictedProductEquiv K n).continuous

theorem exists_finite_forall_mem_integralGL {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ g ∈ C, ∀ v, v ∉ S →
      finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  classical
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 K)) => {g : AdelicGLn.AdelicGL K n |
      ∀ v, v ∉ S → finAt v g ∈ GLnLocal.integralGL (v.adicCompletion K) n})
    (fun S => isOpen_setOf_forall_not_mem_imp S) (fun g _ => by
      have hfin := Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n g)
      refine mem_iUnion.2 ⟨hfin.toFinset, fun v hv => ?_⟩
      by_contra h
      exact hv (hfin.mem_toFinset.2 h))
  refine ⟨T.sup id, fun g hg v hv => ?_⟩
  obtain ⟨S, hS, hgS⟩ := mem_iUnion₂.1 (hT hg)
  exact hgS v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

theorem finprod_le_finprod_of_nonneg {α : Type*} {f g : α → ℝ}
    (hf : (Function.mulSupport f).Finite) (hg : (Function.mulSupport g).Finite)
    (h0 : ∀ a, 0 ≤ f a) (h : ∀ a, f a ≤ g a) : ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf.toFinset ∪ hg.toFinset)
      (fun a ha => Finset.mem_coe.2 (Finset.mem_union_left _ (hf.mem_toFinset.2 ha))),
    finprod_eq_prod_of_mulSupport_subset g (s := hf.toFinset ∪ hg.toFinset)
      (fun a ha => Finset.mem_coe.2 (Finset.mem_union_right _ (hg.mem_toFinset.2 ha)))]
  exact Finset.prod_le_prod (fun a _ => h0 a) fun a _ => h a

theorem adelicNorm_le_of_local {y y' : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (hy' : HasFiniteContent y') (a : InfinitePlace K → ℝ) (b : HeightOneSpectrum (𝓞 K) → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hinf : ∀ w, euclidNorm (infComp w y) ≤ a w * euclidNorm (infComp w y'))
    (hb1 : ∀ v, v ∉ S → b v = 1)
    (hfin : ∀ v, ‖finComp v y‖ ≤ b v * ‖finComp v y'‖) :
    adelicNorm y ≤ (∏ w, a w ^ w.mult) * (∏ v ∈ S, b v) * adelicNorm y' := by
  have hbS : (Function.mulSupport b).Finite :=
    S.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (hb1 v h)
  have hprod : ∏ᶠ v, b v = ∏ v ∈ S, b v :=
    finprod_eq_prod_of_mulSupport_subset b fun v hv => by
      by_contra h
      exact hv (hb1 v h)
  rw [adelicNorm, adelicNorm]
  have hinf' : ∏ w, euclidNorm (infComp w y) ^ w.mult ≤
      (∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg (euclidNorm_nonneg _) _) fun w _ => by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (euclidNorm_nonneg _) (hinf w) _
  have hfin' : ∏ᶠ v, ‖finComp v y‖ ≤ (∏ v ∈ S, b v) * ∏ᶠ v, ‖finComp v y'‖ := by
    rw [← hprod, ← finprod_mul_distrib hbS hy'.finite_mulSupport]
    refine finprod_le_finprod_of_nonneg hy.finite_mulSupport ?_ (fun _ => norm_nonneg _) hfin
    exact (hbS.union hy'.finite_mulSupport).subset (Function.mulSupport_mul _ _)
  have h1 : 0 ≤ ∏ᶠ v, ‖finComp v y‖ := finprod_nonneg fun _ => norm_nonneg _
  have h2 : 0 ≤ (∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult :=
    le_trans (Finset.prod_nonneg fun _ _ => pow_nonneg (euclidNorm_nonneg _) _) hinf'
  calc (∏ w, euclidNorm (infComp w y) ^ w.mult) * ∏ᶠ v, ‖finComp v y‖
      ≤ ((∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult) *
          ((∏ v ∈ S, b v) * ∏ᶠ v, ‖finComp v y'‖) := mul_le_mul hinf' hfin' h1 h2
    _ = _ := by ring

theorem norm_vecMul_le_of_norm_le (v : HeightOneSpectrum (𝓞 K))
    {M : Matrix (Fin n) (Fin n) (v.adicCompletion K)} {m : ℝ} (hm : 0 ≤ m)
    (hM : ∀ i j, ‖M i j‖ ≤ m) (z : Fin n → v.adicCompletion K) : ‖z ᵥ* M‖ ≤ m * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hm (norm_nonneg z))).2 fun j => ?_
  simp only [vecMul, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hm (norm_nonneg z))
    fun i _ => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul (hM i j) (norm_le_pi_norm z i) (norm_nonneg _) hm

theorem euclidNorm_vecMul_le {E : Type*} [NormedField E] {M : Matrix (Fin n) (Fin n) E} {m : ℝ}
    (hm : 0 ≤ m) (hM : ∀ i j, ‖M i j‖ ≤ m) (z : Fin n → E) :
    euclidNorm (z ᵥ* M) ≤ √n * (n * m) * euclidNorm z := by
  refine (euclidNorm_le_sqrt_mul _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (by positivity [euclidNorm_nonneg z])).2 fun j => ?_
  simp only [vecMul, dotProduct]
  calc ‖∑ i, z i * M i j‖ ≤ ∑ i, ‖z i * M i j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, m * euclidNorm z := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul (hM i j) (norm_le_euclidNorm z i) (norm_nonneg _) hm
    _ = n * m * euclidNorm z := by simp [mul_assoc]

theorem exists_one_le_bound {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsCompact C)
    {f : X → ℝ} (hf : Continuous f) : ∃ m : ℝ, 1 ≤ m ∧ ∀ x ∈ C, f x ≤ m := by
  obtain ⟨m, hm⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max m 1, le_max_right _ _, fun x hx =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hm x hx).trans (le_max_left _ _))⟩

theorem continuous_infAt (w : InfinitePlace K) :
    Continuous (infAt (n := n) w : AdelicGLn.AdelicGL K n → GL (Fin n) w.Completion) :=
  (continuous_apply w).comp (continuous_fst.comp (AdelicGLn.restrictedProductEquiv K n).continuous)

theorem continuous_finAt (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finAt (n := n) v : AdelicGLn.AdelicGL K n → GL (Fin n) (v.adicCompletion K)) :=
  (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (AdelicGLn.restrictedProductEquiv K n).continuous)

theorem continuous_GL_apply {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (i j : Fin n) : Continuous fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j :=
  (continuous_apply_apply i j).comp (Units.continuous_val (M := Matrix (Fin n) (Fin n) R))

theorem exists_pos_le_height {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ C, ∀ x : Fin n → K, x ≠ 0 → ε ≤ height g x := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun g _ x hx => absurd (Subsingleton.elim x 0) hx⟩
  obtain ⟨S, hS⟩ := exists_finite_forall_mem_integralGL hC

  have hinf : ∀ w : InfinitePlace K, ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n,
      ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖ ≤ m := fun w => by
    obtain ⟨m, hm1, hm⟩ := exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n =>
      ∑ i, ∑ j, ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((continuous_GL_apply i j).comp ((continuous_infAt w).inv)).norm)
    refine ⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩
    exact (Finset.single_le_sum (f := fun j => ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖((infAt w g)⁻¹ : GL (Fin n) w.Completion) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℝ, 1 ≤ m ∧ ∀ g ∈ C, ∀ i j : Fin n,
      ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖ ≤ m := fun v => by
    obtain ⟨m, hm1, hm⟩ := exists_one_le_bound hC (f := fun g : AdelicGLn.AdelicGL K n =>
      ∑ i, ∑ j, ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖)
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((continuous_GL_apply i j).comp ((continuous_finAt v).inv)).norm)
    refine ⟨m, hm1, fun g hg i j => le_trans ?_ (hm g hg)⟩
    exact (Finset.single_le_sum (f := fun j => ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖((finAt v g)⁻¹ : GL (Fin n) (v.adicCompletion K)) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  choose a ha1 ha using hinf
  choose b hb1 hb using hfin
  set b' : HeightOneSpectrum (𝓞 K) → ℝ := fun v => if v ∈ S then b v else 1 with hb'
  set P : ℝ := (∏ w, (√n * (n * a w)) ^ w.mult) * ∏ v ∈ S, b' v with hP
  have hPpos : 0 < P := by
    refine mul_pos (Finset.prod_pos fun w _ => pow_pos ?_ _) (Finset.prod_pos fun v _ => ?_)
    · have : (0 : ℝ) < n := Nat.cast_pos.2 hn
      exact mul_pos (Real.sqrt_pos.2 this) (mul_pos this (lt_of_lt_of_le one_pos (ha1 w)))
    · rw [hb']
      dsimp only
      split_ifs
      exact lt_of_lt_of_le one_pos (hb1 v)
  refine ⟨P⁻¹, inv_pos.2 hPpos, fun g hg x hx => ?_⟩
  rw [inv_le_iff_one_le_mul₀' hPpos]
  set y := ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hy
  have hxy : ratVec x = y ᵥ* ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    rw [hy, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  refine (one_le_adelicNorm_ratVec hx).trans ?_
  rw [hxy]
  refine (adelicNorm_le_of_local ((hasFiniteContent_height g hx).vecMul g⁻¹)
    (hasFiniteContent_height g hx) (fun w => √n * (n * a w)) b' S (fun w => ?_)
    (fun v hv => by rw [hb']; dsimp only; rw [if_neg hv]) (fun v => ?_)).trans (le_of_eq rfl)
  · rw [infComp_vecMul_GL, show infAt w g⁻¹ = (infAt w g)⁻¹ by simp [infAt, map_inv]]
    exact euclidNorm_vecMul_le (zero_le_one.trans (ha1 w)) (ha w g hg) _
  · rw [finComp_vecMul_GL, show finAt v g⁻¹ = (finAt v g)⁻¹ by
      simp [finAt, map_inv, RestrictedProduct.inv_apply]]
    rw [hb']
    dsimp only
    split_ifs with hv
    · exact norm_vecMul_le_of_norm_le v (zero_le_one.trans (hb1 v)) (hb v g hg) _
    · rw [norm_vecMul_integralGL v (inv_mem (hS g hg v hv)), one_mul]

theorem finite_setOf_algebraMap_mem {D : Set 𝔸[K]} (hD : IsCompact D) :
    {k : K | algebraMap K 𝔸[K] k ∈ D}.Finite := by
  have := discreteTopology_principalSubgroup K
  have hc : IsCompact ((Subtype.val : AdeleRing.principalSubgroup (𝓞 K) K → 𝔸[K]) ⁻¹' D) :=
    (isClosed_principalSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hD
  let f : K → AdeleRing.principalSubgroup (𝓞 K) K := fun k => ⟨algebraMap K 𝔸[K] k, k, rfl⟩
  have hf : Function.Injective f := fun a b h =>
    AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Subtype.val h)
  exact (hc.finite_of_discrete.preimage hf.injOn).subset fun k hk => hk

theorem finite_setOf_ratVec_mem {D : Set (Fin n → 𝔸[K])} (hD : IsCompact D) :
    {x : Fin n → K | ratVec x ∈ D}.Finite := by
  refine (Set.Finite.pi (t := fun i => {k : K | algebraMap K 𝔸[K] k ∈ (fun y => y i) '' D})
    fun i => finite_setOf_algebraMap_mem (hD.image (continuous_apply i))).subset ?_
  intro x hx i _
  exact ⟨ratVec x, hx, rfl⟩

theorem mem_of_norm_le_one (v : HeightOneSpectrum (𝓞 K)) {x : v.adicCompletion K} (hx : ‖x‖ ≤ 1) :
    x ∈ v.adicCompletionIntegers K :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).2
    ((Valued.toNormedField.norm_le_one_iff).1 hx)

def mkIdele (a : ∀ w : InfinitePlace K, w.Completion)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0)
    (hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1) : IdeleGroup K :=
  (prodRestrictedEquiv K).symm
    (MulEquiv.piUnits.symm fun w => Units.mk0 (a w) (ha w),
     ⟨fun v => Units.mk0 (b v) (hb v), by
        filter_upwards [hb1] with v hv
        rw [SetLike.mem_coe, Submonoid.mem_units_iff]
        refine ⟨mem_of_norm_le_one v hv.le, mem_of_norm_le_one v ?_⟩
        rw [Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, hv, inv_one]⟩)

theorem mkIdele_fst (a : ∀ w : InfinitePlace K, w.Completion)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0)
    (hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1) (w : InfinitePlace K) :
    ((mkIdele a b ha hb hb1 : IdeleGroup K) : 𝔸[K]).1 w = a w := by
  rw [← prodRestrictedEquiv_apply_fst, mkIdele, ContinuousMulEquiv.apply_symm_apply]
  rfl

theorem mkIdele_snd (a : ∀ w : InfinitePlace K, w.Completion)
    (b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (ha : ∀ w, a w ≠ 0) (hb : ∀ v, b v ≠ 0)
    (hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1) (v : HeightOneSpectrum (𝓞 K)) :
    ((mkIdele a b ha hb hb1 : IdeleGroup K) : 𝔸[K]).2 v = b v := by
  rw [← prodRestrictedEquiv_apply_snd, mkIdele, ContinuousMulEquiv.apply_symm_apply]
  rfl

theorem exists_norm_eq_norm {E : Type*} [SeminormedAddCommGroup E] {z : Fin n → E} (hz : z ≠ 0) :
    ∃ i, ‖z i‖ = ‖z‖ := by
  have : Nonempty (Fin n) := by
    by_contra h
    exact hz (funext fun i => (h ⟨i⟩).elim)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z j‖) Finset.univ_nonempty
  exact ⟨i, le_antisymm (norm_le_pi_norm z i)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ j))⟩

theorem exists_idele_norm_eq {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (hinf : ∀ w, infComp w y ≠ 0) (hfin : ∀ v, finComp v y ≠ 0) :
    ∃ s : IdeleGroup K, (∀ w, ‖(s : 𝔸[K]).1 w‖ = ‖infComp w y‖) ∧
      ∀ v, ‖(s : 𝔸[K]).2 v‖ = ‖finComp v y‖ := by
  classical
  choose i hi using fun w => exists_norm_eq_norm (hinf w)
  choose j hj using fun v => exists_norm_eq_norm (hfin v)
  have ha : ∀ w, infComp w y (i w) ≠ 0 := fun w h => hinf w (norm_eq_zero.1 (by rw [← hi w, h, norm_zero]))
  have hb0 : ∀ v, finComp v y (j v) ≠ 0 := fun v h =>
    hfin v (norm_eq_zero.1 (by rw [← hj v, h, norm_zero]))
  set b : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K :=
    fun v => if ‖finComp v y‖ = 1 then 1 else finComp v y (j v) with hbdef
  have hb : ∀ v, b v ≠ 0 := fun v => by
    rw [hbdef]; dsimp only; split_ifs
    · exact one_ne_zero
    · exact hb0 v
  have hbn : ∀ v, ‖b v‖ = ‖finComp v y‖ := fun v => by
    rw [hbdef]; dsimp only; split_ifs with h
    · rw [h, norm_one]
    · exact hj v
  have hb1 : ∀ᶠ v in cofinite, ‖b v‖ = 1 := by
    filter_upwards [hy] with v hv
    rw [hbn, hv]
  exact ⟨mkIdele (fun w => infComp w y (i w)) b ha hb hb1,
    fun w => by rw [mkIdele_fst, hi], fun v => by rw [mkIdele_snd, hbn]⟩

theorem infComp_ne_zero_of_adelicNorm_pos {y : Fin n → 𝔸[K]} (h : 0 < adelicNorm y)
    (w : InfinitePlace K) : infComp w y ≠ 0 := by
  intro h0
  apply h.ne'
  have h1 : euclidNorm (infComp w y) = 0 := by rw [h0]; simp [euclidNorm]
  rw [adelicNorm, Finset.prod_eq_zero (Finset.mem_univ w)
    (by rw [h1, zero_pow InfinitePlace.mult_ne_zero]), zero_mul]

theorem finComp_ne_zero_of_adelicNorm_pos {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (h : 0 < adelicNorm y) (v : HeightOneSpectrum (𝓞 K)) : finComp v y ≠ 0 := by
  intro h0
  apply h.ne'
  have hv : v ∈ hy.finite_mulSupport.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, h0, norm_zero]
    exact zero_ne_one
  rw [adelicNorm, finprod_eq_prod_of_mulSupport_subset _
    (s := hy.finite_mulSupport.toFinset) (fun u hu => hy.finite_mulSupport.mem_toFinset.2 hu),
    Finset.prod_eq_zero hv (by rw [h0, norm_zero]), mul_zero]

theorem norm_mul_le_one_of_mul_eq_one {E : Type*} [NormedField E] {a a' b : E} (h : a * a' = 1)
    (hb : ‖b‖ ≤ ‖a‖) : ‖a' * b‖ ≤ 1 := by
  have ha : ‖a‖ * ‖a'‖ = 1 := by rw [← norm_mul, h, norm_one]
  rw [norm_mul]
  calc ‖a'‖ * ‖b‖ ≤ ‖a'‖ * ‖a‖ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = 1 := by rw [mul_comm, ha]

theorem exists_finite_smul_mem_of_height_le {C : Set (AdelicGLn.AdelicGL K n)} (hC : IsCompact C)
    (B : ℝ) : ∃ F : Set (Fin n → K), F.Finite ∧ ∀ g ∈ C, ∀ x : Fin n → K, x ≠ 0 →
      height g x ≤ B → ∃ c : K, c ≠ 0 ∧ c • x ∈ F := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, Set.finite_empty, fun g _ x hx => absurd (Subsingleton.elim x 0) hx⟩
  obtain ⟨ε, hε, hεC⟩ := exists_pos_le_height hC
  set P₀ : ℝ := ∏ w : InfinitePlace K, √(n : ℝ) ^ w.mult with hP₀
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hP₀pos : 0 < P₀ := Finset.prod_pos fun w _ => pow_pos (Real.sqrt_pos.2 hn') _
  obtain ⟨S, hS, hSmem⟩ :=
    exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := K) (div_pos hε hP₀pos) B
  set U₁ : Set 𝔸[K] := {a : InfiniteAdeleRing K | ∀ w, ‖a w‖ ≤ 1} ×ˢ
    (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) with hU₁def
  have hU₁ : IsCompact U₁ := by
    refine IsCompact.prod ?_ (isCompact_integralFiniteAdeles K)
    have : {a : InfiniteAdeleRing K | ∀ w, ‖a w‖ ≤ 1} =
        Set.pi univ (fun w : InfinitePlace K => Metric.closedBall (0 : w.Completion) 1) := by
      ext a
      exact ⟨fun h w _ => mem_closedBall_zero_iff.2 (h w),
        fun h w => mem_closedBall_zero_iff.1 (h w (mem_univ w))⟩
    rw [this]
    exact isCompact_univ_pi fun w => isCompact_closedBall 0 1
  set U : Set (Fin n → 𝔸[K]) := Set.pi univ fun _ => U₁ with hUdef
  have hU : IsCompact U := isCompact_univ_pi fun _ => hU₁
  set D := (fun p : IdeleGroup K × (Fin n → 𝔸[K]) => ((p.1 : 𝔸[K]) • p.2)) '' (S ×ˢ U) with hDdef
  have hD : IsCompact D := (hS.prod hU).image
    ((Units.continuous_val.comp continuous_fst).smul continuous_snd)
  set D' := (fun p : (Fin n → 𝔸[K]) × AdelicGLn.AdelicGL K n =>
    p.1 ᵥ* ((p.2⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) '' (D ×ˢ C) with hD'def
  have hD' : IsCompact D' := (hD.prod hC).image (Continuous.matrix_vecMul continuous_fst
    ((Units.continuous_val (M := Matrix (Fin n) (Fin n) 𝔸[K])).comp (continuous_inv.comp continuous_snd)))
  refine ⟨{x | ratVec x ∈ D'}, finite_setOf_ratVec_mem hD', fun g hg x hx hxB => ?_⟩
  set y := ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K]) with hy
  have hyc : HasFiniteContent y := hasFiniteContent_height g hx
  have hypos : 0 < adelicNorm y := lt_of_lt_of_le hε (hεC g hg x hx)
  obtain ⟨s, hsw, hsv⟩ := exists_idele_norm_eq hyc (infComp_ne_zero_of_adelicNorm_pos hypos)
    (finComp_ne_zero_of_adelicNorm_pos hyc hypos)
  have hmod : (ideleModule K s : ℝ) =
      (∏ w, ‖infComp w y‖ ^ w.mult) * ∏ᶠ v, ‖finComp v y‖ := by
    rw [ideleModule_eq]
    simp_rw [hsw, hsv]
  have hfp : 0 ≤ ∏ᶠ v, ‖finComp v y‖ := finprod_nonneg fun _ => norm_nonneg _
  have hup : (ideleModule K s : ℝ) ≤ B := by
    refine le_trans ?_ hxB
    rw [hmod, height, ← hy, adelicNorm]
    exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_euclidNorm_pi _) _) hfp
  have hlow : ε / P₀ ≤ (ideleModule K s : ℝ) := by
    rw [div_le_iff₀ hP₀pos]
    refine (hεC g hg x hx).trans ?_
    rw [hmod, height, ← hy, adelicNorm, mul_comm _ P₀, ← mul_assoc, hP₀, ← Finset.prod_mul_distrib]
    refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun _ _ => pow_nonneg (euclidNorm_nonneg _) _)
      fun w _ => ?_) hfp
    rw [← mul_pow]
    exact pow_le_pow_left₀ (euclidNorm_nonneg _) (euclidNorm_le_sqrt_mul _) _
  obtain ⟨c, hc⟩ := hSmem s hlow hup
  refine ⟨(c : K), c.ne_zero, ?_⟩
  have hsinv : ((s : 𝔸[K]) * ((s⁻¹ : IdeleGroup K) : 𝔸[K])) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hz : ((s⁻¹ : IdeleGroup K) : 𝔸[K]) • y ∈ U := by
    intro i _
    refine ⟨fun w => ?_, ?_⟩
    · show ‖(((s⁻¹ : IdeleGroup K) : 𝔸[K]) * y i).1 w‖ ≤ 1
      rw [adele_fst_mul_apply]
      exact norm_mul_le_one_of_mul_eq_one (infinite_mul_inv s w)
        ((norm_le_pi_norm (infComp w y) i).trans (hsw w).ge)
    · show (((s⁻¹ : IdeleGroup K) : 𝔸[K]) * y i).2 ∈ integralFiniteAdeles (𝓞 K) K
      rw [mem_integralFiniteAdeles]
      intro v
      rw [adele_snd_mul_apply]
      exact mem_of_norm_le_one v (norm_mul_le_one_of_mul_eq_one (finite_mul_inv s v)
        ((norm_le_pi_norm (finComp v y) i).trans (hsv v).ge))
  refine ⟨(algebraMap K 𝔸[K] (c : K) • y, g), ⟨⟨(diagonal K c * s, ((s⁻¹ : IdeleGroup K) : 𝔸[K]) • y),
    ⟨hc, hz⟩, ?_⟩, hg⟩, ?_⟩
  · show ((diagonal K c * s : IdeleGroup K) : 𝔸[K]) • (((s⁻¹ : IdeleGroup K) : 𝔸[K]) • y) =
      algebraMap K 𝔸[K] (c : K) • y
    rw [smul_smul, Units.val_mul, mul_assoc, hsinv, mul_one, coe_diagonal]
  · show (algebraMap K 𝔸[K] (c : K) • y) ᵥ* ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ratVec ((c : K) • x)
    rw [smul_vecMul, hy, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one,
      ratVec_smul]

theorem exists_height_min (hn : 0 < n) (g : AdelicGLn.AdelicGL K n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∀ y : Fin n → K, y ≠ 0 → height g x ≤ height g y := by
  classical
  set e : Fin n → K := Pi.single ⟨0, hn⟩ 1 with he
  have he0 : e ≠ 0 := fun h => by
    have := congrFun h ⟨0, hn⟩
    simp [he] at this
  obtain ⟨F, hF, hFmem⟩ := exists_finite_smul_mem_of_height_le (isCompact_singleton (x := g))
    (height g e)
  set T := {x ∈ F | x ≠ 0} with hT
  obtain ⟨c₀, hc₀, hc₀F⟩ := hFmem g rfl e he0 le_rfl
  have hTne : T.Nonempty := ⟨c₀ • e, hc₀F, smul_ne_zero hc₀ he0⟩
  obtain ⟨x₀, hx₀T, hx₀⟩ := Set.exists_min_image T (height g) (hF.subset fun x hx => hx.1) hTne
  refine ⟨x₀, hx₀T.2, fun y hy => ?_⟩
  by_cases hyB : height g y ≤ height g e
  · obtain ⟨c, hc, hcF⟩ := hFmem g rfl y hy hyB
    calc height g x₀ ≤ height g (c • y) := hx₀ _ ⟨hcF, smul_ne_zero hc hy⟩
      _ = height g y := height_smul g hy hc
  · calc height g x₀ ≤ height g (c₀ • e) := hx₀ _ ⟨hc₀F, smul_ne_zero hc₀ he0⟩
      _ = height g e := height_smul g he0 hc₀
      _ ≤ height g y := (not_le.1 hyB).le

end Reduction

end

end GroundTheory.Automorphic
