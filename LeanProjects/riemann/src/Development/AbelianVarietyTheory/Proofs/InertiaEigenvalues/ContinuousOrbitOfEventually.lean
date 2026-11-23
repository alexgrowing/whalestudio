import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAdicModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinfStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Topology Filter

namespace GlobalTheory.AinfCont

variable {l : ℕ} [Fact l.Prime]

section Ainf

variable {P : LocPrime l} (AI : LocAinf l P)

theorem exists_eq_mul_of_norm_le (z : OC l)
    (hz : ‖(z : PadicComplex l)‖ ≤ ‖((l : ℕ) : PadicComplex l)‖) : ∃ c : OC l, z = (l : OC l) * c := by
  have hl : ((l : ℕ) : PadicComplex l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have h1 : ‖(z : PadicComplex l) / l‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ hz (norm_nonneg _)
  refine ⟨⟨(z : PadicComplex l) / l, ?_⟩, ?_⟩
  · rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict (PadicComplex.valued l).v] at h1
    refine (Valuation.mem_valuationSubring_iff _ _).2 ?_
    exact_mod_cast h1
  · apply Subtype.ext
    change (z : PadicComplex l) = ((l : OC l) : PadicComplex l) * ((z : PadicComplex l) / l)
    have : ((l : OC l) : PadicComplex l) = l := by simp
    rw [this]; field_simp

theorem eventually_sub_mem_one (y : Ainf l) :
    ∀ᶠ g in 𝓝 (1 : GQ l), AI.actW g y - y ∈ Ideal.span {((l : ℕ) : Ainf l), AI.ξ} := by
  obtain ⟨θ, -, hs, hact, hker, -⟩ := GlobalTheory.T.exists_fontaineTheta_on_Ainf l P AI
  have hc := GlobalTheory.Cyc.IsActC.continuous_orbit l AI.actC ⟨AI.actC_ext, AI.actC_norm⟩
    ((θ y : OC l) : PadicComplex l)
  have hl : (0 : ℝ) < ‖((l : ℕ) : PadicComplex l)‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have := (Metric.tendsto_nhds.1 (hc.tendsto 1)) _ hl
  filter_upwards [this] with g hg
  rw [dist_eq_norm, map_one, RingAut.one_apply, ← hact] at hg
  obtain ⟨c, hc⟩ := exists_eq_mul_of_norm_le (θ (AI.actW g y) - θ y) (by simpa using hg.le)
  obtain ⟨c', rfl⟩ := hs c
  obtain ⟨d, hd⟩ := (hker (AI.actW g y - y - l * c')).1 (by
    rw [map_sub, map_sub, hc, map_mul, map_natCast, sub_self])
  rw [Ideal.mem_span_pair]
  exact ⟨c', d, by linear_combination -hd⟩

theorem eventually_sub_mem_pow (N : ℕ) (y : Ainf l) :
    ∀ᶠ g in 𝓝 (1 : GQ l), AI.actW g y - y ∈ Ideal.span {((l : ℕ) : Ainf l), AI.ξ} ^ (N + 1) := by
  set I : Ideal (Ainf l) := Ideal.span {((l : ℕ) : Ainf l), AI.ξ} with hI
  have hlI : ((l : ℕ) : Ainf l) ∈ I := Ideal.subset_span (by simp)
  have ht : ∀ z : OCb l, ∀ᶠ g in 𝓝 (1 : GQ l),
      AI.actW g (WittVector.teichmuller l z) - WittVector.teichmuller l z ∈ I ^ (N + 1) := by
    intro z
    obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv (OCb l) l N).surjective z
    filter_upwards [eventually_sub_mem_one AI (WittVector.teichmuller l w)] with g hg
    have := SModEq.sub_mem.1 ((SModEq.sub_mem.2 hg).pow_pow_add_one hlI N)
    rw [iterateFrobeniusEquiv_def, map_pow, map_pow]
    exact this
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff y N
  have hall := (Filter.eventually_all_finset (Finset.Iic N)).2
    (fun i _ => ht ((((_root_.frobeniusEquiv (OCb l) l).symm ^ i) (y.coeff i))))
  filter_upwards [hall] with g hg
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, map_add, map_mul, map_pow, map_natCast, map_sum, add_sub_add_comm, ← mul_sub,
    ← Finset.sum_sub_distrib]
  refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlI _)) (sum_mem fun i hi => ?_)
  rw [map_mul, map_pow, map_natCast, ← sub_mul]
  exact Ideal.mul_mem_right _ _ (hg i hi)

theorem eventually_sub_mem (r n : ℕ) (y : Ainf l) :
    ∀ᶠ g in 𝓝 (1 : GQ l), AI.actW g y - y ∈ Ideal.span {((l : ℕ) : Ainf l) ^ r, AI.ξ ^ n} := by
  filter_upwards [eventually_sub_mem_pow AI (r + n) y] with g hg
  have h1 := Ideal.pow_le_pow_right (I := Ideal.span {((l : ℕ) : Ainf l), AI.ξ})
    (Nat.le_succ (r + n)) hg
  rw [Ideal.span_insert] at h1 ⊢
  rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
  exact Ideal.sup_pow_add_le_pow_sup_pow h1

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem xi_mul_cancel {a b : Ainf l} (h : AI.ξ * a = AI.ξ * b) : a = b := by
  apply inclW_injective
  have := congrArg (inclW l) h
  rw [map_mul, map_mul] at this
  exact AI.isUnit_inclW_ξ.mul_left_cancel this

theorem eventually_xi (r n : ℕ) :
    ∀ᶠ g in 𝓝 (1 : GQ l), ∃ u : (Ainf l)ˣ, AI.actW g AI.ξ = AI.ξ * u ∧
      (u : Ainf l) - 1 ∈ Ideal.span {((l : ℕ) : Ainf l) ^ r, AI.ξ ^ n} := by
  obtain ⟨θ, -, -, -, hker, -⟩ := GlobalTheory.T.exists_fontaineTheta_on_Ainf l P AI
  filter_upwards [eventually_sub_mem AI r (n + 1) AI.ξ] with g hg
  obtain ⟨b, hb⟩ := xi_dvd_act AI g AI.ξ ⟨1, (mul_one _).symm⟩
  obtain ⟨b', hb'⟩ := xi_dvd_act AI g⁻¹ AI.ξ ⟨1, (mul_one _).symm⟩
  have h1 : AI.ξ * 1 = AI.ξ * (b * AI.actWHom g b') := by
    have := congrArg (AI.actWHom g) hb'
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply, map_mul,
      hb] at this
    rw [← mul_assoc, mul_one]; exact this
  have h2 := (xi_mul_cancel AI h1).symm
  have hb2 : AI.actW g AI.ξ = AI.ξ * b := hb
  refine ⟨Units.mkOfMulEqOne _ _ h2, hb2, ?_⟩
  change b - 1 ∈ _
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨p, q, hpq⟩ := hg
  have hθξ : θ AI.ξ = 0 := (hker _).2 dvd_rfl
  have hp : θ p = 0 := by
    have := congrArg θ hpq
    rw [hb2] at this
    simp only [map_add, map_mul, map_pow, map_natCast, map_sub, hθξ, pow_succ, mul_zero, zero_mul,
      add_zero, sub_zero] at this
    have hl : ((l : ℕ) : OC l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ hl)
  obtain ⟨p', rfl⟩ := (hker _).1 hp
  refine ⟨p', q, xi_mul_cancel AI ?_⟩
  rw [hb2] at hpq
  linear_combination hpq

theorem units_zpow_sub_one_mem {R : Type} [CommRing R] (J : Ideal R) (u : Rˣ)
    (hu : (u : R) - 1 ∈ J) (a : ℤ) : ((u ^ a : Rˣ) : R) - 1 ∈ J := by
  have h1 : Units.map (Ideal.Quotient.mk J).toMonoidHom u = 1 := by
    ext
    exact Ideal.Quotient.eq.2 hu
  have h2 : Units.map (Ideal.Quotient.mk J).toMonoidHom (u ^ a) = 1 := by
    rw [map_zpow, h1, one_zpow]
  exact Ideal.Quotient.eq.1 (congrArg Units.val h2)

theorem eventually_actQab (a b : ℤ) (hab : a ≤ b) (r : ℕ) (x : Qab (AinfSub l) (xiU AI) a b) :
    ∀ᶠ g in 𝓝 (1 : GQ l), ∃ y, actQab (xiOK AI) a b g x - x = (l : ℤ_[l]) ^ r • y := by
  obtain ⟨n, rfl⟩ := Int.exists_add_of_le hab
  obtain ⟨⟨_, _, ⟨y, rfl⟩, rfl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  filter_upwards [eventually_sub_mem AI r n y, eventually_xi AI r n] with g hy ⟨u, hu, hu1⟩
  have hua := units_zpow_sub_one_mem _ u hu1 a
  have hm : ((u ^ a : (Ainf l)ˣ) : Ainf l) * AI.actW g y - y ∈
      Ideal.span {((l : ℕ) : Ainf l) ^ r, AI.ξ ^ n} := by
    have := add_mem (Ideal.mul_mem_right (AI.actW g y) _ hua) hy
    convert this using 1
    ring
  obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.1 hm
  refine ⟨Submodule.Quotient.mk ⟨_, _, ⟨p, rfl⟩, rfl⟩, ?_⟩
  rw [actQab, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq]
  refine ⟨_, ⟨q, rfl⟩, ?_⟩
  have hg : AI.actWCbHom g (xiU AI) = (Units.map (inclW l).toMonoidHom u : (WCb l)ˣ) * xiU AI := by
    change AI.actWCbHom g (inclW l AI.ξ) = inclW l u * inclW l AI.ξ
    rw [inclW_act, mul_comm, ← map_mul, ← hu]; rfl
  have hz := act_zpow (act := AI.actWCbHom) (ξ := xiU AI) g a _ hg
  change ((xiU AI ^ (a + n) : (WCb l)ˣ) : WCb l) * inclW l q =
    AI.actWCbHom g (((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l y) -
      ((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l y -
      (l : ℤ_[l]) ^ r • (((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l p)
  rw [map_mul, hz, inclW_act, mul_zpow, ← map_zpow, zpow_add, zpow_natCast, Units.val_mul,
    Units.val_mul, Units.val_pow_eq_pow_val, Algebra.smul_def, map_pow, map_natCast]
  have h3 := congrArg (inclW l) hpq
  simp only [map_add, map_mul, map_pow, map_natCast, map_sub] at h3
  have e1 : ((xiU AI : (WCb l)ˣ) : WCb l) = inclW l AI.ξ := rfl
  have e2 : ((Units.map (inclW l).toMonoidHom (u ^ a) : (WCb l)ˣ) : WCb l) =
    inclW l ((u ^ a : (Ainf l)ˣ) : Ainf l) := rfl
  have e3 : AI.actWHom g y = AI.actW g y := rfl
  rw [e1, e2, e3]
  linear_combination (((xiU AI ^ a : (WCb l)ˣ) : WCb l)) * h3

end Ainf

theorem isIntegral_of_norm_le_one (x : Om l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_of_norm_le_one (LL : FinExt l) (x : ↥LL.1) (h : ‖(x : Om l)‖ ≤ 1) : x ∈ OL LL :=
  (isIntegral_algHom_iff (LL.1.val.restrictScalars ℤ_[l]) LL.1.val.toRingHom.injective).1
    (isIntegral_of_norm_le_one _ h)

theorem lattice_mem_nhds {G Qp LL O : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    (T : LocLat G Qp LL O) (c : O) (hc : ∀ᶠ z in 𝓝 (0 : LL), ∃ o : O, z = algebraMap O LL (c * o)) :
    ∀ᶠ v in 𝓝 (0 : T.V), ∃ y ∈ T.L.T, v = c • y := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 T.L.fg
  have hsurj : Function.Surjective (Fintype.linearCombination LL s) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← T.L.span, ← hs,
      Submodule.span_span_of_tower]
  have hopen := (IsModuleTopology.isOpenQuotientMap_of_surjective hsurj).isOpenMap
  have hU : {z : Fin n → LL | ∀ i, ∃ o : O, z i = algebraMap O LL (c * o)} ∈ 𝓝 0 :=
    Filter.eventually_all.2 fun i => ((continuous_apply i).tendsto (0 : Fin n → LL)).eventually hc
  have h2 := hopen.image_mem_nhds hU
  rw [map_zero] at h2
  filter_upwards [h2] with v ⟨z, hz, hv⟩
  choose o ho using hz
  refine ⟨∑ i, o i • s i, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rw [← hs]; exact Submodule.subset_span ⟨i, rfl⟩
  · rw [← hv, Fintype.linearCombination_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ho, algebraMap_smul]

theorem eventually_actT {G Qp LL O : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    (T : LocLat G Qp LL O) (c : O) (hc : ∀ᶠ z in 𝓝 (0 : LL), ∃ o : O, z = algebraMap O LL (c * o))
    (t : ↥T.L.T) : ∀ᶠ g in 𝓝 (1 : G), ∃ y, actT T.L g t - t = c • y := by
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  have h : Tendsto (fun g => T.ρ g t - t) (𝓝 1) (𝓝 0) := by
    have h1 : Continuous (fun g => T.ρ g t - t) := (T.cont t).sub continuous_const
    simpa using h1.tendsto 1
  filter_upwards [h.eventually (lattice_mem_nhds T c hc)] with g ⟨y, hy, e⟩
  exact ⟨⟨y, hy⟩, Subtype.ext e⟩

theorem pow_mul_OL_mem_nhds (LL : FinExt l) (r : ℕ) :
    ∀ᶠ z in 𝓝 (0 : ↥LL.1), ∃ o : ↥(OL LL), z = algebraMap ↥(OL LL) ↥LL.1
      (algebraMap ℤ_[l] ↥(OL LL) ((l : ℤ_[l]) ^ r) * o) := by
  have hl : ((l : ℕ) : Om l) ^ r ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hl' : ((l : ℕ) : ↥LL.1) ^ r ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hc : Continuous fun z : ↥LL.1 => ‖(z : Om l)‖ := continuous_subtype_val.norm
  have hU : ∀ᶠ z : ↥LL.1 in 𝓝 0, ‖(z : Om l)‖ < ‖((l : ℕ) : Om l) ^ r‖ := by
    refine (isOpen_lt hc continuous_const).mem_nhds ?_
    have := norm_pos_iff.2 hl
    simpa using this
  filter_upwards [hU] with z hz
  have hm : z / (l : ↥LL.1) ^ r ∈ OL LL := mem_OL_of_norm_le_one LL _ (by
    have : ((z / (l : ↥LL.1) ^ r : ↥LL.1) : Om l) = (z : Om l) / (l : Om l) ^ r := by simp
    rw [this, norm_div]
    exact div_le_one_of_le₀ hz.le (norm_nonneg _))
  refine ⟨⟨_, hm⟩, ?_⟩
  rw [map_mul, map_pow, map_natCast, map_pow, map_natCast]
  change z = _ * (z / _)
  field_simp

theorem eventually_actTZ {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (r : ℕ) (t : ↥T.L.T) :
    letI := zlMod LL T
    ∀ᶠ g in 𝓝 (1 : G), ∃ y, actTZ LL T g t - t = (l : ℤ_[l]) ^ r • y := by
  haveI : IsTopologicalRing ↥LL.1 := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  exact eventually_actT T _ (pow_mul_OL_mem_nhds LL r) t

theorem continuous_orbit_of_eventually {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup M] [Module R M] (a : R) (ρ : Representation R G M) (x : M)
    (h : ∀ r : ℕ, ∀ᶠ g in 𝓝 (1 : G), ∃ y, ρ g x - x = a ^ r • y) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) fun g => ρ g x := by
  rw [GlobalTheory.continuous_adicModule_iff]
  intro g n
  have hc : Tendsto (fun k => g⁻¹ * k) (𝓝 g) (𝓝 1) := by
    have := (continuous_const_mul g⁻¹).tendsto g
    rwa [inv_mul_cancel] at this
  filter_upwards [hc.eventually (h n)] with k ⟨y, e⟩
  refine ⟨ρ g y, ?_⟩
  rw [← map_smul, ← e, map_sub, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem eventually_tensor {R G M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (c : R) (F : Filter G) (f : G → M →ₗ[R] M) (f' : G → N →ₗ[R] N)
    (h : ∀ x, ∀ᶠ g in F, ∃ y, f g x - x = c • y) (h' : ∀ x, ∀ᶠ g in F, ∃ y, f' g x - x = c • y)
    (x : TensorProduct R M N) :
    ∀ᶠ g in F, ∃ y, TensorProduct.map (f g) (f' g) x - x = c • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact .of_forall fun g => ⟨0, by simp⟩
  | tmul m n =>
    filter_upwards [h m, h' n] with g ⟨y, e⟩ ⟨y', e'⟩
    refine ⟨y ⊗ₜ f' g n + m ⊗ₜ y', ?_⟩
    rw [smul_add, TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, ← e, ← e',
      TensorProduct.map_tmul, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  | add x x' hx hx' =>
    filter_upwards [hx, hx'] with g ⟨y, e⟩ ⟨y', e'⟩
    exact ⟨y + y', by rw [map_add, smul_add, ← e, ← e']; abel⟩

theorem continuous_repQ {P : LocPrime l} (AI : LocAinf l P) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (a b : ℤ) (H : Subgroup (GQ l)) (hle : H ≤ GK K)
    (hab : a ≤ b) :
    letI := zlMod LL T
    letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU AI) a b)) :=
      (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
    ∀ x, Continuous fun g => (repQ AI H ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) g x := by
  letI := zlMod LL T
  intro x
  refine continuous_orbit_of_eventually (l : ℤ_[l]) _ x fun r => ?_
  have h1 : Tendsto (Subgroup.inclusion hle) (𝓝 1) (𝓝 1) := by
    have : Continuous (Subgroup.inclusion hle) := continuous_subtype_val.subtype_mk _
    simpa using this.tendsto 1
  have h2 : Tendsto (fun g : ↥H => (g : GQ l)) (𝓝 1) (𝓝 1) := continuous_subtype_val.tendsto 1
  exact eventually_tensor ((l : ℤ_[l]) ^ r) (𝓝 (1 : ↥H))
    (fun g => actTZ LL T (Subgroup.inclusion hle g)) (fun g => actQab (xiOK AI) a b (g : GQ l))
    (fun t => h1.eventually (eventually_actTZ LL T r t))
    (fun q => h2.eventually (eventually_actQab AI a b hab r q)) x

theorem continuous_orbit_tensor_Qab : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (a b : ℤ) (j : ℕ) (hle : Gj K j ≤ GK K), a ≤ b → letI := zlMod LL T; letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b)) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; ∀ x, Continuous fun g => (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) g x := by
  intro D HW F l _ K s LL h S E T a b j hle hab
  exact continuous_repQ (D.locA l) K LL T a b (Gj K j) hle hab

end GlobalTheory.AinfCont
