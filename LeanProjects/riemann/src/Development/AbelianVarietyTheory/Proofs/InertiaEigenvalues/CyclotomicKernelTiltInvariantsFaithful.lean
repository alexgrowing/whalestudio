import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormRootSubOneLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerTraceAlmostSurjective

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Cyc GlobalTheory.Cyc.TraceTilt

namespace GlobalTheory.TiltFaithful

def Reps {G : Type*} [Group G] (H U : Subgroup G) (S : Finset G) : Prop :=
  (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ U

theorem exists_reps' {G : Type*} [Group G] (H U W : Subgroup G) [W.FiniteIndex] (hW : H ⊓ W ≤ U) :
    ∃ S : Finset G, Reps H U S := by
  classical
  haveI : (U.subgroupOf H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := W.subgroupOf H) fun x hx => hW ⟨x.2, hx⟩
  letI : Fintype (H ⧸ U.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : H ⧸ U.subgroupOf H => (q.out : G)), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact q.out.2
  · intro h hh
    have key : ∀ q : H ⧸ U.subgroupOf H,
        (q.out : G)⁻¹ * h ∈ U ↔ q = ((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H) := by
      intro q
      conv_rhs => rw [← q.out_eq']
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
    refine ⟨(((⟨h, hh⟩ : H) : H ⧸ U.subgroupOf H).out : G),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩
    rintro s ⟨hs, hs'⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    rw [(key q).1 hs']

theorem reps_mul {G : Type*} [Group G] {H V U : Subgroup G} (hVH : V ≤ H) (hUV : U ≤ V)
    {S T : Finset G} (hS : Reps H V S) (hT : Reps V U T) :
    ∃ R : Finset G, Reps H U R ∧ ∀ {M : Type} [AddCommMonoid M] (f : G → M),
      ∑ r ∈ R, f r = ∑ s ∈ S, ∑ t ∈ T, f (s * t) := by
  classical
  have huniq : ∀ h ∈ H, ∃! p : G × G, p ∈ S ×ˢ T ∧ (p.1 * p.2)⁻¹ * h ∈ U := by
    intro h hh
    obtain ⟨s, ⟨hs, hsh⟩, hsu⟩ := hS.2 h hh
    obtain ⟨t, ⟨ht, hth⟩, htu⟩ := hT.2 _ hsh
    refine ⟨(s, t), ⟨Finset.mem_product.2 ⟨hs, ht⟩, ?_⟩, ?_⟩
    · rw [mul_inv_rev, mul_assoc]
      exact hth
    · rintro ⟨s', t'⟩ ⟨hm, hp⟩
      obtain ⟨hs', ht'⟩ := Finset.mem_product.1 hm
      rw [mul_inv_rev, mul_assoc] at hp
      have h1 : s' = s := hsu s' ⟨hs', by
        have := V.mul_mem (hT.1 t' ht') (hUV hp)
        rwa [mul_inv_cancel_left] at this⟩
      subst h1
      rw [htu t' ⟨ht', hp⟩]
  have hinj : Set.InjOn (fun p : G × G => p.1 * p.2) ↑(S ×ˢ T) := by
    intro p hp q hq he
    have hp' := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    refine (huniq (p.1 * p.2) (H.mul_mem (hS.1 _ hp'.1) (hVH (hT.1 _ hp'.2)))).unique
      ⟨hp, by simp⟩ ⟨hq, ?_⟩
    have he' : p.1 * p.2 = q.1 * q.2 := he
    rw [he']; simp
  refine ⟨(S ×ˢ T).image fun p => p.1 * p.2, ⟨?_, ?_⟩, fun f => ?_⟩
  · intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs
    have hp' := Finset.mem_product.1 hp
    exact H.mul_mem (hS.1 _ hp'.1) (hVH (hT.1 _ hp'.2))
  · intro h hh
    obtain ⟨p, ⟨hp, hph⟩, hpu⟩ := huniq h hh
    refine ⟨p.1 * p.2, ⟨Finset.mem_image_of_mem _ hp, hph⟩, ?_⟩
    rintro s ⟨hs, hsh⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hs
    rw [hpu q ⟨hq, hsh⟩]
  · rw [Finset.sum_image hinj, Finset.sum_product]

variable {l : ℕ} [Fact l.Prime]

theorem exists_tilt_near {P : LocPrime l} (AI : LocAinf l P) (N : Subgroup (GQ l))
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) (B : ℕ → OC l)
    (hB : ∀ j, ∀ n ∈ N, AI.actC n (B j) = B j)
    (hs : ∀ j, ‖(B (j + 1) : PadicComplex l) ^ l - B j‖ ≤ r) :
    ∃ (x : OCb l) (y : OC l), (∀ n ∈ N, AI.actT n x = x) ∧
      PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y ∧
      ‖(B 0 : PadicComplex l) - y‖ ≤ r := by
  have hp : l.Prime := Fact.out
  have hl : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := (l : ℝ)⁻¹) (by positivity) hr
  have hk' : r ^ l ^ k ≤ (l : ℝ)⁻¹ :=
    (pow_le_pow_of_le_one hr0 hr.le (Nat.lt_pow_self hp.one_lt).le).trans hk.le
  have hB1 : ∀ j, ‖(B j : PadicComplex l)‖ ≤ 1 := fun j => (mem_OC _).1 (B j).2
  have hcomp : ∀ n, (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (B (n + 1 + k) ^ l ^ k) :
      ModP (OC l) l) ^ l = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (B (n + k) ^ l ^ k) := by
    intro n
    have h0 : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})
        ((B (n + k + 1) ^ l - B (n + k)) ^ l ^ k) = 0 := by
      rw [mk_eq_zero_iff]
      push_cast
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hs _) _).trans hk'
    have h2 := sub_pow_char_pow (R := ModP (OC l) l) (p := l) (n := k)
      (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (B (n + k + 1) ^ l))
      (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (B (n + k)))
    rw [map_pow, map_sub] at h0
    have h3 := sub_eq_zero.mp (h2.symm.trans h0)
    rw [show n + 1 + k = n + k + 1 by omega, ← map_pow, ← pow_mul, mul_comm, pow_mul, map_pow,
      map_pow _ (B (n + k))]
    exact h3
  let x : OCb l := ⟨fun n => Ideal.Quotient.mk _ (B (n + k) ^ l ^ k), hcomp⟩
  have hx : ∀ n, PreTilt.coeff n x = Ideal.Quotient.mk _ (B (n + k) ^ l ^ k) := fun n => rfl
  have h4 : ∀ j, ‖(B 0 : PadicComplex l) - (B j : PadicComplex l) ^ l ^ j‖ ≤ r := by
    intro j
    induction j with
    | zero => simpa using hr0
    | succ j ih =>
      rw [← sub_add_sub_cancel _ ((B j : PadicComplex l) ^ l ^ j)]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
      rw [pow_succ', pow_mul, norm_sub_rev]
      refine (norm_pow_sub_pow_le ?_ (hB1 j) _).trans (hs j)
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hB1 _)
  refine ⟨x, _, fun g hg => Perfection.ext fun n => ?_, hx 0, ?_⟩
  · change PreTilt.coeff n (AI.actT g x) = PreTilt.coeff n x
    obtain ⟨y', hy', hy⟩ := AI.actT_coeff g x n _ (hx n)
    rw [hy, hx]
    congr 1
    apply Subtype.ext
    rw [hy']
    push_cast
    rw [map_pow, hB _ g hg]
  · rw [zero_add]
    exact h4 k

theorem near_of_tilt {P : LocPrime l} (AI : LocAinf l P) (T : Finset (GQ l)) (d : GQ l) (x : OCb l)
    (y : OC l) (hy : PreTilt.coeff 0 x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y)
    (b : Om l) (r : ℝ) (hr : (l : ℝ)⁻¹ ≤ r) (hb : ‖(b : PadicComplex l) - y‖ ≤ r)
    (hd : AI.actT d (∑ t ∈ T, AI.actT t x) = ∑ t ∈ T, AI.actT t x) :
    ‖d (∑ t ∈ T, t b) - ∑ t ∈ T, t b‖ ≤ r := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hb
  choose z hz hz' using fun s => AI.actT_coeff s x 0 y hy
  have hd' : ∑ t ∈ T, AI.actT (d * t) x = ∑ t ∈ T, AI.actT t x := by
    rw [← hd, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul AI.actT, RingAut.mul_apply]
  have h1 := congrArg (PreTilt.coeff 0) hd'
  rw [map_sum, map_sum, Finset.sum_congr rfl fun s _ => hz' (d * s),
    Finset.sum_congr rfl fun s _ => hz' s] at h1
  have h2 : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})
      (∑ s ∈ T, (z (d * s) - z s)) = 0 := by
    rw [Finset.sum_sub_distrib, map_sub, map_sum, map_sum]
    exact sub_eq_zero.2 h1
  rw [mk_eq_zero_iff] at h2
  have h3 : ((∑ s ∈ T, (z (d * s) - z s) : OC l) : PadicComplex l) =
      ∑ s ∈ T, (AI.actC (d * s) y - AI.actC s y) := by
    rw [show ((∑ s ∈ T, (z (d * s) - z s) : OC l) : PadicComplex l) =
      ∑ s ∈ T, ((z (d * s) - z s : OC l) : PadicComplex l) from
      map_sum (PadicComplexInt l).subtype _ _]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← hz, ← hz]
    rfl
  have h5 : ((d (∑ t ∈ T, t b) - ∑ t ∈ T, t b : Om l) : PadicComplex l) =
      ∑ s ∈ T, (AI.actC (d * s) ((b : PadicComplex l) - y) - AI.actC s ((b : PadicComplex l) - y)) +
        ∑ s ∈ T, (AI.actC (d * s) y - AI.actC s y) := by
    rw [← Finset.sum_add_distrib, map_sum, ← Finset.sum_sub_distrib, PadicComplex.coe_eq, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_sub, map_sub, map_sub, AI.actC_ext, AI.actC_ext, PadicComplex.coe_eq,
      PadicComplex.coe_eq, AlgEquiv.mul_apply]
    ring
  rw [← PadicComplex.norm_extends l, h5]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ((h3 ▸ h2).trans hr))
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr0 fun s _ => ?_
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [AI.actC_norm]; exact hb
  · rw [norm_neg, AI.actC_norm]; exact hb

theorem fixed_of_near (hn : ∀ (g : GQ l) (x : Om l), ‖g x‖ = ‖x‖) (D A : Subgroup (GQ l))
    (hAD : A ≤ D) (S : Finset (GQ l)) (hS : Reps D A S) (a u : Om l) (ha0 : a ≠ 0) (ha1 : ‖a‖ < 1)
    (haD : ∀ d ∈ D, d a = a) (hu1 : ‖u‖ ≤ 1) (hu : ‖a‖ ≤ ‖∑ s ∈ S, s u‖)
    (hnear : ∀ y : Om l, ‖y‖ ≤ 1 → (∀ n ∈ A, n y = y) → ∀ d ∈ D,
      ‖d (u * y) - u * y‖ ≤ ‖a‖ ^ 3)
    (y : Om l) (hy : ∀ n ∈ A, n y = y) (g : GQ l) (hg : g ∈ D) : g y = y := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hdu : ∀ d ∈ D, ‖d u - u‖ ≤ ‖a‖ ^ 3 := fun d hd => by
    simpa using hnear 1 (by simp) (by simp) d hd
  set m : Om l := (S.card : Om l) with hm
  have hsplit : ∀ w : Om l, ∑ s ∈ S, s w = m * w + ∑ s ∈ S, (s w - w) := fun w => by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  have h3 : ‖a‖ ^ 3 < ‖a‖ := pow_lt_self_of_lt_one₀ hapos ha1 (by norm_num)
  have hmu : ‖a‖ ≤ ‖m‖ * ‖u‖ := by
    rw [hsplit] at hu
    have h1 := hu.trans (IsUltrametricDist.norm_add_le_max _ _)
    have h2 : ‖∑ s ∈ S, (s u - u)‖ ≤ ‖a‖ ^ 3 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
        fun s hs => hdu s (hS.1 s hs)
    rcases le_max_iff.1 h1 with h | h
    · rwa [norm_mul] at h
    · linarith
  have hm1 : ‖m‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  have ham : ‖a‖ ≤ ‖m‖ := hmu.trans (mul_le_of_le_one_right (norm_nonneg _) hu1)
  have hau : ‖a‖ ≤ ‖u‖ := hmu.trans (mul_le_of_le_one_left (norm_nonneg _) hm1)
  have hmove : ∀ w : Om l, ‖w‖ ≤ 1 → (∀ n ∈ A, n w = w) → ∀ d ∈ D, ‖d w - w‖ ≤ ‖a‖ ^ 2 := by
    intro w hw1 hw d hd
    have e : u * (d w - w) = (d (u * w) - u * w) + -((d u - u) * d w) := by
      rw [map_mul]; ring
    have h1 : ‖u * (d w - w)‖ ≤ ‖a‖ ^ 3 := by
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hnear w hw1 hw d hd) ?_)
      rw [norm_neg, norm_mul, hn]
      exact (mul_le_of_le_one_right (norm_nonneg _) hw1).trans (hdu d hd)
    rw [norm_mul] at h1
    have h2 := (mul_le_mul_of_nonneg_right hau (norm_nonneg (d w - w))).trans h1
    rw [pow_succ'] at h2
    exact le_of_mul_le_mul_left h2 hapos
  have hsmall : ∀ w : Om l, ‖w‖ ≤ 1 → (∀ n ∈ A, n w = w) → ∑ s ∈ S, s w = 0 → ‖w‖ ≤ ‖a‖ := by
    intro w hw1 hw h0
    rw [hsplit, add_eq_zero_iff_eq_neg] at h0
    have h1 : ‖m * w‖ ≤ ‖a‖ ^ 2 := by
      rw [h0, norm_neg]
      exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
        fun s hs => hmove w hw1 hw s (hS.1 s hs)
    rw [norm_mul] at h1
    have h2 := (mul_le_mul_of_nonneg_right ham (norm_nonneg w)).trans h1
    rw [pow_two] at h2
    exact le_of_mul_le_mul_left h2 hapos
  have hzero : ∀ w : Om l, (∀ n ∈ A, n w = w) → ∑ s ∈ S, s w = 0 → w = 0 := by
    intro w hw h0
    by_contra hw0
    obtain ⟨k, hk1, hk2⟩ := exists_mem_Ioc_zpow (norm_pos_iff.2 hw0) ((one_lt_inv₀ hapos).2 ha1)
    have hpos : 0 < ‖a‖ ^ (k + 1) := zpow_pos hapos _
    have h1 := hsmall (a ^ (k + 1) * w) (by
      rw [norm_mul, norm_zpow]
      refine (mul_le_mul_of_nonneg_left hk2 hpos.le).trans ?_
      rw [inv_zpow, mul_inv_cancel₀ hpos.ne'])
      (fun n hnA => by rw [map_mul, map_zpow₀, haD n (hAD hnA), hw n hnA]) (by
        rw [← mul_zero (a ^ (k + 1)), ← h0, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [map_mul, map_zpow₀, haD s (hS.1 s hs)])
    rw [norm_mul, norm_zpow] at h1
    have h2 := mul_lt_mul_of_pos_left hk1 hpos
    rw [inv_zpow, zpow_add_one₀ hapos.ne', mul_comm _ ‖a‖, mul_assoc,
      mul_inv_cancel₀ (zpow_pos hapos k).ne', mul_one, mul_comm ‖a‖, ← zpow_add_one₀ hapos.ne'] at h2
    linarith
  have htr : ∀ d ∈ D, d (∑ s ∈ S, s y) = ∑ s ∈ S, s y := fun d hd => by
    rw [map_sum]
    refine sum_shift D A S hS.1 hS.2 (fun g => g y) ?_ d hd
    intro g v _ hv
    change g (v y) = g y
    rw [hy v hv]
  have h0 := hzero (m * y - ∑ s ∈ S, s y)
    (fun n hnA => by rw [map_sub, map_mul, hm, map_natCast, hy n hnA, htr n (hAD hnA)]) (by
      rw [Finset.sum_congr rfl fun s hs => show s (m * y - ∑ s ∈ S, s y) =
        m * s y - ∑ s ∈ S, s y by rw [map_sub, map_mul, hm, map_natCast, htr s (hS.1 s hs)],
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, sub_self])
  have h1 := htr g hg
  rw [← sub_eq_zero.1 h0, map_mul, hm, map_natCast] at h1
  exact mul_left_cancel₀ (norm_pos_iff.1 (hapos.trans_le ham)) h1

theorem faithH : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI := by
  intro l _ P AI L g hg hfix
  have hp : l.Prime := Fact.out
  have hl : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hn : ∀ (g : GQ l) (x : Om l), ‖g x‖ = ‖x‖ := fun g x => by
    rw [← PadicComplex.norm_extends l, ← AI.actC_ext, AI.actC_norm, PadicComplex.norm_extends]
  let K : FinExt l := ⟨⊥, inferInstance⟩
  have hH : ∀ h : GQ l, h ∈ Hinf K ↔ P.χQ h = 1 := fun h =>
    ((cyc_basic l P.χQ P.χQ_cyc).2.2 K h (by
      have : K0 K = ⊥ := bot_inf_eq _
      rw [this, IntermediateField.fixingSubgroup_bot]; trivial)).2
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let E : IntermediateField ℚ_[l] (Om l) := IntermediateField.normalClosure ℚ_[l] L.1 (Om l)
  have hLE : L.1 ≤ E := IntermediateField.le_normalClosure _
  haveI : FiniteDimensional ℚ_[l] E := inferInstance
  haveI : Normal ℚ_[l] E := inferInstance
  haveI : E.fixingSubgroup.FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen E.fixingSubgroup E.fixingSubgroup_isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  have hsup : (Kinf K ⊔ E).fixingSubgroup = Hinf K ⊓ E.fixingSubgroup :=
    IntermediateField.fixingSubgroup_sup
  have hst : ∀ h ∈ Hinf K, ∀ x ∈ Kinf K ⊔ E, h x ∈ Kinf K ⊔ E := by
    intro h hh
    have : Kinf K ⊔ E ≤ (Kinf K ⊔ E).comap (h : Om l →ₐ[ℚ_[l]] Om l) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · change h x ∈ Kinf K ⊔ E
        rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx]
        exact (le_sup_left : Kinf K ≤ Kinf K ⊔ E) hx
      · change h x ∈ Kinf K ⊔ E
        have h1 := AlgEquiv.restrictNormal_commutes h E ⟨x, hx⟩
        have h2 : h x ∈ E := by
          have : h x = (h.restrictNormal E ⟨x, hx⟩ : E) := h1.symm
          rw [this]; exact Subtype.property _
        exact (le_sup_right : E ≤ Kinf K ⊔ E) h2
    exact fun x hx => this hx
  set N := (Kinf K ⊔ E).fixingSubgroup with hN
  let A : Subgroup (GQ l) := Hinf K ⊓ GK L
  let D : Subgroup (GQ l) :=
    { carrier := {d | d ∈ Hinf K ∧ ∀ x : OCb l, (∀ h ∈ A, AI.actT h x = x) → AI.actT d x = x}
      one_mem' := ⟨one_mem _, fun x _ => by rw [map_one]; rfl⟩
      mul_mem' := fun {c d} hc hd => ⟨mul_mem hc.1 hd.1, fun x hx => by
        rw [map_mul AI.actT, RingAut.mul_apply, hd.2 x hx, hc.2 x hx]⟩
      inv_mem' := fun {c} hc => ⟨inv_mem hc.1, fun x hx => by
        conv_lhs => rw [← hc.2 x hx]
        rw [← RingAut.mul_apply, ← map_mul AI.actT, inv_mul_cancel, map_one]; rfl⟩ }
  have hDH : D ≤ Hinf K := fun d hd => hd.1
  have hAD : A ≤ D := fun d hd => ⟨hd.1, fun x hx => hx d hd⟩
  have hNA : N ≤ A := by
    rw [hsup]
    exact inf_le_inf_left _ (IntermediateField.fixingSubgroup_le hLE)
  have hgD : g ∈ D := ⟨(hH g).2 hg, fun x hx => hfix x fun h h1 h2 => hx h ⟨(hH h).2 h2, h1⟩⟩
  obtain ⟨S₁, hS₁⟩ := exists_reps' (Hinf K) D E.fixingSubgroup (hsup ▸ hNA.trans hAD)
  obtain ⟨S₂, hS₂⟩ := exists_reps' D A E.fixingSubgroup
    ((inf_le_inf_right _ hDH).trans (hsup ▸ hNA))
  obtain ⟨T, hT⟩ := exists_reps' A N E.fixingSubgroup
    ((inf_le_inf_right _ (hAD.trans hDH)).trans hsup.ge)
  obtain ⟨R₂, hR₂, hs₂⟩ := reps_mul hAD hNA hS₂ hT
  obtain ⟨R, hR, hs⟩ := reps_mul hDH (hNA.trans hAD) hS₁ hR₂
  obtain ⟨r, hr0, hr1, hroot⟩ := approx_root hn K (Kinf K ⊔ E) R le_sup_left hst hR.1 hR.2
  have hr' : max r (l : ℝ)⁻¹ < 1 := max_lt hr1 (inv_lt_one_of_one_lt₀ hl)
  have hr'0 : 0 ≤ max r (l : ℝ)⁻¹ := le_max_of_le_left hr0
  obtain ⟨a, ha, hra, ha1⟩ := exists_near_one K ((max r (l : ℝ)⁻¹) ^ ((3 : ℕ)⁻¹ : ℝ))
    (Real.rpow_nonneg hr'0 _) (Real.rpow_lt_one hr'0 hr' (by norm_num))
  have hra3 : max r (l : ℝ)⁻¹ ≤ ‖a‖ ^ 3 := by
    rw [← Real.rpow_inv_natCast_pow hr'0 (n := 3) (by norm_num)]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hr'0 _) hra.le 3
  have ha0 : a ≠ 0 := norm_pos_iff.1 ((Real.rpow_nonneg hr'0 _).trans_lt hra)
  obtain ⟨e, heM, he1, he⟩ :=
    trace_almost_onto l K (Kinf K ⊔ E) R le_sup_left hst hR.1 hR.2 a ha ha1
  have heN : ∀ n ∈ N, n e = e := fun n hnN =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hnN e heM
  have key : ∀ b : Om l, ‖b‖ ≤ 1 → (∀ n ∈ N, n b = b) → ∀ d ∈ D,
      ‖d (∑ t ∈ T, t b) - ∑ t ∈ T, t b‖ ≤ ‖a‖ ^ 3 := by
    intro b0 hb01 hb0 d hd
    let X := {c : Om l // ‖c‖ ≤ 1 ∧ ∀ n ∈ N, n c = c}
    have hstep : ∀ b : X, ∃ c : X, ‖c.1 ^ l - b.1‖ ≤ r := fun b => by
      obtain ⟨c, hc, hc'⟩ := hroot b.1 b.2.1 b.2.2
      exact ⟨⟨c, hc⟩, hc'⟩
    choose f hf using hstep
    let b : ℕ → X := fun j => f^[j] ⟨b0, hb01, hb0⟩
    obtain ⟨x, y, hxN, hxy, hy⟩ := exists_tilt_near AI N r hr0 hr1
      (fun j => ⟨((b j).1 : PadicComplex l), (mem_OC _).2 (by
        rw [PadicComplex.norm_extends]; exact (b j).2.1)⟩)
      (fun j n hnL => by
        change AI.actC n ((b j).1 : PadicComplex l) = ((b j).1 : PadicComplex l)
        rw [AI.actC_ext, (b j).2.2 n hnL])
      (fun j => by
        change ‖((b (j + 1)).1 : PadicComplex l) ^ l - ((b j).1 : PadicComplex l)‖ ≤ r
        have h1 := hf (b j)
        rw [← PadicComplex.norm_extends l, PadicComplex.coe_eq, map_sub, map_pow] at h1
        have h2 : b (j + 1) = f (b j) := Function.iterate_succ_apply' f j _
        rw [h2]
        exact h1)
    refine near_of_tilt AI T d x y hxy b0 _ ((le_max_right _ _).trans hra3)
      (le_trans hy ((le_max_left _ _).trans hra3)) (hd.2 _ fun h hh => ?_)
    rw [map_sum]
    have := sum_shift A N T hT.1 hT.2 (fun g => AI.actT g x)
      (fun g v _ hv => by rw [map_mul AI.actT, RingAut.mul_apply, hxN v hv]) h hh
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul AI.actT, RingAut.mul_apply]
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_
  refine fixed_of_near hn D A hAD S₂ hS₂ a (∑ t ∈ T, t e) ha0 ha1
    (fun d hd => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hDH hd) a ha) ?_ ?_ ?_ y
    (fun n hnA => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hnA.2 y hy) g hgD
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun t _ => by
      rw [hn]; exact he1
  · rw [← he, hs (fun r => r e)]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun s _ => ?_
    rw [← hn s (∑ s ∈ S₂, s (∑ t ∈ T, t e))]
    apply le_of_eq
    congr 1
    rw [hs₂ (fun r => (s * r) e), map_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [map_sum, map_sum]
    rfl
  · intro w hw1 hw d hd
    have h1 := key (e * w) (by
      rw [norm_mul]; exact mul_le_one₀ he1 (norm_nonneg _) hw1)
      (fun n hnN => by rw [map_mul, heN n hnN, hw n (hNA hnN)]) d hd
    have h2 : ∑ t ∈ T, t (e * w) = (∑ t ∈ T, t e) * w := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun t ht => by rw [map_mul, hw t (hT.1 t ht)]
    rwa [h2] at h1

end GlobalTheory.TiltFaithful
