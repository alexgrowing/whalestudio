import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso
import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EpEqOneIff

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MeasureTheory
open scoped Pointwise ENNReal Function

variable {D : D7} {N N' : ℕ}

def unionFd (M La : AddSubgroup (VC D N N')) (s : Set (VC D N N')) : Set (VC D N N') :=
  ⋃ q : La ⧸ M.addSubgroupOf La, (Quotient.out q : La) +ᵥ s

theorem out_mem (M La : AddSubgroup (VC D N N')) (g : La) :
    (((g + Quotient.out (QuotientAddGroup.mk (-g) : La ⧸ M.addSubgroupOf La) : La)) : VC D N N') ∈ M := by
  have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk (-g) : La ⧸ M.addSubgroupOf La)
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
  have h2 := M.neg_mem h
  convert h2 using 1
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_rev, neg_neg]

theorem out_inj (M La : AddSubgroup (VC D N N')) {q q' : La ⧸ M.addSubgroupOf La}
    (h : (Quotient.out q : La) = Quotient.out q') : q = q' := by
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', h]

theorem mem_vadd_iff {La : AddSubgroup (VC D N N')} (g : La) (s : Set (VC D N N')) (x : VC D N N') :
    x ∈ g +ᵥ s ↔ x - (g : VC D N N') ∈ s := by
  rw [Set.mem_vadd_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [AddSubgroup.vadd_def, vadd_eq_add, add_sub_cancel_left]; exact hy
  · intro h
    exact ⟨_, h, by rw [AddSubgroup.vadd_def, vadd_eq_add, add_sub_cancel]⟩

theorem unionFd_fd {M La : AddSubgroup (VC D N N')} (hle : M ≤ La)
    [Finite (La ⧸ M.addSubgroupOf La)] {s : Set (VC D N N')}
    (hs : IsAddFundamentalDomain La s volume) :
    IsAddFundamentalDomain M (unionFd M La s) volume where
  nullMeasurableSet := NullMeasurableSet.iUnion fun q => hs.nullMeasurableSet_vadd _
  ae_covers := by
    filter_upwards [hs.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    refine ⟨⟨_, out_mem M La g⟩, Set.mem_iUnion.2 ⟨QuotientAddGroup.mk (-g), ?_⟩⟩
    rw [mem_vadd_iff]
    convert hg using 1
    simp only [AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_add]
    abel
  aedisjoint := by
    intro a b hab
    change volume ((a +ᵥ unionFd M La s) ∩ (b +ᵥ unionFd M La s)) = 0
    let a' : La := ⟨a, hle a.2⟩
    let b' : La := ⟨b, hle b.2⟩
    have hsub : (a +ᵥ unionFd M La s) ∩ (b +ᵥ unionFd M La s) ⊆
        ⋃ q : La ⧸ M.addSubgroupOf La, ⋃ q' : La ⧸ M.addSubgroupOf La,
          ((a' + Quotient.out q) +ᵥ s) ∩ ((b' + Quotient.out q') +ᵥ s) := by
      rintro x ⟨hxa, hxb⟩
      obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.1 hxa
      obtain ⟨u', hu', hu'e⟩ := Set.mem_vadd_set.1 hxb
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hu
      obtain ⟨q', hq'⟩ := Set.mem_iUnion.1 hu'
      refine Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨q', ⟨?_, ?_⟩⟩⟩
      · rw [mem_vadd_iff] at hq ⊢
        convert hq using 1
        simp only [a', AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_add]
        abel
      · rw [mem_vadd_iff] at hq' ⊢
        convert hq' using 1
        rw [← hu'e]
        simp only [b', AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_add]
        abel
    refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun q' => ?_)
    by_cases he : a' + Quotient.out q = b' + Quotient.out q'
    · exfalso
      have h2 := congrArg (fun z : La => (z : VC D N N')) he
      simp only [a', b', AddSubgroup.coe_add] at h2
      have hqq : q = q' := by
        rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf]
        have : ((-Quotient.out q + Quotient.out q' : La) : VC D N N') = (a : VC D N N') - b := by
          simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
          rw [eq_sub_iff_add_eq]
          rw [← sub_eq_zero] at h2 ⊢
          rw [← neg_eq_zero, ← h2]
          abel
        rw [this]
        exact M.sub_mem a.2 b.2
      subst hqq
      apply hab
      simp only [add_left_inj] at h2
      exact Subtype.ext h2
    · exact hs.aedisjoint he

theorem pieces_disj {M La : AddSubgroup (VC D N N')} {s : Set (VC D N N')}
    (hs : IsAddFundamentalDomain La s volume) :
    Pairwise (AEDisjoint volume on fun q : La ⧸ M.addSubgroupOf La => (Quotient.out q : La) +ᵥ s) := by
  intro q q' hqq
  exact hs.aedisjoint fun h => hqq (out_inj M La h)

theorem lint_unionFd {M La : AddSubgroup (VC D N N')} [Countable La]
    [Fintype (La ⧸ M.addSubgroupOf La)]
    {s : Set (VC D N N')} (hs : IsAddFundamentalDomain La s volume) (f : VC D N N' → ℝ≥0∞)
    (hf : ∀ g : La, ∀ x, f (g +ᵥ x) = f x) :
    ∫⁻ x in unionFd M La s, f x =
      (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ≥0∞) * ∫⁻ x in s, f x := by
  unfold unionFd
  rw [lintegral_iUnion₀ (fun q => hs.nullMeasurableSet_vadd _) (pieces_disj hs), tsum_fintype]
  have : ∀ q : La ⧸ M.addSubgroupOf La, ∫⁻ x in (Quotient.out q : La) +ᵥ s, f x = ∫⁻ x in s, f x :=
    fun q => (hs.vadd _).setLIntegral_eq hs f hf
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem vol_unionFd {M La : AddSubgroup (VC D N N')} [Countable La]
    [Fintype (La ⧸ M.addSubgroupOf La)]
    {s : Set (VC D N N')} (hs : IsAddFundamentalDomain La s volume) :
    volume (unionFd M La s) = (Fintype.card (La ⧸ M.addSubgroupOf La) : ℝ≥0∞) * volume s := by
  unfold unionFd
  rw [measure_iUnion₀ (pieces_disj hs) (fun q => hs.nullMeasurableSet_vadd _), tsum_fintype]
  have : ∀ q : La ⧸ M.addSubgroupOf La, volume ((Quotient.out q : La) +ᵥ s) = volume s :=
    fun q => (hs.vadd _).measure_eq hs
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem avg_sub {M La : AddSubgroup (VC D N N')} [Countable La] [Countable M] (hle : M ≤ La)
    [Finite (La ⧸ M.addSubgroupOf La)] {s t : Set (VC D N N')}
    (hs : IsAddFundamentalDomain La s volume) (ht : IsAddFundamentalDomain M t volume)
    (f : VC D N N' → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (hper : ∀ g ∈ La, ∀ x, f (x + g) = f x) :
    ⨍ x in t, f x = ⨍ x in s, f x := by
  haveI := Fintype.ofFinite (La ⧸ M.addSubgroupOf La)
  set k := Fintype.card (La ⧸ M.addSubgroupOf La)
  have hk : k ≠ 0 := Fintype.card_ne_zero
  have ht' := unionFd_fd hle hs
  have hperL : ∀ g : La, ∀ x, ENNReal.ofReal (f (g +ᵥ x)) = ENNReal.ofReal (f x) := by
    intro g x; rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm, hper g g.2]
  have hperM : ∀ g : M, ∀ x, ENNReal.ofReal (f (g +ᵥ x)) = ENNReal.ofReal (f x) := by
    intro g x; rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm, hper g (hle g.2)]
  have hint : ∀ u : Set (VC D N N'), ∫ x in u, f x = (∫⁻ x in u, ENNReal.ofReal (f x)).toReal := by
    intro u
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
      hfc.aestronglyMeasurable
  have hL : ∫⁻ x in t, ENNReal.ofReal (f x) = (k : ℝ≥0∞) * ∫⁻ x in s, ENNReal.ofReal (f x) := by
    rw [ht.setLIntegral_eq ht' _ hperM, lint_unionFd hs _ hperL]
  have hV : volume t = (k : ℝ≥0∞) * volume s := by
    rw [ht.measure_eq ht', vol_unionFd hs]
  rw [setAverage_eq, setAverage_eq, hint, hint, hL, Measure.real, Measure.real, hV,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, smul_eq_mul, smul_eq_mul]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [mul_inv]
  field_simp

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MeasureTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO
open scoped Pointwise ENNReal Function

variable {D : D7} {N N' : ℕ}

def crD (T : Tor D) (A B : VC D N N' → ℂ) (z : VC D N N') : ℂ :=
  A z * starRingEnd ℂ (B z) * (Real.exp (-Real.pi * (Hf D T z z).re) : ℂ)

theorem re_Hf_add' (T : Tor D) (z x : VC D N N') :
    (Hf D T (z + x) (z + x)).re =
      (Hf D T z z).re + 2 * (Hf D T z x).re + (Hf D T x x).re := by
  rw [Hf_add_left, Hf_add_right, Hf_add_right, Complex.add_re, Complex.add_re, Complex.add_re,
    Hf_re_swap T z x]
  ring

theorem exp_mul_conj (w : ℂ) :
    Complex.exp w * starRingEnd ℂ (Complex.exp w) = ((Real.exp (2 * w.re) : ℝ) : ℂ) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, Complex.add_conj, Complex.ofReal_exp]

theorem crD_U (T : Tor D) (A B : VC D N N' → ℂ) (y z : VC D N N') :
    crD T (U D T y A) (U D T y B) z = crD T A B (z + y) := by
  simp only [crD, U, map_mul]
  set w : ℂ := -(Real.pi : ℂ) * Hf D T z y - (Real.pi : ℂ) * Hf D T y y / 2
  have h1 := exp_mul_conj w
  have hw : w.re = -Real.pi * (Hf D T z y).re - Real.pi * (Hf D T y y).re / 2 := by
    simp only [w, Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, Complex.div_re, Complex.normSq_ofNat]
    norm_num
    ring
  have h2 : ((Real.exp (2 * w.re) : ℝ) : ℂ) * (Real.exp (-Real.pi * (Hf D T z z).re) : ℂ) =
      (Real.exp (-Real.pi * (Hf D T (z + y) (z + y)).re) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, re_Hf_add', hw]
    congr 2
    ring
  rw [← h2, ← h1]
  ring

theorem crD_smul (T : Tor D) (c c' : ℂ) (A B : VC D N N' → ℂ) (z : VC D N N') :
    crD T (fun w => c * A w) (fun w => c' * B w) z = c * starRingEnd ℂ c' * crD T A B z := by
  simp only [crD, map_mul]; ring

def ep (T : Tor D) (x y : VC D N N') : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))

theorem Hf_im_swap (T : Tor D) (x y : VC D N N') : (Hf D T y x).im = -(Hf D T x y).im := by
  rw [Hf_herm T x y, Complex.conj_im]

theorem cf_swap (T : Tor D) (x y : VC D N N') : cf T y x = ep T x y * cf T x y := by
  simp only [cf, ep, ← Complex.exp_add, Hf_im_swap T x y]
  congr 1
  push_cast
  ring

theorem aU_eig (T : Tor D) {La₁ : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La₁) {y : VC D N N'} (hy : y ∈ La₁) (x z : VC D N N') :
    al D T y * U D T y (U D T x G) z = ep T x y * U D T x G z := by
  have h1 := U_U T y x G z
  have h2 : U D T x G z = al D T y * cf T x y * U D T (x + y) G z := by
    conv_lhs => rw [← fix_eq T hG hy]
    rw [U_smul, U_U]; ring
  rw [h1, h2, add_comm y x, cf_swap]
  ring

def trm (T : Tor D) (G : VC D N N' → ℂ) (x : VC D N N') : VC D N N' → ℂ :=
  fun z => al D T x * U D T x G z

theorem al_mul_conj (T : Tor D) (y : VC D N N') : al D T y * starRingEnd ℂ (al D T y) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.norm_al]
  simp

theorem crD_shift (T : Tor D) {La₁ : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La₁) {y : VC D N N'} (hy : y ∈ La₁) (x x' z : VC D N N') :
    crD T (trm T G x) (trm T G x') (z + y) =
      ep T x y * starRingEnd ℂ (ep T x' y) * crD T (trm T G x) (trm T G x') z := by
  rw [← crD_U]
  have hx : ∀ u : VC D N N', (fun w => al D T y * U D T y (trm T G u) w) =
      fun w => ep T u y * trm T G u w := by
    intro u; funext w
    show al D T y * U D T y (fun z => al D T u * U D T u G z) w = ep T u y * (al D T u * U D T u G w)
    rw [U_smul, ← mul_assoc, mul_comm (al D T y), mul_assoc, aU_eig T hG hy]
    ring
  have h := crD_smul T (al D T y) (al D T y) (U D T y (trm T G x)) (U D T y (trm T G x')) z
  rw [hx x, hx x', al_mul_conj, one_mul, crD_smul] at h
  exact h.symm

theorem ep_mul_conj (T : Tor D) (x x' y : VC D N N') :
    ep T x y * starRingEnd ℂ (ep T x' y) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((Hf D T (x - x') y).im : ℂ)) := by
  simp only [ep, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  rw [sub_eq_add_neg, Hf_add_left]
  have : Hf D T (-x') y = -Hf D T x' y := by
    have h := Hf_add_left T x' (-x') y
    rw [add_neg_cancel] at h
    have h0 : Hf D T 0 y = 0 := by simp [Hf]
    rw [h0] at h
    linear_combination -h
  rw [this, Complex.add_im, Complex.neg_im]
  congr 1
  push_cast
  ring

theorem ep_eq_one_iff (t : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = 1 ↔ ∃ n : ℤ, t = n := by
  first | exact UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff .. | (apply UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff t

theorem int_shift {M : AddSubgroup (VC D N N')} [Countable M] {t : Set (VC D N N')}
    (ht : IsAddFundamentalDomain M t volume) (f : VC D N N' → ℂ)
    (hper : ∀ m ∈ M, ∀ z, f (z + m) = f z) (x : VC D N N') :
    ∫ z in t, f (z + x) = ∫ z in t, f z := by
  have hFd' : IsAddFundamentalDomain M (x +ᵥ t) volume := ht.vadd_of_comm x
  have h1 : ∫ z in t, f (z + x) = ∫ z in (fun z => x + z) '' t, f z := by
    have e := (measurePreserving_add_left volume x).setIntegral_image_emb
      (measurableEmbedding_addLeft x) f t
    rw [e]
    simp only [add_comm x]
  have himg : (fun z => x + z) '' t = x +ᵥ t := by rw [← Set.image_vadd]; rfl
  rw [h1, himg]
  refine hFd'.setIntegral_eq ht fun g z => ?_
  rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
  exact hper g g.2 z

theorem int_zero_of_char {M : AddSubgroup (VC D N N')} [Countable M] {t : Set (VC D N N')}
    (ht : IsAddFundamentalDomain M t volume) (f : VC D N N' → ℂ)
    (hper : ∀ m ∈ M, ∀ z, f (z + m) = f z) (y : VC D N N') (lam : ℂ) (hlam : lam ≠ 1)
    (hy : ∀ z, f (z + y) = lam * f z) :
    ∫ z in t, f z = 0 := by
  have h := int_shift ht f hper y
  simp only [hy] at h
  rw [integral_const_mul] at h
  have : (lam - 1) * ∫ z in t, f z = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hlam)

theorem intOn_of_full {M : AddSubgroup (VC D N N')} (hM : FullLat M) {t : Set (VC D N N')}
    (ht : IsAddFundamentalDomain M t volume) (f : VC D N N' → ℂ) (hf : Continuous f)
    (hper : ∀ m ∈ M, ∀ z, f (z + m) = f z) : IntegrableOn f t volume := by
  obtain ⟨hd, hs⟩ := hM
  let L : Submodule ℤ (VC D N N') := M.toIntSubmodule
  have : DiscreteTopology L := hd
  have : IsZLattice ℝ L := ⟨hs⟩
  have : Countable M := (inferInstance : Countable L)
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ
  have h0 : IsAddFundamentalDomain M (ZSpan.fundamentalDomain b) volume :=
    ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) volume
  have hb : Bornology.IsBounded (ZSpan.fundamentalDomain b) := ZSpan.fundamentalDomain_isBounded b
  have hc : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  have hi : IntegrableOn f (ZSpan.fundamentalDomain b) volume :=
    (hf.continuousOn.integrableOn_compact hc).mono_set subset_closure
  refine (h0.integrableOn_iff ht ?_).1 hi
  intro g z
  rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
  exact hper g g.2 z

theorem countable_of_full {M : AddSubgroup (VC D N N')} (hM : FullLat M) : Countable M := by
  obtain ⟨hd, hs⟩ := hM
  let L : Submodule ℤ (VC D N N') := M.toIntSubmodule
  have : DiscreteTopology L := hd
  have : IsZLattice ℝ L := ⟨hs⟩
  exact (inferInstance : Countable L)

theorem fd_of_full {M : AddSubgroup (VC D N N')} (hM : FullLat M) :
    ∃ t : Set (VC D N N'), IsAddFundamentalDomain M t volume := by
  obtain ⟨hd, hs⟩ := hM
  let L : Submodule ℤ (VC D N N') := M.toIntSubmodule
  have : DiscreteTopology L := hd
  have : IsZLattice ℝ L := ⟨hs⟩
  exact ⟨_, ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) volume⟩

theorem full_inf {La₁ La₂ : AddSubgroup (VC D N N')} (h₁ : FullLat La₁) (h₂ : FullLat La₂)
    [Finite (La₂ ⧸ La₁.addSubgroupOf La₂)] : FullLat (La₁ ⊓ La₂) := by
  obtain ⟨hd, -⟩ := h₁
  obtain ⟨-, hs⟩ := h₂
  haveI := hd
  constructor
  · exact DiscreteTopology.of_continuous_injective
      (f := AddSubgroup.inclusion (inf_le_left : La₁ ⊓ La₂ ≤ La₁))
      (continuous_inclusion inf_le_left) (AddSubgroup.inclusion_injective _)
  · haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
    set k := Fintype.card (La₂ ⧸ La₁.addSubgroupOf La₂)
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [eq_top_iff, ← hs, Submodule.span_le]
    intro x hx
    have hmem : k • x ∈ La₁ ⊓ La₂ := by
      have h0 := card_nsmul_eq_zero (x := (QuotientAddGroup.mk (⟨x, hx⟩ : La₂) :
        La₂ ⧸ La₁.addSubgroupOf La₂))
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_addSubgroupOf] at h0
      exact ⟨by simpa using h0, La₂.nsmul_mem hx k⟩
    have : x = (k : ℝ)⁻¹ • (k • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hk, one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IL

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MeasureTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO
open scoped Pointwise ENNReal Function

variable {D : D7} {N N' : ℕ}

theorem Hf_cont_left (T : Tor D) (w : VC D N N') : Continuous fun z : VC D N N' => Hf D T z w := by
  unfold Hf; fun_prop

theorem Hf_cont_diag (T : Tor D) : Continuous fun z : VC D N N' => Hf D T z z := by
  unfold Hf; fun_prop

theorem U_cont (T : Tor D) {G : VC D N N' → ℂ} (hG : Continuous G) (x : VC D N N') :
    Continuous (U D T x G) := by
  have h1 := Hf_cont_left T x
  unfold U; fun_prop

theorem dens_cont (T : Tor D) {G : VC D N N' → ℂ} (hG : Continuous G) :
    Continuous (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T G) := by
  have h1 := Hf_cont_diag T (N := N) (N' := N')
  unfold Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens; fun_prop

theorem crD_cont (T : Tor D) {A B : VC D N N' → ℂ} (hA : Continuous A) (hB : Continuous B) :
    Continuous (crD T A B) := by
  have h1 := Hf_cont_diag T (N := N) (N' := N')
  unfold crD; fun_prop

theorem crD_self (T : Tor D) (A : VC D N N' → ℂ) (z : VC D N N') :
    crD T A A z = ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T A z : ℝ) : ℂ) := by
  simp only [crD, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

theorem normSq_eq (T : Tor D) (La' : AddSubgroup (VC D N N')) (G : VC D N N' → ℂ) :
    normSq D T La' G = ⨍ z in Classical.epsilon
      (fun Fd => IsAddFundamentalDomain La' Fd volume), Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T G z := rfl

theorem crD_Mper (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T La₁) (hZ : ∀ x ∈ La₂, ∀ y ∈ La₂, ∃ b : ℤ, (Hf D T x y).im = b)
    {x x' : VC D N N'} (hx : x ∈ La₂) (hx' : x' ∈ La₂) :
    ∀ m ∈ La₁ ⊓ La₂, ∀ z, crD T (trm T G x) (trm T G x') (z + m) =
      crD T (trm T G x) (trm T G x') z := by
  intro m hm z
  rw [crD_shift T hG hm.1, ep_mul_conj]
  obtain ⟨b, hb⟩ := hZ (x - x') (La₂.sub_mem hx hx') m hm.2
  rw [hb, (ep_eq_one_iff _).2 ⟨b, rfl⟩, one_mul]

theorem trm_cont (T : Tor D) {G : VC D N N' → ℂ} (hG : Continuous G) (x : VC D N N') :
    Continuous (trm T G x) := by
  have := U_cont T hG x
  unfold trm; fun_prop

theorem iso_core (T : Tor D) {La₁ La₂ : AddSubgroup (VC D N N')}
    (h₁ : FullLat La₁) (h₂ : FullLat La₂)
    [Finite (La₂ ⧸ La₁.addSubgroupOf La₂)] [Finite (La₁ ⧸ La₂.addSubgroupOf La₁)]
    (hZ : ∀ x ∈ La₂, ∀ y ∈ La₂, ∃ b : ℤ, (Hf D T x y).im = b)
    (hS : SemiChar T La₂)
    (hSD : ∀ v ∈ La₂, (∀ y ∈ La₁, ∃ b : ℤ, (Hf D T v y).im = b) → v ∈ La₁)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T La₁) :
    normSq D T La₂ (Iop D T La₁ La₂ G) = normSq D T La₁ G := by
  classical
  set M := La₁ ⊓ La₂ with hMdef
  have hM : FullLat M := full_inf h₁ h₂
  haveI : Countable La₁ := countable_of_full h₁
  haveI : Countable La₂ := countable_of_full h₂
  haveI : Countable M := countable_of_full hM
  haveI : Finite (La₁ ⧸ M.addSubgroupOf La₁) := by
    rw [hMdef, AddSubgroup.inf_addSubgroupOf_left]; infer_instance
  haveI : Finite (La₂ ⧸ M.addSubgroupOf La₂) := by
    rw [hMdef, AddSubgroup.inf_addSubgroupOf_right]; infer_instance
  obtain ⟨t, ht⟩ := fd_of_full hM
  have hs₁ := Classical.epsilon_spec (fd_of_full h₁)
  have hs₂ := Classical.epsilon_spec (fd_of_full h₂)
  have hGc : Continuous G := hG.1.continuous

  have hA : normSq D T La₁ G = ⨍ z in t, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T G z := by
    rw [normSq_eq]
    exact (avg_sub inf_le_left hs₁ ht _ (fun z => by unfold Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens; positivity)
      (dens_cont T hGc) fun g hg z => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens_periodic T La₁ G hG g hg z).symm

  have hIG := Iop_mem_ThSp T hS hG
  have hB : normSq D T La₂ (Iop D T La₁ La₂ G) =
      ⨍ z in t, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z := by
    rw [normSq_eq]
    exact (avg_sub inf_le_right hs₂ ht _ (fun z => by unfold Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens; positivity)
      (dens_cont T hIG.1.continuous)
      fun g hg z => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens_periodic T La₂ _ hIG g hg z).symm
  rw [hA, hB]
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  set Q := La₂ ⧸ La₁.addSubgroupOf La₂
  set k := Fintype.card Q
  have hk : k ≠ 0 := Fintype.card_ne_zero
  have hidx : (La₁.addSubgroupOf La₂).index = k := by
    rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  let xr : Q → VC D N N' := fun q => ((Quotient.out q : La₂) : VC D N N')
  have hxr : ∀ q, xr q ∈ La₂ := fun q => (Quotient.out q).2
  set c : ℂ := Complex.ofReal ((Real.sqrt (k : ℝ))⁻¹)
  have hI : ∀ z, Iop D T La₁ La₂ G z = c * ∑ q : Q, trm T G (xr q) z := by
    intro z
    simp only [Iop, hidx, finsum_eq_sum_of_fintype, trm, c, xr]
    push_cast; rfl

  have hdens : ∀ z, ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z : ℝ) : ℂ) =
      c * starRingEnd ℂ c * ∑ q : Q, ∑ q' : Q, crD T (trm T G (xr q)) (trm T G (xr q')) z := by
    intro z
    rw [← crD_self]
    have e1 : crD T (Iop D T La₁ La₂ G) (Iop D T La₁ La₂ G) z =
        c * starRingEnd ℂ c * ((∑ q : Q, trm T G (xr q) z) *
          starRingEnd ℂ (∑ q' : Q, trm T G (xr q') z) *
          (Real.exp (-Real.pi * (Hf D T z z).re) : ℂ)) := by
      simp only [crD, hI, map_mul]; ring
    rw [e1, map_sum, Finset.sum_mul_sum]
    simp_rw [Finset.sum_mul]
    rfl
  have hint : ∀ q q' : Q, IntegrableOn (crD T (trm T G (xr q)) (trm T G (xr q'))) t volume :=
    fun q q' => intOn_of_full hM ht _ (crD_cont T (trm_cont T hGc _) (trm_cont T hGc _))
      (crD_Mper T hG hZ (hxr q) (hxr q'))

  have hoff : ∀ q q' : Q, q ≠ q' → ∫ z in t, crD T (trm T G (xr q)) (trm T G (xr q')) z = 0 := by
    intro q q' hqq
    have hnot : xr q - xr q' ∉ La₁ := by
      intro hin
      apply hqq
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf]
      have : ((-Quotient.out q + Quotient.out q' : La₂) : VC D N N') = -(xr q - xr q') := by
        simp only [xr, AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
      rw [this]; exact La₁.neg_mem hin
    have hex : ∃ y ∈ La₁, ∀ b : ℤ, (Hf D T (xr q - xr q') y).im ≠ b := by
      by_contra hcon
      push Not at hcon
      exact hnot (hSD _ (La₂.sub_mem (hxr q) (hxr q')) hcon)
    obtain ⟨y, hy, hb⟩ := hex
    refine int_zero_of_char ht _ (crD_Mper T hG hZ (hxr q) (hxr q')) y _ ?_
      (fun z => by rw [crD_shift T hG hy, ep_mul_conj])
    intro h1
    obtain ⟨n, hn⟩ := (ep_eq_one_iff _).1 h1
    exact hb n hn

  have hdiag : ∀ q : Q, ∫ z in t, crD T (trm T G (xr q)) (trm T G (xr q)) z =
      ∫ z in t, ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T G z : ℝ) : ℂ) := by
    intro q
    have h1 : ∀ z, crD T (trm T G (xr q)) (trm T G (xr q)) z =
        ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T G (z + xr q) : ℝ) : ℂ) := by
      intro z
      have := crD_smul T (al D T (xr q)) (al D T (xr q)) (U D T (xr q) G) (U D T (xr q) G) z
      show crD T (fun w => al D T (xr q) * U D T (xr q) G w)
        (fun w => al D T (xr q) * U D T (xr q) G w) z = _
      rw [this, al_mul_conj, one_mul, crD_U, crD_self]
    simp only [h1]
    exact int_shift ht (fun z => ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T G z : ℝ) : ℂ))
      (fun m hm z => by rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens_periodic T La₁ G hG m hm.1 z]) (xr q)
  have hsum : ∫ z in t, ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z : ℝ) : ℂ) =
      c * starRingEnd ℂ c * (k * ∫ z in t, ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T G z : ℝ) : ℂ)) := by
    simp only [hdens]
    rw [integral_const_mul, integral_finsetSum _ fun q _ => ?_]
    · congr 1
      rw [Finset.sum_congr rfl fun q _ => integral_finsetSum _ fun q' _ => hint q q']
      rw [Finset.sum_congr rfl fun q _ => Finset.sum_eq_single q (fun q' _ h => hoff q q' (Ne.symm h))
        (fun h => absurd (Finset.mem_univ q) h)]
      simp only [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl
    · exact integrable_finsetSum _ fun q' _ => hint q q'
  have hcc : c * starRingEnd ℂ c * (k : ℂ) = 1 := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hr : (Real.sqrt (k : ℝ))⁻¹ * (Real.sqrt (k : ℝ))⁻¹ * (k : ℝ) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), inv_mul_cancel₀ hk']
    simp only [c, Complex.conj_ofReal]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hr, Complex.ofReal_one]
  have hreal : ∫ z in t, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T (Iop D T La₁ La₂ G) z =
      ∫ z in t, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.dens D T G z := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal, ← integral_complex_ofReal, hsum, ← mul_assoc, hcc, one_mul]
  rw [setAverage_eq, setAverage_eq, hreal]

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IL

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric MeasureTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

def HfIntRec : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      HfInt (tor0 D cc δ) (La D (tor0 D cc δ) L L')

def SelfDualRec : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ v : VC D N N', (∀ y ∈ La D (tor0 D cc δ) L L', ∃ b : ℤ, (Hf D (tor0 D cc δ) v y).im = b) →
        v ∈ La D (tor0 D cc δ) L L'

theorem IopIso_of_parts (hA : HfIntRec) (hB : SelfDualRec) :
    ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      IopIso D (tor0 D cc δ) := by
  intro D cc hcc δ hδ N N' L₁ L₁' L₂ L₂' h1 h2 G hG
  by_cases h0 : δ = 0
  · subst h0
    have e1 := FL.La_zero D L₁ L₁' cc
    have e2 := FL.La_zero D L₂ L₂' cc
    have hle : La D (tor0 D cc 0) L₂ L₂' ≤ La D (tor0 D cc 0) L₁ L₁' := by rw [e1, e2]
    rw [IO.Iop_of_le _ hle hG, e1, e2]
  · have f1 := FL.fullLat D L₁ L₁' h1 cc hcc δ h0
    have f2 := FL.fullLat D L₂ L₂' h2 cc hcc δ h0
    haveI := La_index_finite cc hcc δ L₁ L₂ L₁' L₂' h1 h2
    haveI := La_index_finite cc hcc δ L₂ L₁ L₂' L₁' h2 h1
    have hI2 := hA D cc hcc δ hδ h0 N N' L₂ L₂' h2
    refine IL.iso_core _ f1 f2 ?_ (semiChar_of_HfInt _ hI2) ?_ hG
    · intro x hx y hy
      obtain ⟨a, b, -, h⟩ := hI2 x hx y hy
      exact ⟨b, by rw [h]; simp⟩
    · intro v _ hv
      exact hB D cc hcc δ hδ h0 N N' L₁ L₁' h1 v hv

theorem LinkThIndep_of_parts (hA : HfIntRec) (hB : SelfDualRec) : LinkThIndep :=
  LinkThIndep_of_IopIso (IopIso_of_parts hA hB)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
