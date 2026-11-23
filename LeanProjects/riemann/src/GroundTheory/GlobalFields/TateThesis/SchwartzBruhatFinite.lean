import Mathlib
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
  Topology Filter
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem isOpen_idealFiniteAdeles (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsOpen (idealFiniteAdeles I : Set 𝔸ᶠ[K]) := by
  rw [idealFiniteAdeles_eq_smul]
  exact isOpen_integralFiniteAdeles.smul _

theorem isCompact_idealFiniteAdeles (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsCompact (idealFiniteAdeles I : Set 𝔸ᶠ[K]) := by
  rw [idealFiniteAdeles_eq_smul]
  exact (isCompact_integralFiniteAdeles K).smul _

theorem measurableSet_idealFiniteAdeles (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeasurableSet (idealFiniteAdeles I : Set 𝔸ᶠ[K]) :=
  (isOpen_idealFiniteAdeles I).measurableSet

theorem exists_idealFiniteAdeles_subset {W : Set 𝔸ᶠ[K]} (hW : W ∈ 𝓝 (0 : 𝔸ᶠ[K])) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, (idealFiniteAdeles I : Set 𝔸ᶠ[K]) ⊆ W := by
  obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW
  have h𝔞 : Ideal.span {d} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hI : ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  refine ⟨Units.mk0 _ hI, fun x hx ↦ ?_⟩
  have hdK : (algebraMap (𝓞 K) K d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
  set y : 𝔸ᶠ[K] := algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d)⁻¹ * x with hy
  have hxy : x = algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d) * y := by
    rw [hy, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hdK, map_one, one_mul]
  rw [hxy]
  refine hd y fun v ↦ ?_
  change (((algebraMap (𝓞 K) K d)⁻¹ : K) : v.adicCompletion K) * x v ∈ v.adicCompletionIntegers K
  obtain ⟨z, hz, hzv⟩ := exists_mem_ideal_intValuation_eq v h𝔞
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have hle : exp (-FractionalIdeal.count K v
      ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) ≤ v.intValuation d := by
    rw [← hzv, map_mul]
    exact mul_le_of_le_one_left' (v.intValuation_le_one r)
  have hxv := hx v
  rw [mem_adicCompletionIntegers, Valuation.map_mul, valuedAdicCompletion_eq_valuation', map_inv₀,
    valuation_of_algebraMap]
  refine (inv_mul_le_one_iff_withZero ?_).mpr (hxv.trans hle)
  rw [Ne, ← valuation_of_algebraMap (K := K), map_eq_zero]
  exact hdK

variable (K) in

def finiteSchwartzBruhat : Submodule ℂ (𝔸ᶠ[K] → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.comp_left (smul_zero c)⟩

theorem mem_finiteSchwartzBruhat {f : 𝔸ᶠ[K] → ℂ} :
    f ∈ finiteSchwartzBruhat K ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

def cosetIndicator (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : 𝔸ᶠ[K]) : 𝔸ᶠ[K] → ℂ :=
  (a +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])).indicator 1

theorem mem_vadd_idealFiniteAdeles {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {a x : 𝔸ᶠ[K]} :
    x ∈ a +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K]) ↔ x - a ∈ idealFiniteAdeles I := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, SetLike.mem_coe]

open Classical in
theorem cosetIndicator_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a x : 𝔸ᶠ[K]) :
    cosetIndicator I a x = if x - a ∈ idealFiniteAdeles I then 1 else 0 := by
  rw [cosetIndicator, Set.indicator_apply]
  simp only [mem_vadd_idealFiniteAdeles, Pi.one_apply]

theorem cosetIndicator_zero_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    cosetIndicator I 0 = (idealFiniteAdeles I : Set 𝔸ᶠ[K]).indicator 1 := by
  rw [cosetIndicator, zero_vadd]

theorem cosetIndicator_mem_finiteSchwartzBruhat (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : 𝔸ᶠ[K]) :
    cosetIndicator I a ∈ finiteSchwartzBruhat K := by
  classical
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x₀ ↦ ?_, ?_⟩
  · have hW : {x : 𝔸ᶠ[K] | x - x₀ ∈ idealFiniteAdeles I} ∈ 𝓝 x₀ :=
      ((isOpen_idealFiniteAdeles I).preimage (continuous_id.sub continuous_const)).mem_nhds
        (by simp)
    filter_upwards [hW] with x hx
    rw [cosetIndicator_apply, cosetIndicator_apply]
    have : x - a = (x - x₀) + (x₀ - a) := by abel
    rw [this, AddSubgroup.add_mem_cancel_left _ hx]
  · refine HasCompactSupport.intro ((isCompact_idealFiniteAdeles I).vadd a) fun x hx ↦ ?_
    exact Set.indicator_of_notMem hx _

theorem exists_forall_add_eq_of_mem_finiteSchwartzBruhat {f : 𝔸ᶠ[K] → ℂ}
    (hf : f ∈ finiteSchwartzBruhat K) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ x, ∀ h ∈ idealFiniteAdeles I, f (x + h) = f x := by
  have hloc : ∀ x : 𝔸ᶠ[K], ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      ∀ h ∈ idealFiniteAdeles J, f (x + h) = f x := by
    intro x
    have h1 : ∀ᶠ h in 𝓝 (0 : 𝔸ᶠ[K]), f (x + h) = f x :=
      ((continuous_const_add x).tendsto' 0 x (add_zero x)).eventually (hf.1.eventually_eq x)
    obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset h1
    exact ⟨J, fun h hh ↦ hJ hh⟩
  choose J hJ using hloc
  obtain ⟨t, ht⟩ := hf.2.isCompact.elim_finite_subcover
    (fun x ↦ x +ᵥ (idealFiniteAdeles (J x) : Set 𝔸ᶠ[K]))
    (fun x ↦ (isOpen_idealFiniteAdeles (J x)).vadd x)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, mem_vadd_idealFiniteAdeles.mpr (by simp)⟩)
  have hW : (⋂ x ∈ t, (idealFiniteAdeles (J x) : Set 𝔸ᶠ[K])) ∈ 𝓝 (0 : 𝔸ᶠ[K]) :=
    (biInter_finset_mem t).mpr fun x _ ↦
      (isOpen_idealFiniteAdeles (J x)).mem_nhds (zero_mem _)
  obtain ⟨I, hI⟩ := exists_idealFiniteAdeles_subset hW
  have hmain : ∀ x ∈ tsupport f, ∀ h ∈ idealFiniteAdeles I, f (x + h) = f x := by
    intro x hx h hh
    obtain ⟨x₀, hx₀t, hxx₀⟩ := Set.mem_iUnion₂.mp (ht hx)
    rw [mem_vadd_idealFiniteAdeles] at hxx₀
    have hh' : h ∈ idealFiniteAdeles (J x₀) := Set.mem_iInter₂.mp (hI hh) x₀ hx₀t
    have e1 := hJ x₀ (x - x₀) hxx₀
    have e2 := hJ x₀ (x + h - x₀) (by
      have : x + h - x₀ = (x - x₀) + h := by abel
      rw [this]
      exact add_mem hxx₀ hh')
    rw [add_sub_cancel] at e1 e2
    rw [e1, e2]
  refine ⟨I, fun x h hh ↦ ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hmain x hx h hh
  · by_cases hxh : x + h ∈ tsupport f
    · have := hmain (x + h) hxh (-h) (neg_mem hh)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxh]

theorem exists_eq_sum_cosetIndicator {f : 𝔸ᶠ[K] → ℂ} (hf : f ∈ finiteSchwartzBruhat K) :
    ∃ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : Finset 𝔸ᶠ[K]),
      f = ∑ a ∈ s, f a • cosetIndicator I a := by
  classical
  obtain ⟨I, hI⟩ := exists_forall_add_eq_of_mem_finiteSchwartzBruhat hf
  let H := idealFiniteAdeles I
  have : DiscreteTopology (𝔸ᶠ[K] ⧸ H) := QuotientAddGroup.discreteTopology (isOpen_idealFiniteAdeles I)
  have hS : ((QuotientAddGroup.mk : 𝔸ᶠ[K] → 𝔸ᶠ[K] ⧸ H) '' tsupport f).Finite :=
    (hf.2.isCompact.image continuous_quotient_mk').finite_of_discrete
  have hmk : ∀ a x : 𝔸ᶠ[K], x - a ∈ idealFiniteAdeles I ↔
      (QuotientAddGroup.mk x : 𝔸ᶠ[K] ⧸ H) = QuotientAddGroup.mk a := by
    intro a x
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_sub, sub_eq_neg_add]
  have hinj : Set.InjOn (fun q : 𝔸ᶠ[K] ⧸ H ↦ q.out) ↑hS.toFinset :=
    fun q _ q' _ h ↦ by simpa using congrArg (QuotientAddGroup.mk (s := H)) h
  refine ⟨I, hS.toFinset.image fun q ↦ q.out, ?_⟩
  rw [Finset.sum_image hinj]
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, cosetIndicator_apply, mul_ite, mul_one, mul_zero, hmk,
    QuotientAddGroup.out_eq']
  rw [Finset.sum_ite_eq]
  split_ifs with hx
  · have hq := QuotientAddGroup.out_eq' (s := H) (QuotientAddGroup.mk x)
    rw [← hmk] at hq
    have := hI x (Quotient.out (QuotientAddGroup.mk x : 𝔸ᶠ[K] ⧸ H) - x) hq
    rw [add_sub_cancel] at this
    exact this.symm
  · exact image_eq_zero_of_notMem_tsupport fun hx' ↦ hx ((Set.Finite.mem_toFinset hS).mpr
      ⟨x, hx', rfl⟩)

theorem finiteSchwartzBruhat_eq_span :
    finiteSchwartzBruhat K = Submodule.span ℂ
      (Set.range fun p : (FractionalIdeal (𝓞 K)⁰ K)ˣ × 𝔸ᶠ[K] ↦ cosetIndicator p.1 p.2) := by
  refine le_antisymm (fun f hf ↦ ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨I, s, hs⟩ := exists_eq_sum_cosetIndicator hf
    rw [hs]
    exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(I, a), rfl⟩)
  · rintro _ ⟨p, rfl⟩
    exact cosetIndicator_mem_finiteSchwartzBruhat p.1 p.2

theorem integrable_of_mem_finiteSchwartzBruhat {f : 𝔸ᶠ[K] → ℂ} (hf : f ∈ finiteSchwartzBruhat K) :
    Integrable f (finiteAdeleMeasure K) :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

variable (K) in

def finiteFourier (f : 𝔸ᶠ[K] → ℂ) (y : 𝔸ᶠ[K]) : ℂ :=
  ∫ x, f x * (finiteAdelicChar K (x * y) : ℂ) ∂finiteAdeleMeasure K

theorem continuous_finiteAdelicChar_mul (y : 𝔸ᶠ[K]) :
    Continuous fun x : 𝔸ᶠ[K] ↦ (finiteAdelicChar K (x * y) : ℂ) :=
  continuous_subtype_val.comp (continuous_finiteAdelicChar.comp (continuous_mul_const y))

theorem integrable_mul_finiteAdelicChar {f : 𝔸ᶠ[K] → ℂ} (hf : Integrable f (finiteAdeleMeasure K))
    (y : 𝔸ᶠ[K]) :
    Integrable (fun x ↦ f x * (finiteAdelicChar K (x * y) : ℂ)) (finiteAdeleMeasure K) :=
  hf.mono (hf.1.mul (continuous_finiteAdelicChar_mul y).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ by rw [norm_mul, Circle.norm_coe, mul_one])

theorem finiteFourier_add {f g : 𝔸ᶠ[K] → ℂ} (hf : Integrable f (finiteAdeleMeasure K))
    (hg : Integrable g (finiteAdeleMeasure K)) :
    finiteFourier K (f + g) = finiteFourier K f + finiteFourier K g := by
  funext y
  simp only [finiteFourier, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_finiteAdelicChar hf y) (integrable_mul_finiteAdelicChar hg y)

theorem finiteFourier_smul (c : ℂ) (f : 𝔸ᶠ[K] → ℂ) :
    finiteFourier K (c • f) = c • finiteFourier K f := by
  funext y
  simp only [finiteFourier, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem finiteFourier_zero : finiteFourier K (0 : 𝔸ᶠ[K] → ℂ) = 0 := by
  funext y
  simp [finiteFourier]

theorem integral_indicator_mul_finiteAdelicChar (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (w : 𝔸ᶠ[K]) :
    ∫ x, (idealFiniteAdeles I : Set 𝔸ᶠ[K]).indicator (1 : 𝔸ᶠ[K] → ℂ) x *
        (finiteAdelicChar K (x * w) : ℂ) ∂finiteAdeleMeasure K =
      ((finiteAdeleMeasure K (idealFiniteAdeles I)).toReal : ℂ) *
        (idealFiniteAdeles (traceDualIdeal K I) : Set 𝔸ᶠ[K]).indicator 1 w := by
  classical
  set H : Set 𝔸ᶠ[K] := ((idealFiniteAdeles I : AddSubgroup 𝔸ᶠ[K]) : Set 𝔸ᶠ[K]) with hH
  by_cases hw : w ∈ idealFiniteAdeles (traceDualIdeal K I)
  · have h1 := (forall_finiteAdelicChar_mul_eq_one_iff I w).mpr hw
    have : (fun x ↦ H.indicator (1 : 𝔸ᶠ[K] → ℂ) x * (finiteAdelicChar K (x * w) : ℂ)) =
        H.indicator 1 := by
      funext x
      by_cases hx : x ∈ H
      · rw [Set.indicator_of_mem hx, h1 x hx]
        simp
      · rw [Set.indicator_of_notMem hx, zero_mul]
    rw [this]
    refine (integral_indicator_const (μ := finiteAdeleMeasure K) (1 : ℂ)
      (by rw [hH]; exact measurableSet_idealFiniteAdeles I)).trans ?_
    rw [Set.indicator_of_mem (SetLike.mem_coe.mpr hw), Pi.one_apply, mul_one, measureReal_def,
      Complex.real_smul, mul_one]
  · obtain ⟨h₀, hh₀, hne⟩ : ∃ h₀ ∈ idealFiniteAdeles I, finiteAdelicChar K (h₀ * w) ≠ 1 := by
      by_contra hcon
      exact hw ((forall_finiteAdelicChar_mul_eq_one_iff I w).mp fun x hx ↦
        by_contra fun h ↦ hcon ⟨x, hx, h⟩)
    set F : 𝔸ᶠ[K] → ℂ := fun x ↦ H.indicator 1 x * (finiteAdelicChar K (x * w) : ℂ)
    have hshift : ∀ x, F (x + h₀) = (finiteAdelicChar K (h₀ * w) : ℂ) * F x := by
      intro x
      have hmem : x + h₀ ∈ H ↔ x ∈ H := AddSubgroup.add_mem_cancel_right _ hh₀
      simp only [F, Set.indicator_apply, hmem, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul,
        Pi.one_apply]
      split_ifs <;> ring
    have hint : ∫ x, F x ∂finiteAdeleMeasure K =
        (finiteAdelicChar K (h₀ * w) : ℂ) * ∫ x, F x ∂finiteAdeleMeasure K := by
      rw [← integral_const_mul, ← integral_add_right_eq_self F h₀]
      simp only [hshift]
    have hne' : (finiteAdelicChar K (h₀ * w) : ℂ) ≠ 1 := by
      rwa [Ne, Circle.coe_eq_one]
    have h0 : ∫ x, F x ∂finiteAdeleMeasure K = 0 := by
      have : ((finiteAdelicChar K (h₀ * w) : ℂ) - 1) * ∫ x, F x ∂finiteAdeleMeasure K = 0 := by
        rw [sub_mul, ← hint, one_mul, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne')
    rw [show (∫ x, H.indicator (1 : 𝔸ᶠ[K] → ℂ) x * (finiteAdelicChar K (x * w) : ℂ)
        ∂finiteAdeleMeasure K) = ∫ x, F x ∂finiteAdeleMeasure K from rfl, h0,
      Set.indicator_of_notMem (by simpa using hw), mul_zero]

theorem finiteFourier_cosetIndicator (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a y : 𝔸ᶠ[K]) :
    finiteFourier K (cosetIndicator I a) y =
      ((finiteAdeleMeasure K (idealFiniteAdeles I)).toReal : ℂ) *
        ((finiteAdelicChar K (a * y) : ℂ) *
          (idealFiniteAdeles (traceDualIdeal K I) : Set 𝔸ᶠ[K]).indicator 1 y) := by
  classical
  rw [finiteFourier, ← integral_add_left_eq_self _ a]
  have : (fun x ↦ cosetIndicator I a (a + x) * (finiteAdelicChar K ((a + x) * y) : ℂ)) =
      fun x ↦ (finiteAdelicChar K (a * y) : ℂ) *
        ((idealFiniteAdeles I : Set 𝔸ᶠ[K]).indicator (1 : 𝔸ᶠ[K] → ℂ) x *
          (finiteAdelicChar K (x * y) : ℂ)) := by
    funext x
    rw [cosetIndicator_apply, add_sub_cancel_left, Set.indicator_apply, add_mul,
      AddChar.map_add_eq_mul, Circle.coe_mul]
    simp only [SetLike.mem_coe, Pi.one_apply]
    ring
  rw [this, integral_const_mul, integral_indicator_mul_finiteAdelicChar]
  ring

theorem isLocallyConstant_finiteAdelicChar_mul (a : 𝔸ᶠ[K]) :
    IsLocallyConstant fun y : 𝔸ᶠ[K] ↦ (finiteAdelicChar K (a * y) : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun y₀ ↦ ?_
  have hW : {y : 𝔸ᶠ[K] | a * (y - y₀) ∈ finiteInvDifferent K} ∈ 𝓝 y₀ :=
    ((isOpen_finiteInvDifferent K).preimage
      (continuous_const.mul (continuous_id.sub continuous_const))).mem_nhds (by simp)
  filter_upwards [hW] with y hy
  have : a * y = a * y₀ + a * (y - y₀) := by ring
  rw [this, AddChar.map_add_eq_mul, finiteAdelicChar_eq_one_of_mem hy, mul_one]

theorem finiteAdelicChar_mul_indicator_mem (a : 𝔸ᶠ[K]) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (fun y ↦ (finiteAdelicChar K (a * y) : ℂ) *
      (idealFiniteAdeles J : Set 𝔸ᶠ[K]).indicator 1 y) ∈ finiteSchwartzBruhat K := by
  have h := cosetIndicator_mem_finiteSchwartzBruhat J 0
  rw [cosetIndicator_zero_eq] at h
  exact ⟨(isLocallyConstant_finiteAdelicChar_mul a).mul h.1, h.2.mul_left⟩

theorem finiteFourier_finiteAdelicChar_mul_indicator (a : 𝔸ᶠ[K])
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (z : 𝔸ᶠ[K]) :
    finiteFourier K (fun y ↦ (finiteAdelicChar K (a * y) : ℂ) *
        (idealFiniteAdeles J : Set 𝔸ᶠ[K]).indicator 1 y) z =
      ((finiteAdeleMeasure K (idealFiniteAdeles J)).toReal : ℂ) *
        (idealFiniteAdeles (traceDualIdeal K J) : Set 𝔸ᶠ[K]).indicator 1 (a + z) := by
  rw [finiteFourier, ← integral_indicator_mul_finiteAdelicChar]
  congr 1
  funext y
  have : y * (a + z) = a * y + y * z := by ring
  rw [this, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem finiteFourier_mem_finiteSchwartzBruhat {f : 𝔸ᶠ[K] → ℂ}
    (hf : f ∈ finiteSchwartzBruhat K) : finiteFourier K f ∈ finiteSchwartzBruhat K := by
  rw [finiteSchwartzBruhat_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨I, a⟩, rfl⟩ := hg
    have : finiteFourier K (cosetIndicator I a) =
        ((finiteAdeleMeasure K (idealFiniteAdeles I)).toReal : ℂ) •
          fun y ↦ (finiteAdelicChar K (a * y) : ℂ) *
            (idealFiniteAdeles (traceDualIdeal K I) : Set 𝔸ᶠ[K]).indicator 1 y := by
      funext y
      rw [finiteFourier_cosetIndicator, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (finiteAdelicChar_mul_indicator_mem a _)
  | zero => rw [finiteFourier_zero]; exact zero_mem _
  | add g h hg hh ihg ihh =>
    rw [← finiteSchwartzBruhat_eq_span] at hg hh
    rw [finiteFourier_add (integrable_of_mem_finiteSchwartzBruhat hg)
      (integrable_of_mem_finiteSchwartzBruhat hh)]
    exact add_mem ihg ihh
  | smul c g _ ih =>
    rw [finiteFourier_smul]
    exact Submodule.smul_mem _ c ih

theorem finiteFourier_finiteFourier {f : 𝔸ᶠ[K] → ℂ} (hf : f ∈ finiteSchwartzBruhat K) :
    finiteFourier K (finiteFourier K f) = fun x ↦ f (-x) := by
  classical
  have key : ∀ f ∈ finiteSchwartzBruhat K,
      finiteFourier K (finiteFourier K f) = fun x ↦ f (-x) := by
    intro f hf
    rw [finiteSchwartzBruhat_eq_span] at hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨I, a⟩, rfl⟩ := hg
      have hF : finiteFourier K (cosetIndicator I a) =
          ((finiteAdeleMeasure K (idealFiniteAdeles I)).toReal : ℂ) •
            fun y ↦ (finiteAdelicChar K (a * y) : ℂ) *
              (idealFiniteAdeles (traceDualIdeal K I) : Set 𝔸ᶠ[K]).indicator 1 y := by
        funext y
        rw [finiteFourier_cosetIndicator, Pi.smul_apply, smul_eq_mul]
      funext z
      rw [hF, finiteFourier_smul, Pi.smul_apply, finiteFourier_finiteAdelicChar_mul_indicator,
        traceDualIdeal_traceDualIdeal, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
        finiteAdeleMeasure_idealFiniteAdeles_mul_traceDual, Complex.ofReal_one, one_mul]
      show _ = cosetIndicator I a (-z)
      rw [cosetIndicator_apply, Set.indicator_apply]
      have : -z - a = -(a + z) := by abel
      simp only [SetLike.mem_coe, Pi.one_apply, this, neg_mem_iff]
    | zero => funext x; simp [finiteFourier_zero]
    | add g h hg hh ihg ihh =>
      rw [← finiteSchwartzBruhat_eq_span] at hg hh
      rw [finiteFourier_add (integrable_of_mem_finiteSchwartzBruhat hg)
        (integrable_of_mem_finiteSchwartzBruhat hh),
        finiteFourier_add
          (integrable_of_mem_finiteSchwartzBruhat (finiteFourier_mem_finiteSchwartzBruhat hg))
          (integrable_of_mem_finiteSchwartzBruhat (finiteFourier_mem_finiteSchwartzBruhat hh)),
        ihg, ihh]
      rfl
    | smul c g _ ih =>
      rw [finiteFourier_smul, finiteFourier_smul, ih]
      rfl
  exact key f hf

end

end GroundTheory.Global
