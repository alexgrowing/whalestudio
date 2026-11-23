import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.FourierPi

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

def box (n : Type*) (s : kˣ) : Set (n → k) := Set.univ.pi fun _ => cball s

omit [DecidableEq n] in
theorem isOpen_box (s : kˣ) : IsOpen (box n s) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball s

omit [Fintype n] [DecidableEq n] in
theorem isCompact_box (s : kˣ) : IsCompact (box n s) :=
  isCompact_univ_pi fun _ => isCompact_cball s

omit [DecidableEq n] in
theorem exists_box_subset {U : Set (n → k)} (hU : U ∈ 𝓝 (0 : n → k)) : ∃ s : kˣ, box n s ⊆ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  have h1 : (⋂ i, t i) ∈ 𝓝 (0 : k) := Filter.iInter_mem.mpr ht
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  exact ⟨s, fun x hx => hsub fun i _ => Set.mem_iInter.mp (hs (hx i trivial)) i⟩

omit [DecidableEq n] in

theorem exists_box_invariant {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∃ s : kˣ, ∀ t ∈ box n s, ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : n → k), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (n → k) × (n → k) => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  obtain ⟨s, hs⟩ := exists_box_subset h1
  refine ⟨s, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hs ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · have := hs (show -t ∈ box n s from fun i _ => neg_mem_cball (ht i trivial)) _ hx'
    rw [← this, add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

omit [DecidableEq n] in
theorem continuous_dot : Continuous fun q : (n → k) × (n → k) => q.1 ⬝ᵥ q.2 :=
  continuous_fst.dotProduct continuous_snd

variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k]

theorem fourier_eq_zero_pi (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) {s : kˣ}
    {f : (n → k) → ℂ} (hs : ∀ t ∈ box n s, ∀ x, f (x + t) = f x) {y : n → k} (hy : y ∉ box n (c * s⁻¹)) :
    ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = 0 := by
  haveI := secondCountable k
  obtain ⟨i, hi⟩ : ∃ i, y i ∉ cball (c * s⁻¹) := by
    by_contra hne
    push Not at hne
    exact hy fun i _ => hne i
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one s hi
  have hbox : (Pi.single i t : n → k) ∈ box n s := by
    intro j _
    by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  have h1 := integral_add_right_eq_self (μ := μ) (fun x => f x * (ψ (x ⬝ᵥ y) : ℂ)) (Pi.single i t)
  have h2 : ∀ x, f (x + Pi.single i t) * (ψ ((x + Pi.single i t) ⬝ᵥ y) : ℂ) =
      (ψ (t * y i) : ℂ) * (f x * (ψ (x ⬝ᵥ y) : ℂ)) := by
    intro x
    rw [hs _ hbox, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
  simp only [h2, integral_const_mul] at h1
  have h3 : (ψ (t * y i) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
  refine (mul_eq_zero.mp ?_).resolve_left h3
  rw [sub_mul, h1, one_mul, sub_self]

theorem fourier_indicator_pi (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c) (s : kˣ)
    (x : n → k) :
    ∫ y, (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y ⬝ᵥ x) : ℂ) ∂μ =
      (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ)) x := by
  haveI := secondCountable k
  by_cases hx : x ∈ box n s
  · rw [Set.indicator_of_mem hx]
    have : ∀ y, (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y ⬝ᵥ x) : ℂ) =
        (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y := by
      intro y
      by_cases hy : y ∈ box n (c * s⁻¹)
      · have h1 : y ⬝ᵥ x ∈ cball c := by
          show valuation k (∑ i, y i * x i) ≤ valuation k (c : k)
          refine Valuation.map_sum_le (valuation k) fun i _ => ?_
          have h2 : valuation k (y i * x i) ≤ valuation k (((c * s⁻¹ : kˣ) : k) * s) := by
            rw [map_mul, map_mul]
            exact mul_le_mul' (hy i trivial) (hx i trivial)
          rwa [← Units.val_mul, inv_mul_cancel_right] at h2
        rw [h.eq_one h1, Circle.coe_one, mul_one]
      · simp [Set.indicator_of_notMem hy]
    simp only [this]
    rw [integral_indicator_const _ (isOpen_box _).measurableSet]
    simp
  · rw [Set.indicator_of_notMem hx]
    refine fourier_eq_zero_pi μ h (s := c * s⁻¹) (fun t ht y => ?_) (by simpa using hx)
    by_cases hy : y ∈ box n (c * s⁻¹)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem
        (show y + t ∈ box n (c * s⁻¹) from fun i _ => add_mem_cball (hy i trivial) (ht i trivial))]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
      intro h1
      exact hy fun i _ => by simpa using add_mem_cball (h1 i trivial) (neg_mem_cball (ht i trivial))

theorem fourier_mem_SB (μ : Measure (n → k)) [μ.IsAddRightInvariant] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (n → k) := by
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_,
    HasCompactSupport.intro (isCompact_box (c * s⁻¹)) fun y hy => fourier_eq_zero_pi μ h hs hy⟩
  have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport f, ψ (x ⬝ᵥ z) = ψ (x ⬝ᵥ y) := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : (n → k) × (n → k) => (ψ (q.2 ⬝ᵥ q.1), ψ (q.2 ⬝ᵥ y)) :=
      (h.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_fst)).prodMk
        (h.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_const))
    filter_upwards [h2.eventually_eq (y, x)] with q hq
    simp only [Prod.mk.injEq] at hq
    rw [hq.1, hq.2]
  filter_upwards [h1] with z hz
  congr 1
  funext x
  by_cases hx : x ∈ tsupport f
  · rw [hz x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem fourier_inversion_pi (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (h : HasConductor ψ c)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    ∃ s : kˣ, ∫ y, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∂μ =
      ((μ.real (box n s) * μ.real (box n (c * s⁻¹)) : ℝ) : ℂ) * f 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  refine ⟨s, ?_⟩
  set e : (n → k) → ℂ := (box n (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) with he
  have h1 : ∀ y, ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ = ∫ x, f x * (e y * (ψ (y ⬝ᵥ x) : ℂ)) ∂μ := by
    intro y
    by_cases hy : y ∈ box n (c * s⁻¹)
    · simp [he, Set.indicator_of_mem hy, dotProduct_comm y]
    · simp [he, Set.indicator_of_notMem hy, fourier_eq_zero_pi μ h hs hy]
  have hei : Integrable e μ :=
    (integrable_indicator_iff (isOpen_box _).measurableSet).mpr
      (integrableOn_const (isCompact_box _).measure_lt_top.ne)
  have hfi : Integrable f μ := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hint : Integrable (Function.uncurry fun y x => f x * (e y * (ψ (y ⬝ᵥ x) : ℂ))) (μ.prod μ) := by
    have h2 := (hei.mul_prod hfi).mul_bdd (c := 1) (g := fun q : (n → k) × (n → k) => (ψ (q.1 ⬝ᵥ q.2) : ℂ))
      (Continuous.aestronglyMeasurable
        (continuous_subtype_val.comp (h.continuous.comp continuous_dot)))
      (Filter.Eventually.of_forall fun q => (Circle.norm_coe _).le)
    refine h2.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry]
    ring
  simp only [h1]
  rw [integral_integral_swap hint]
  simp only [integral_const_mul, he, fourier_indicator_pi μ h s]
  have h3 : ∀ x, f x * (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ)) x =
      (box n s).indicator (fun _ => (μ.real (box n (c * s⁻¹)) : ℂ) * f 0) x := by
    intro x
    by_cases hx : x ∈ box n s
    · have := hs x hx 0
      rw [zero_add] at this
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, this, mul_comm]
    · simp [Set.indicator_of_notMem hx]
  simp only [h3]
  rw [integral_indicator_const _ (isOpen_box _).measurableSet, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul]

theorem vol_mul_vol_dual {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν) (s : kˣ) :
    ν.real (cball s) * ν.real (cball (c * s⁻¹)) = 1 := by
  haveI := hν.1
  haveI := t2Space k
  have hcl : IsClopen (cball (1 : kˣ)) := ⟨(isCompact_cball 1).isClosed, isOpen_cball 1⟩
  have hf : (cball (1 : kˣ)).indicator (fun _ => (1 : ℂ)) ∈ SB k := by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
      HasCompactSupport.intro (isCompact_cball 1) fun y hy => Set.indicator_of_notMem hy _⟩
    by_cases hx : x ∈ cball (1 : kˣ)
    · filter_upwards [hcl.isOpen.mem_nhds hx] with z hz
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hz]
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]
  have h1 := (fourier_inversion ν h hf).symm.trans (hν.2 _ hf)
  rw [Set.indicator_of_mem (by simp [cball]), mul_one] at h1
  have h2 : ν.real (𝒪[k] : Set k) ^ 2 * nabs k c = 1 := by exact_mod_cast h1
  have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
    rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
  rw [measureReal_cball, measureReal_cball, ← h2, h4]; ring

theorem fourier_pi_of_conductor {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧
      ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  refine ⟨fourier_mem_SB _ h hf, ?_⟩
  obtain ⟨s, hs⟩ := fourier_inversion_pi (Measure.pi fun _ : n => ν) h hf
  have hb : ∀ r : kˣ, (Measure.pi fun _ : n => ν).real (box n r) = ν.real (cball r) ^ Fintype.card n := by
    intro r
    simp [Measure.real, box, Measure.pi_pi]
  rw [hs, hb, hb, ← mul_pow, vol_mul_vol_dual h hν]
  simp

theorem fourier_pi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), ∀ f ∈ SB (n → k), (fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∈ SB (n → k) ∧ ∫ y : n → k, (∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0 := by
  intro k _ _ _ _ _ _ n _ _ ψ hc h1 ν hν f hf
  obtain ⟨c, h⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψ hc h1
  exact fourier_pi_of_conductor h hν hf

end GlobalTheory.SplitWeil.FourierPi
