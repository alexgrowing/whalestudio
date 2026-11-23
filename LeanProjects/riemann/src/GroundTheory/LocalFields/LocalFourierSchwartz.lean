import Mathlib
import GroundTheory.LocalFields.LocalFourierChar

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section SchwartzBruhat

variable (K) in

def schwartzBruhat : Submodule ℂ (K → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.smul_left (f := fun _ => c)⟩

omit [Field K] [ValuativeRel K] [IsNonarchimedeanLocalField K] in
theorem mem_schwartzBruhat {f : K → ℂ} :
    f ∈ schwartzBruhat K ↔ IsLocallyConstant f ∧ HasCompactSupport f := Iff.rfl

theorem isLocallyConstant_of_add_valBall {g : K → ℂ} {N : ℤ}
    (hg : ∀ x, ∀ h ∈ valBall K N, g (x + h) = g x) : IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨{z | z - x ∈ valBall K N},
    (isOpen_valBall N).preimage (continuous_id.sub continuous_const), by simp, fun z hz => ?_⟩
  have := hg x (z - x) hz
  rwa [add_sub_cancel] at this

theorem exists_invariant_of_mem_schwartzBruhat {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    ∃ N M : ℤ, (∀ x, ∀ h ∈ valBall K N, f (x + h) = f x) ∧ ∀ x, f x ≠ 0 → x ∈ valBall K M := by
  obtain ⟨hlc, hcs⟩ := hf
  obtain ⟨m, hm⟩ : ∃ m : ℕ, tsupport f ⊆ (valBall K (-(m : ℤ)) : Set K) := by
    refine hcs.isCompact.elim_directed_cover (fun m : ℕ => (valBall K (-(m : ℤ)) : Set K))
      (fun m => isOpen_valBall _) ?_ ?_
    · intro x _
      simp only [Set.mem_iUnion]
      exact exists_mem_valBall_neg_nat x
    · exact Monotone.directed_le fun a b hab => valBall_antitone (by omega)
  have hloc : ∀ x : K, ∃ n : ℤ, ∀ h ∈ valBall K n, f (x + h) = f x := by
    intro x
    have ho : IsOpen {h : K | f (x + h) = f x} :=
      (hlc.isOpen_fiber (f x)).preimage (continuous_const.add continuous_id)
    obtain ⟨n, -, hn⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp (ho.mem_nhds (by simp))
    exact ⟨n, fun h hh => hn hh⟩
  choose n hn using hloc
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x => {z : K | z - x ∈ valBall K (n x)})
    (fun x _ => ((isOpen_valBall _).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp))
  obtain ⟨N, hN⟩ := (t.image n).exists_le
  have hval : ∀ y ∈ tsupport f, ∀ h ∈ valBall K N, f (y + h) = f y := by
    intro y hy h hh
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hyx⟩ := this
    have hN' : valBall K N ≤ valBall K (n x) :=
      valBall_antitone (hN _ (Finset.mem_image_of_mem n hxt))
    have e1 : f y = f x := by
      have := hn x (y - x) hyx
      rwa [add_sub_cancel] at this
    have e2 : f (y + h) = f x := by
      have := hn x (y + h - x)
        (by rw [show y + h - x = (y - x) + h by ring]; exact add_mem hyx (hN' hh))
      rwa [add_sub_cancel] at this
    rw [e1, e2]
  refine ⟨N, -(m : ℤ), fun y h hh => ?_, fun x hx => hm (subset_tsupport f hx)⟩
  by_cases hy : y ∈ tsupport f
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport f
  · have := hval (y + h) hyh (-h) (neg_mem hh)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

end SchwartzBruhat

theorem eq_zero_of_eq_mul_of_ne_one {a c : ℂ} (ha : a ≠ 1) (h : c = a * c) : c = 0 := by
  have : (1 - a) * c = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))

section Fourier

variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]

open scoped Classical in

theorem integral_valBall_char (χ : AddChar K Circle) (k : ℤ) :
    ∫ x in valBall K k, (χ x : ℂ) ∂μ =
      if IsTrivialOn χ k then (μ.real (valBall K k) : ℂ) else 0 := by
  classical
  split_ifs with h
  · have e : ∀ x ∈ (valBall K k : Set K), (χ x : ℂ) = 1 := fun x hx => by simp [h x hx]
    rw [setIntegral_congr_fun (measurableSet_valBall k) e, setIntegral_const, Complex.real_smul,
      mul_one]
  · obtain ⟨h₀, hh₀, hne⟩ : ∃ h₀ ∈ valBall K k, χ h₀ ≠ 1 := by simpa [IsTrivialOn] using h
    let g : K → ℂ := (valBall K k : Set K).indicator fun x => (χ x : ℂ)
    have hg : ∀ x, g (h₀ + x) = (χ h₀ : ℂ) * g x := by
      intro x
      have hiff : h₀ + x ∈ valBall K k ↔ x ∈ valBall K k :=
        ⟨fun h' => by simpa using sub_mem h' hh₀, fun h' => add_mem hh₀ h'⟩
      by_cases hx : x ∈ valBall K k
      · simp [g, Set.indicator_of_mem (show x ∈ (valBall K k : Set K) from hx),
          Set.indicator_of_mem (show h₀ + x ∈ (valBall K k : Set K) from hiff.mpr hx),
          AddChar.map_add_eq_mul]
      · simp [g, Set.indicator_of_notMem (show x ∉ (valBall K k : Set K) from hx),
          Set.indicator_of_notMem (show h₀ + x ∉ (valBall K k : Set K) from mt hiff.mp hx)]
    have key : ∫ x in valBall K k, (χ x : ℂ) ∂μ = (χ h₀ : ℂ) * ∫ x in valBall K k, (χ x : ℂ) ∂μ :=
      calc ∫ x in valBall K k, (χ x : ℂ) ∂μ = ∫ x, g x ∂μ :=
            (integral_indicator (measurableSet_valBall k)).symm
        _ = ∫ x, g (h₀ + x) ∂μ := (integral_add_left_eq_self g h₀).symm
        _ = ∫ x, (χ h₀ : ℂ) * g x ∂μ := by simp only [hg]
        _ = (χ h₀ : ℂ) * ∫ x in valBall K k, (χ x : ℂ) ∂μ := by
            rw [integral_const_mul, integral_indicator (measurableSet_valBall k)]
    exact eq_zero_of_eq_mul_of_ne_one (fun h' => hne (Circle.coe_eq_one.mp h')) key

variable (ψ : AddChar K Circle)

def localFourier (f : K → ℂ) (y : K) : ℂ := ∫ x, f x * (ψ (x * y) : ℂ) ∂μ

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in
theorem integrable_of_mem_schwartzBruhat {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    Integrable f μ :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

omit hψ1 in
theorem integrable_mul_char_of_mem_schwartzBruhat {f : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (y : K) : Integrable (fun x => f x * (ψ (x * y) : ℂ)) μ :=
  (hf.1.continuous.mul ((continuous_subtype_val.comp hψ).comp
    (continuous_id.mul continuous_const))).integrable_of_hasCompactSupport hf.2.mul_right

theorem localFourier_eq_zero_of_notMem {f : K → ℂ} {N : ℤ}
    (hfN : ∀ x, ∀ h ∈ valBall K N, f (x + h) = f x) {y : K}
    (hy : y ∉ valBall K (addCharConductor ψ - N)) : localFourier μ ψ f y = 0 := by
  rw [← isTrivialOn_mulShift_iff_mem hψ hψ1] at hy
  obtain ⟨h, hh, hne⟩ : ∃ h ∈ valBall K N, ψ (y * h) ≠ 1 := by
    simpa [IsTrivialOn, AddChar.mulShift_apply] using hy
  have key : localFourier μ ψ f y = (ψ (h * y) : ℂ) * localFourier μ ψ f y :=
    calc ∫ x, f x * (ψ (x * y) : ℂ) ∂μ = ∫ x, f (h + x) * (ψ ((h + x) * y) : ℂ) ∂μ :=
          (integral_add_left_eq_self (fun x => f x * (ψ (x * y) : ℂ)) h).symm
      _ = ∫ x, (ψ (h * y) : ℂ) * (f x * (ψ (x * y) : ℂ)) ∂μ := by
          congr 1
          ext x
          rw [add_comm h x, hfN x h hh, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
          ring
      _ = (ψ (h * y) : ℂ) * localFourier μ ψ f y := integral_const_mul _ _
  refine eq_zero_of_eq_mul_of_ne_one (fun h' => hne ?_) key
  rw [mul_comm]
  exact Circle.coe_eq_one.mp h'

omit [BorelSpace K] [μ.IsAddHaarMeasure] in

theorem localFourier_add_eq {f : K → ℂ} {M : ℤ} (hfM : ∀ x, f x ≠ 0 → x ∈ valBall K M) (y : K)
    {h : K} (hh : h ∈ valBall K (addCharConductor ψ - M)) :
    localFourier μ ψ f (y + h) = localFourier μ ψ f y := by
  unfold localFourier
  congr 1
  ext x
  by_cases hx : f x = 0
  · simp [hx]
  have : ψ (x * h) = 1 := isTrivialOn_addCharConductor hψ hψ1 _ (by
    have := mul_mem_valBall (hfM x hx) hh
    rwa [add_sub_cancel] at this)
  rw [mul_add, AddChar.map_add_eq_mul, this, mul_one]

theorem localFourier_mem_schwartzBruhat {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    localFourier μ ψ f ∈ schwartzBruhat K := by
  obtain ⟨N, M, hN, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  refine ⟨isLocallyConstant_of_add_valBall (N := addCharConductor ψ - M)
    fun y h hh => localFourier_add_eq μ hψ hψ1 hM y hh, ?_⟩
  exact HasCompactSupport.intro (isCompact_valBall (addCharConductor ψ - N))
    fun y hy => localFourier_eq_zero_of_notMem μ hψ hψ1 hN hy

theorem localFourier_localFourier {f : K → ℂ} (hf : f ∈ schwartzBruhat K) (z : K) :
    localFourier μ ψ (localFourier μ ψ f) z =
      (((residueCard K : ℝ) ^ (-addCharConductor ψ) * μ.real (valBall K 0) ^ 2 : ℝ) : ℂ) * f (-z) := by
  obtain ⟨N, M, hN, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  have hfi : Integrable f μ := integrable_of_mem_schwartzBruhat μ hf
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  let B : Set K := valBall K (addCharConductor ψ - N)
  have hBm : MeasurableSet B := measurableSet_valBall _
  have : IsFiniteMeasure (μ.restrict B) :=
    isFiniteMeasure_restrict.mpr (isCompact_valBall _).measure_lt_top.ne

  have hA : localFourier μ ψ (localFourier μ ψ f) z =
      ∫ y in B, localFourier μ ψ f y * (ψ (y * z) : ℂ) ∂μ := by
    rw [show localFourier μ ψ (localFourier μ ψ f) z =
      ∫ y, localFourier μ ψ f y * (ψ (y * z) : ℂ) ∂μ from rfl]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [localFourier_eq_zero_of_notMem μ hψ hψ1 hN hy, zero_mul]).symm

  let G : K → K → ℂ := fun y x => f x * (ψ (x * y) : ℂ) * (ψ (y * z) : ℂ)
  have hG : Integrable (Function.uncurry G) ((μ.restrict B).prod μ) := by
    have hdom : Integrable (fun p : K × K => (1 : ℝ) * ‖f p.2‖) ((μ.restrict B).prod μ) :=
      (integrable_const (1 : ℝ)).mul_prod hfi.norm
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hf.1.continuous.comp continuous_snd).mul
        (hψc.comp (continuous_snd.mul continuous_fst))).mul
        (hψc.comp (continuous_fst.mul continuous_const))
    · simp [G, Function.uncurry, Circle.norm_coe]
  have hB : ∫ y in B, localFourier μ ψ f y * (ψ (y * z) : ℂ) ∂μ =
      ∫ y in B, ∫ x, G y x ∂μ ∂μ := by
    congr 1
    ext y
    exact (integral_mul_const _ _).symm

  have hinner : ∀ x, ∫ y in B, G y x ∂μ =
      (valBall K N : Set K).indicator (fun _ => f (-z) * (μ.real B : ℂ)) (x + z) := by
    intro x
    have e : ∀ y, G y x = f x * ((ψ.mulShift (x + z)) y : ℂ) := fun y => by
      simp only [G, AddChar.mulShift_apply]
      rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3
      ring
    simp only [e]
    rw [integral_const_mul, integral_valBall_char]
    by_cases hxz : x + z ∈ valBall K N
    · have ht : IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - N) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_pos ht, Set.indicator_of_mem (show x + z ∈ (valBall K N : Set K) from hxz)]
      have : f x = f (-z) := by
        have := hN (-z) (x + z) hxz
        rw [show -z + (x + z) = x by ring] at this
        exact this
      rw [this]
    · have ht : ¬ IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - N) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_neg ht, Set.indicator_of_notMem (show x + z ∉ (valBall K N : Set K) from hxz),
        mul_zero]
  rw [hA, hB, integral_integral_swap hG]
  simp only [hinner]
  have hpre : ∫ x, (valBall K N : Set K).indicator (fun _ => f (-z) * (μ.real B : ℂ)) (x + z) ∂μ =
      ∫ x, (valBall K N : Set K).indicator (fun _ => f (-z) * (μ.real B : ℂ)) x ∂μ :=
    integral_add_right_eq_self (fun x => (valBall K N : Set K).indicator
      (fun _ => f (-z) * (μ.real B : ℂ)) x) z
  rw [hpre, integral_indicator_const _ (measurableSet_valBall N), Complex.real_smul]
  simp only [B]
  rw [measureReal_valBall μ N, measureReal_valBall μ (addCharConductor ψ - N)]
  have hq : (residueCard K : ℝ) ≠ 0 := by exact_mod_cast residueCard_ne_zero
  have : (residueCard K : ℝ) ^ (-addCharConductor ψ) =
      (residueCard K : ℝ) ^ (-N) * (residueCard K : ℝ) ^ (-(addCharConductor ψ - N)) := by
    rw [← zpow_add₀ hq]
    ring_nf
  rw [this]
  push_cast
  ring

end Fourier

end GroundTheory.LocalField
