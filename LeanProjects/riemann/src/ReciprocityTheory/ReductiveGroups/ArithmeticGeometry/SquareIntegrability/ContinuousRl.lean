import Mathlib

open MeasureTheory Set Complex

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.I2.DimB

variable {k : ℕ}

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def rl (t : Fin k → ℝ) : Fin k → ℂ := fun i => (t i : ℂ)

def iz (n : Fin k → ℤ) : Fin k → ℂ := fun i => (n i : ℂ)

def ubox (k : ℕ) : Set (Fin k → ℝ) :=
  {x | ∀ i, x i ∈ Ioc ((0 : Fin k → ℝ) i) ((0 : Fin k → ℝ) i + 1)}

def tproj (t : Fin k → ℝ) : UnitAddTorus (Fin k) := fun i => (t i : UnitAddCircle)

theorem tproj_oqm : IsOpenQuotientMap (tproj (k := k)) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

theorem tproj_add (s t : Fin k → ℝ) : tproj (s + t) = tproj s + tproj t := by
  funext i; simp [tproj]

theorem tproj_eq {s t : Fin k → ℝ} (h : tproj s = tproj t) :
    ∃ n : Fin k → ℤ, t = s + fun i => (n i : ℝ) := by
  have hi : ∀ i, ∃ m : ℤ, t i = s i + m := by
    intro i
    have h1 : ((s i : ℝ) : UnitAddCircle) = (t i : UnitAddCircle) := congrFun h i
    have h2 : (((t i - s i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h2
    refine ⟨m, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hm
    linarith
  choose n hn using hi
  exact ⟨n, funext fun i => by simp [hn i]⟩

theorem descend (φ : (Fin k → ℝ) → ℂ) (hφ : Continuous φ)
    (hp : ∀ (n : Fin k → ℤ) t, φ (t + fun i => (n i : ℝ)) = φ t) :
    ∃ D : C(UnitAddTorus (Fin k), ℂ), ∀ t, D (tproj t) = φ t := by
  let D0 : UnitAddTorus (Fin k) → ℂ := fun θ => φ (Function.surjInv tproj_oqm.surjective θ)
  have hD : ∀ t, D0 (tproj t) = φ t := by
    intro t
    obtain ⟨n, hn⟩ := tproj_eq (Function.surjInv_eq tproj_oqm.surjective (tproj t))
    have e := hp n (Function.surjInv tproj_oqm.surjective (tproj t))
    rw [← hn] at e
    exact e.symm
  refine ⟨⟨D0, ?_⟩, hD⟩
  rw [tproj_oqm.isQuotientMap.continuous_iff]
  have : D0 ∘ tproj = φ := funext hD
  rw [this]; exact hφ

theorem box_shift (φ : (Fin k → ℝ) → ℂ) (hφ : Continuous φ)
    (hp : ∀ (n : Fin k → ℤ) t, φ (t + fun i => (n i : ℝ)) = φ t) (s : Fin k → ℝ) :
    ∫ x in ubox k, φ (x + s) = ∫ x in ubox k, φ x := by
  obtain ⟨D, hD⟩ := descend φ hφ hp
  let D' : C(UnitAddTorus (Fin k), ℂ) := ⟨fun θ => D (θ + tproj s), by fun_prop⟩
  have h1 : ∀ x, φ (x + s) = D' (tproj x) := fun x => by
    rw [← hD, tproj_add]; rfl
  have h2 : ∀ x, φ x = D (tproj x) := fun x => (hD x).symm
  have e0 := UnitAddTorus.integral_preimage (fun θ => D θ) 0
  have es := UnitAddTorus.integral_preimage (fun θ => D θ) s
  have m0 : MeasurableSet (ubox k) := by
    have := MeasurableSet.univ_pi (fun i : Fin k =>
      (measurableSet_Ioc : MeasurableSet (Ioc ((0 : Fin k → ℝ) i) ((0 : Fin k → ℝ) i + 1))))
    convert this using 1; ext x; simp [ubox]
  have ms : MeasurableSet {x : Fin k → ℝ | ∀ i, x i ∈ Ioc (s i) (s i + 1)} := by
    have := MeasurableSet.univ_pi (fun i : Fin k =>
      (measurableSet_Ioc : MeasurableSet (Ioc (s i) (s i + 1))))
    convert this using 1; ext x; simp
  have key : ∫ x in ubox k, φ (x + s) = ∫ x in {x : Fin k → ℝ | ∀ i, x i ∈ Ioc (s i) (s i + 1)}, φ x := by
    rw [← integral_indicator m0, ← integral_indicator ms,
      ← integral_add_right_eq_self (μ := volume)
        (indicator {x : Fin k → ℝ | ∀ i, x i ∈ Ioc (s i) (s i + 1)} φ) s]
    congr 1; funext x
    simp only [indicator, ubox, Pi.zero_apply, zero_add, mem_Ioc]
    congr 1
    apply propext
    refine forall_congr' fun i => ?_
    constructor <;> intro h <;> simp only [Pi.add_apply] at h ⊢ <;> constructor <;> linarith [h.1, h.2]
  rw [key]
  simp_rw [h2]
  exact es.symm.trans e0

theorem mF_tproj (m : Fin k → ℤ) (x : Fin k → ℝ) :
    UnitAddTorus.mFourier m (tproj x) = cexp (2 * Real.pi * I * ∑ l, (m l : ℂ) * (x l : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, tproj, fourier_coe_apply]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp; ring

theorem torus_unique (D : C(UnitAddTorus (Fin k), ℂ))
    (h : ∀ n, UnitAddTorus.mFourierCoeff D n = 0) : D = 0 := by
  have hinj := (UnitAddTorus.mFourierBasis (d := Fin k)).repr.injective
  have h1 := @hinj (ContinuousMap.toLp 2 _ ℂ D) 0 (by
    rw [map_zero]
    refine lp.ext (funext fun n => ?_)
    rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierCoeff_toLp, h]
    rfl)
  exact ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (E := ℂ) _ (h1.trans (map_zero _).symm)

theorem shift_sum {G β ι : Type*} [AddCommMonoid G] (Φ : G → β) (a : ι → G)
    (h : ∀ l v, Φ (v + a l) = Φ v) (S : Finset ι) (v : G) : Φ (v + ∑ l ∈ S, a l) = Φ v := by
  classical
  induction S using Finset.induction_on generalizing v with
  | empty => simp
  | insert b S hb ih => rw [Finset.sum_insert hb, ← add_assoc, ih, h]

theorem shift_int {G β : Type*} [AddCommGroup G] (Φ : G → β) (e : G) (h : ∀ v, Φ (v + e) = Φ v)
    (c : ℤ) (v : G) : Φ (v + c • e) = Φ v := by
  induction c using Int.induction_on generalizing v with
  | zero => simp
  | succ n ih => rw [add_smul, one_smul, ← add_assoc, h, ih]
  | pred n ih =>
    rw [← ih v, ← h (v + (-(n : ℤ) - 1) • e)]
    congr 1
    rw [sub_smul, one_smul, neg_smul]; abel

def IPer (Ψ : (Fin k → ℂ) → ℂ) : Prop := ∀ (n : Fin k → ℤ) z, Ψ (z + iz n) = Ψ z

theorem iper_of_unit (Ψ : (Fin k → ℂ) → ℂ) (h : ∀ l z, Ψ (z + Pi.single l 1) = Ψ z) : IPer Ψ := by
  intro n z
  have hn : iz n = ∑ l, (n l) • (Pi.single l 1 : Fin k → ℂ) := by
    funext i; simp [iz, Finset.sum_apply, Pi.single_apply]
  rw [hn]
  exact shift_sum Ψ _ (fun l v => shift_int Ψ _ (h l) (n l) v) _ z

theorem rl_add (s t : Fin k → ℝ) : rl (s + t) = rl s + rl t := by funext i; simp [rl]

theorem continuous_rl : Continuous (rl (k := k)) :=
  continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)

def Av (Ψ : (Fin k → ℂ) → ℂ) (w : Fin k → ℂ) : ℂ := ∫ x in ubox k, Ψ (rl x + w)

theorem Av_real (Ψ : (Fin k → ℂ) → ℂ) (hc : Continuous Ψ) (hp : IPer Ψ) (w : Fin k → ℂ)
    (s : Fin k → ℝ) : Av Ψ (w + rl s) = Av Ψ w := by
  have e : ∀ x, rl x + (w + rl s) = rl (x + s) + w := fun x => by rw [rl_add]; abel
  unfold Av
  simp_rw [e]
  refine box_shift (fun x => Ψ (rl x + w)) (hc.comp (continuous_rl.add continuous_const))
    (fun n t => ?_) s
  have : rl (t + fun i => (n i : ℝ)) + w = (rl t + w) + iz n := by
    rw [rl_add]; have : rl (fun i => (n i : ℝ)) = iz n := by funext i; simp [rl, iz]
    rw [this]; abel
  simp only [this, hp n]

theorem line_cauchy (Ψ : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ Ψ) (l : Fin k)
    (hp1 : ∀ z, Ψ (z + Pi.single l 1) = Ψ z) (u : Fin k → ℂ) (y : ℝ) :
    ∫ x in (0:ℝ)..1, Ψ (u + (x : ℂ) • Pi.single l 1) =
      ∫ x in (0:ℝ)..1, Ψ (u + ((y : ℂ) * I) • Pi.single l 1 + (x : ℂ) • Pi.single l 1) := by
  set f : ℂ → ℂ := fun c => Ψ (u + c • Pi.single l 1) with hf
  have hfd : Differentiable ℂ f :=
    hd.comp ((differentiable_const u).add (differentiable_id.smul_const _))
  have hper : ∀ c, f (c + 1) = f c := fun c => by
    simp only [hf, add_smul, one_smul, ← add_assoc, hp1]
  have H := integral_boundary_rect_eq_zero_of_differentiableOn f 0 (1 + y * I) hfd.differentiableOn
  have hre : (1 + (y : ℂ) * I).re = 1 := by simp
  have him : (1 + (y : ℂ) * I).im = y := by simp
  simp only [Complex.zero_re, Complex.zero_im, hre, him, Complex.ofReal_zero, zero_mul, add_zero,
    Complex.ofReal_one, zero_add] at H
  have h3 : (∫ t in (0:ℝ)..y, f (1 + (t : ℂ) * I)) = ∫ t in (0:ℝ)..y, f ((t : ℂ) * I) := by
    congr 1; funext t; rw [add_comm, hper]
  rw [h3] at H
  have H2 : (∫ x in (0:ℝ)..1, f (x : ℂ)) = ∫ x in (0:ℝ)..1, f ((x : ℂ) + y * I) := by
    linear_combination H
  have e1 : ∀ x : ℝ, u + ((y : ℂ) * I) • Pi.single l 1 + (x : ℂ) • Pi.single l 1 =
      u + ((x : ℂ) + y * I) • (Pi.single l 1 : Fin k → ℂ) := fun x => by
    rw [add_smul]; abel
  simp_rw [e1]
  exact H2

theorem ubox_sub_Icc : ubox k ⊆ Icc (0 : Fin k → ℝ) 1 := by
  intro x hx
  exact ⟨fun i => by have := (hx i).1; simp at this; exact this.le,
    fun i => by have := (hx i).2; simpa using this⟩

theorem Av_line (Ψ : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ Ψ) (hp : IPer Ψ) (w : Fin k → ℂ)
    (l : Fin k) (y : ℝ) : Av Ψ (w + ((y : ℂ) * I) • Pi.single l 1) = Av Ψ w := by
  have hc := hd.continuous
  have hp1 : ∀ z, Ψ (z + Pi.single l 1) = Ψ z := fun z => by
    have := hp (Pi.single l 1) z
    have e : iz (Pi.single l (1 : ℤ)) = (Pi.single l 1 : Fin k → ℂ) := by
      funext i; simp [iz, Pi.single_apply]
    rwa [e] at this
  have avg : ∀ v, Av Ψ v = ∫ t in ubox k, ∫ x in (0:ℝ)..1, Ψ (rl t + v + (x : ℂ) • Pi.single l 1) := by
    intro v
    have e2 : ∀ x : ℝ, rl (Pi.single l x) = (x : ℂ) • (Pi.single l 1 : Fin k → ℂ) := fun x => by
      funext i; simp [rl, Pi.single_apply]; split_ifs <;> simp
    have e1 : Av Ψ v = ∫ x in (0:ℝ)..1, Av Ψ (v + (x : ℂ) • Pi.single l 1) := by
      simp_rw [← e2, Av_real Ψ hc hp]; simp
    rw [e1]
    simp only [Av]
    rw [intervalIntegral.integral_of_le zero_le_one]
    rw [integral_integral_swap]
    · congr 1; funext t; rw [intervalIntegral.integral_of_le zero_le_one]
      congr 1; funext x; rw [add_assoc]
    · rw [Measure.prod_restrict]
      refine (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ?_).mono_set
        (Set.prod_mono Ioc_subset_Icc_self ubox_sub_Icc)
      refine Continuous.continuousOn ?_
      exact hc.comp ((continuous_rl.comp continuous_snd).add
        (continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const)))
  rw [avg, avg]
  congr 1; funext t
  rw [line_cauchy Ψ hd l hp1 (rl t + w) y]
  congr 1; funext x; rw [← add_assoc]

theorem Av_const (Ψ : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ Ψ) (hp : IPer Ψ) (w : Fin k → ℂ) :
    Av Ψ w = Av Ψ 0 := by
  have hdec : w = rl (fun i => (w i).re) + ∑ l, (((w l).im : ℂ) * I) • (Pi.single l 1 : Fin k → ℂ) := by
    funext i; simp [rl, Finset.sum_apply, Pi.single_apply, Complex.re_add_im]
  rw [hdec, shift_sum (Av Ψ) _ (fun l v => Av_line Ψ hd hp v l _)]
  have := Av_real Ψ hd.continuous hp 0 (fun i => (w i).re)
  rwa [zero_add] at this

def ex (m : Fin k → ℤ) (z : Fin k → ℂ) : ℂ := cexp (-(2 * Real.pi * I * ∑ l, (m l : ℂ) * z l))

theorem ex_ne (m : Fin k → ℤ) (z : Fin k → ℂ) : ex m z ≠ 0 := Complex.exp_ne_zero _

theorem ex_add (m : Fin k → ℤ) (z w : Fin k → ℂ) : ex m (z + w) = ex m z * ex m w := by
  simp only [ex, Pi.add_apply, mul_add, Finset.sum_add_distrib, ← Complex.exp_add]; congr 1; ring

theorem ex_iz (m n : Fin k → ℤ) : ex m (iz n) = 1 := by
  simp only [ex, iz]
  have : ∑ l, (m l : ℂ) * (n l : ℂ) = ((∑ l, m l * n l : ℤ) : ℂ) := by push_cast; rfl
  rw [this, show -(2 * Real.pi * I * ((∑ l, m l * n l : ℤ) : ℂ)) =
    ((-(∑ l, m l * n l) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem ex_shift (m : Fin k → ℤ) (q : ℕ) (j : Fin k) (z : Fin k → ℂ) :
    cexp (2 * Real.pi * I * q * z j) * ex m z = ex (m - (q : ℤ) • Pi.single j 1) z := by
  simp only [ex, ← Complex.exp_add]
  congr 1
  have : ∑ l, (((m - (q : ℤ) • (Pi.single j 1 : Fin k → ℤ)) l : ℤ) : ℂ) * z l = ∑ l, (m l : ℂ) * z l - q * z j := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul, sub_mul,
      Finset.sum_sub_distrib]
    congr 1
    simp [Pi.single_apply]
  rw [this]; ring

theorem mF_ex (m : Fin k → ℤ) (x : Fin k → ℝ) :
    UnitAddTorus.mFourier (-m) (tproj x) = ex m (rl x) := by
  rw [mF_tproj, ex]
  congr 1
  simp only [rl, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

def Pm (h : (Fin k → ℂ) → ℂ) (m : Fin k → ℤ) : (Fin k → ℂ) → ℂ := fun z => h z * ex m z

theorem Pm_diff (h : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ h) (m : Fin k → ℤ) :
    Differentiable ℂ (Pm h m) := by
  unfold Pm ex; fun_prop

theorem Pm_per (h : (Fin k → ℂ) → ℂ) (hp : IPer h) (m : Fin k → ℤ) : IPer (Pm h m) :=
  fun n z => by simp only [Pm, ex_add, ex_iz, hp n z, mul_one]

theorem four_zero {q : ℕ} (hq : 0 < q) (h : (Fin k → ℂ) → ℂ) (hd : Differentiable ℂ h)
    (hp1 : ∀ l z, h (z + Pi.single l 1) = h z) (τ : Fin k → Fin k → ℂ) (C : Fin k → ℂ)
    (hqp : ∀ j z, h (z + τ j) = C j * cexp (2 * Real.pi * I * q * z j) * h z)
    (hc : ∀ m : Fin k → ℤ, (∀ l, 0 ≤ m l ∧ m l < q) → Av (Pm h m) 0 = 0) : h = 0 := by
  have hp := iper_of_unit h hp1
  by_cases hC : ∃ j, C j = 0
  · obtain ⟨j, hj⟩ := hC
    funext z
    have := hqp j (z - τ j)
    rw [sub_add_cancel, hj] at this; simpa using this
  push Not at hC
  have hrec : ∀ j m, Av (Pm h m) 0 =
      C j * ex m (τ j) * Av (Pm h (m - (q : ℤ) • Pi.single j 1)) 0 := by
    intro j m
    rw [← Av_const _ (Pm_diff h hd m) (Pm_per h hp m) (τ j)]
    unfold Av
    rw [← integral_const_mul]
    congr 1; funext x
    simp only [Pm, add_zero, ex_add, hqp j, ← ex_shift]; ring
  let P : (Fin k → ℤ) → Prop := fun m => Av (Pm h m) 0 = 0
  have Z : ∀ j m, P (m + (q : ℤ) • (Pi.single j 1 : Fin k → ℤ)) = P m := by
    intro j m
    show (Av (Pm h (m + (q : ℤ) • (Pi.single j 1 : Fin k → ℤ))) 0 = 0) = (Av (Pm h m) 0 = 0)
    rw [hrec j (m + _), add_sub_cancel_right]
    apply propext
    simp [hC j, ex_ne]
  have hall : ∀ m, Av (Pm h m) 0 = 0 := by
    intro m
    have hm : m = (fun l => m l % q) + ∑ l, (m l / q) • ((q : ℤ) • Pi.single l (1 : ℤ)) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
      linear_combination -(Int.emod_add_mul_ediv (m i) q)
    have := shift_sum (G := Fin k → ℤ) (β := Prop) P
      (fun l => (m l / q) • ((q : ℤ) • (Pi.single l 1 : Fin k → ℤ)))
      (fun l v => shift_int (G := Fin k → ℤ) (β := Prop) P _ (Z l) _ v) Finset.univ (fun l => m l % q)
    rw [← hm] at this
    show P m
    rw [this]
    exact hc _ (fun l => ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩)
  have hz : ∀ x y : Fin k → ℝ, h (rl x + fun i => I * (y i : ℂ)) = 0 := by
    intro x y
    set w : Fin k → ℂ := fun i => I * (y i : ℂ)
    obtain ⟨D, hD⟩ := descend (fun x => h (rl x + w))
      (hd.continuous.comp (continuous_rl.add continuous_const)) (fun n t => by
        have e : rl (t + fun i => (n i : ℝ)) + w = (rl t + w) + iz n := by
          funext i; simp [rl, iz]; ring
        simp only [e, hp n])
    have hD0 : D = 0 := torus_unique D (fun m => by
      rw [UnitAddTorus.mFourierCoeff_eq_integral _ m 0]
      have e : ∀ x : Fin k → ℝ, UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) •
          D (fun i => (x i : UnitAddCircle)) = (ex m w)⁻¹ * Pm h m (rl x + w) := by
        intro x
        have h1 := mF_ex m x
        have h2 := hD x
        rw [show (fun i => (x i : UnitAddCircle)) = tproj x from rfl, h1, h2, smul_eq_mul, Pm, ex_add]
        field_simp [ex_ne m w]
      rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul]
      have := hall m
      rw [← Av_const _ (Pm_diff h hd m) (Pm_per h hp m) w] at this
      unfold Av at this
      exact mul_eq_zero_of_right _ this)
    have := hD x
    rw [hD0] at this
    simpa using this.symm
  funext z
  have : z = rl (fun i => (z i).re) + fun i => I * ((z i).im : ℂ) := by
    funext i; simp only [rl, Pi.add_apply]; rw [mul_comm]; exact (re_add_im _).symm
  rw [this]; exact hz _ _

end ReciprocityTheory.ChartRestriction.G.I2.DimB
