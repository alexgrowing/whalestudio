import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ContDiff

namespace GlobalTheory.JSW

def schur (n : ℕ) (l : Fin n → ℕ) : MvPolynomial (Fin n) ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n =>
    if ((l i : ℤ) - i + j) < 0 then 0 else MvPolynomial.hsymm (Fin n) ℤ (((l i : ℤ) - i + j).toNat))

def schurAt {n : ℕ} (l : Fin n → ℕ) (α : Fin n → ℂ) : ℂ := MvPolynomial.eval₂ (Int.castRingHom ℂ) α (schur n l)

def sphW (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (l : Fin n → ℕ) : ℂ :=
  if Antitone l then
    (q : ℂ) ^ (-(∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (l i : ℂ))) / 2) * schurAt l α
  else 0

theorem schur_zero (n : ℕ) : schur n (fun _ => 0) = 1 := by
  rw [schur, Matrix.det_of_upperTriangular]
  · simp
  · intro i j h
    have h' : (j : ℕ) < i := h
    rw [Matrix.of_apply, if_pos (by push_cast; omega)]

theorem sphW_of_not_antitone (q : ℕ) {n : ℕ} (α : Fin n → ℂ) {l : Fin n → ℕ} (h : ¬ Antitone l) : sphW q α l = 0 :=
  if_neg h

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open GlobalTheory.CuspRep

omit [IsTotallyComplex E] in

instance isAddHaarMeasure_volume_lie : Measure.IsAddHaarMeasure (volume : Measure (Lie E a)) :=
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin a → Cinf E)) := Measure.pi.isAddHaarMeasure _
  Measure.pi.isAddHaarMeasure _

def smoothInf (f : Lie E a → ℂ) (φ : GA E a → ℂ) (g : GA E a) : ℂ := ∫ x, f x * chart φ g x

def IsTestInf (f : Lie E a → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E a

def smoothSpan (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (f : Lie E a → ℂ) (φ : Sm E a), IsTestInf f ∧ φ ∈ π.V ∧ F = smoothInf f φ.1}

omit [IsTotallyComplex E] in

theorem IsTestInf.mul {f h : Lie E a → ℂ} (hf : IsTestInf f) (hh : ContDiffOn ℝ ∞ h (invSet E a)) :
    IsTestInf fun x => f x * h x := by
  have hs : tsupport (fun x => f x * h x) ⊆ tsupport f := tsupport_mul_subset_left
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hf.2.1.mul_right, hs.trans hf.2.2⟩
  by_cases hx : x ∈ tsupport f
  · exact hf.1.contDiffAt.mul (hh.contDiffAt (isOpen_invSet.mem_nhds (hf.2.2 hx)))
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
    simp [hy]

omit [IsTotallyComplex E] in

theorem exists_isTestInf {y : Lie E a} (hy : y ∈ invSet E a) {U : Set (Lie E a)} (hU : U ∈ nhds y) :
    ∃ ρ : Lie E a → ℝ, IsTestInf (fun x => (ρ x : ℂ)) ∧ tsupport ρ ⊆ U ∧ (∀ x, ρ x ∈ Set.Icc (0 : ℝ) 1) ∧ ρ y = 1 := by
  obtain ⟨f, h1, h2, h3, h4, h5⟩ := exists_contDiff_tsupport_subset (n := ⊤) (s := invSet E a ∩ U) (x := y)
    (Filter.inter_mem (isOpen_invSet.mem_nhds hy) hU)
  refine ⟨f, ⟨Complex.ofRealCLM.contDiff.comp h3, h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp), ?_⟩,
    h1.trans Set.inter_subset_right, fun x => h4 ⟨x, rfl⟩, h5⟩
  exact (tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) f).trans (h1.trans Set.inter_subset_left)

theorem IsTestInf.integrable {f : Lie E a → ℂ} (hf : IsTestInf f) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) :
    Integrable fun x => f x * chart φ g x :=
  (hf.mul (hφ g)).1.continuous.integrable_of_hasCompactSupport (hf.mul (hφ g)).2.1

theorem smoothInf_smul (f : Lie E a → ℂ) (c : ℂ) (φ : GA E a → ℂ) : smoothInf f (c • φ) = c • smoothInf f φ := by
  funext g
  rw [Pi.smul_apply, smoothInf, smoothInf, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext x
  by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h, mul_left_comm]

theorem smoothInf_left (f : Lie E a → ℂ) (φ : GA E a → ℂ) (γ g : GA E a) :
    smoothInf f (fun x => φ (γ * x)) g = smoothInf f φ (γ * g) := by
  simp only [smoothInf, chart, mul_assoc]

theorem smoothInf_rt_fin (f : Lie E a → ℂ) (φ : GA E a → ℂ) (k : GL (Fin a) (Af E)) (g : GA E a) :
    smoothInf f (fun x => φ (x * finGL E a k)) g = smoothInf f φ (g * finGL E a k) := by
  simp only [smoothInf, chart_rt_fin]

theorem smoothInf_mem_smoothSpan (π : CuspSub E a) {f : Lie E a → ℂ} (hf : IsTestInf f) {φ : Sm E a} (hφ : φ ∈ π.V) :
    smoothInf f φ.1 ∈ smoothSpan π :=
  Submodule.subset_span ⟨f, φ, hf, hφ, rfl⟩

theorem exists_smoothInf_ne_zero {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) {g : GA E a} (hg : φ g ≠ 0) :
    ∃ f : Lie E a → ℂ, IsTestInf f ∧ smoothInf f φ g ≠ 0 := by
  obtain ⟨ρ, h1, -, h2, h3⟩ := exists_isTestInf (E := E) (a := a) (y := oneL E a) isUnit_one Filter.univ_mem
  have hc : ContDiffOn ℝ ∞ (fun x => starRingEnd ℂ (chart φ g x)) (invSet E a) :=
    Complex.conjCLE.contDiff.comp_contDiffOn (hφ g)
  have hf := h1.mul hc
  refine ⟨_, hf, ?_⟩
  have hF := hf.mul (hφ g)
  have e : (fun x => (ρ x : ℂ) * starRingEnd ℂ (chart φ g x) * chart φ g x) =
      fun x => ((ρ x * Complex.normSq (chart φ g x) : ℝ) : ℂ) := by
    funext x
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_mul]
  rw [smoothInf, e, integral_complex_ofReal, Complex.ofReal_ne_zero]
  rw [e] at hF
  have hcont : Continuous fun x => ρ x * Complex.normSq (chart φ g x) := Complex.continuous_re.comp hF.1.continuous
  have hsupp : HasCompactSupport fun x => ρ x * Complex.normSq (chart φ g x) :=
    hF.2.1.comp_left (g := Complex.re) rfl
  have h4 : chart φ g (oneL E a) = φ g := (chart_val φ g 1).trans (by simp)
  refine (hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp
    (fun x => mul_nonneg (h2 x).1 (Complex.normSq_nonneg _)) (x := oneL E a) ?_).ne'
  simpa [h3, h4] using hg

theorem smoothSpan_ne_bot (π : CuspSub E a) : smoothSpan π ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  obtain ⟨f, hf, h⟩ := exists_smoothInf_ne_zero φ.2 hg
  intro hb
  have := smoothInf_mem_smoothSpan π hf hφ
  rw [hb, Submodule.mem_bot] at this
  exact h (congrFun this g)

example : schur 1 (fun _ => 0) = 1 := schur_zero 1

example : schur 2 ![1, 0] = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  simp [schur, Matrix.det_fin_two, MvPolynomial.hsymm_one]

example (q : ℕ) (α : Fin 2 → ℂ) : sphW q α ![1, 0] = (q : ℂ) ^ (-1 / 2 : ℂ) * (α 0 + α 1) := by
  have h : Antitone (![1, 0] : Fin 2 → ℕ) := by decide
  have e : schur 2 ![1, 0] = MvPolynomial.X 0 + MvPolynomial.X 1 := by
    simp [schur, Matrix.det_fin_two, MvPolynomial.hsymm_one]
  rw [sphW, if_pos h, schurAt, e]
  congr 1
  · congr 1
    simp
    norm_num
  · simp

example : ∃ f : Lie E a → ℂ, IsTestInf f ∧ f (oneL E a) = 1 := by
  obtain ⟨ρ, h1, -, -, h3⟩ := exists_isTestInf (E := E) (a := a) (y := oneL E a) isUnit_one Filter.univ_mem
  exact ⟨_, h1, by simp [h3]⟩

end GlobalTheory.JSW
