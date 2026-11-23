import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.FilGrowth

def wtSpan {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (R : ℝ) : Submodule ℂ V :=
  Submodule.span ℂ {z | ∃ ν : Fin n → ℝ, IsWeight E ν z ∧ ∀ a, |ν a| ≤ R}

section Alg
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V}

theorem isWeight_step (hE : GlRel E) {ν : Fin n → ℝ} {z : V} (hz : IsWeight E ν z) (a b : Fin n) :
    IsWeight E (fun c => ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) (E a b z) := by
  intro c
  have h := congrArg (fun T : Module.End ℂ V => T z) (hE c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hz c, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  by_cases h1 : c = a
  · subst h1
    by_cases h2 : b = c
    · subst h2; simp
    · have h3 : ¬ c = b := fun h => h2 h.symm
      simp [h2, h3, add_smul, add_comm]
  · by_cases h2 : b = c
    · subst h2
      simp [h1, sub_smul]
      abel
    · have h3 : ¬ c = b := fun h => h2 h.symm
      simp [h1, h2, h3]

theorem exists_isWeight_word (hE : GlRel E) {ν : Fin n → ℝ} {z : V} (hz : IsWeight E ν z)
    (w : List (Fin n × Fin n)) : ∃ ν' : Fin n → ℝ, IsWeight E ν' (ew E w z) := by
  induction w with
  | nil => exact ⟨ν, by simpa [ew] using hz⟩
  | cons p w ih =>
    obtain ⟨ν', h⟩ := ih
    exact ⟨_, by simpa [ew] using isWeight_step hE h p.1 p.2⟩

theorem wtSpan_mono {R R' : ℝ} (h : R ≤ R') : wtSpan E R ≤ wtSpan E R' :=
  Submodule.span_mono fun _ ⟨ν, h1, h2⟩ => ⟨ν, h1, fun a => (h2 a).trans h⟩

theorem step_mem_wtSpan (hE : GlRel E) {R : ℝ} (a b : Fin n) {z : V} (hz : z ∈ wtSpan E R) :
    E a b z ∈ wtSpan E (R + 1) := by
  have : wtSpan E R ≤ (wtSpan E (R + 1)).comap (E a b) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨ν, h1, h2⟩
    refine Submodule.subset_span ⟨_, isWeight_step hE h1 a b, fun c => ?_⟩
    have := abs_le.1 (h2 c)
    rw [abs_le]
    split_ifs <;> constructor <;> linarith [this.1, this.2]
  exact this hz

theorem word_mem_wtSpan (hE : GlRel E) {R : ℝ} (w : List (Fin n × Fin n)) {z : V}
    (hz : z ∈ wtSpan E R) : ew E w z ∈ wtSpan E (R + w.length) := by
  induction w with
  | nil => simpa [ew] using hz
  | cons p w ih =>
    have := step_mem_wtSpan hE p.1 p.2 ih
    simpa [ew, add_assoc] using this

end Alg

section Inner
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ V}

theorem weight_le_of_mem_wtSpan (hU : KUnit ε E) {R : ℝ} {μ : Fin n → ℝ} {y : V}
    (hy : y ∈ wtSpan E R) (hy0 : y ≠ 0) (hμ : IsWeight E μ y) (a : Fin n) : |μ a| ≤ R := by
  by_contra hlt
  have : wtSpan E R ≤ LinearMap.ker (innerₛₗ ℂ y) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨ν, h1, h2⟩
    have hne : μ ≠ ν := by
      rintro rfl
      exact hlt (h2 a)
    exact kWtOrth V n ε E μ ν y z hU hμ h1 hne
  have h0 : ⟪y, y⟫_ℂ = 0 := this hy
  exact hy0 (inner_self_eq_zero.1 h0)

theorem kSpan_le_wtSpan (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {u : V}
    (hu : KHighest ε E μ u) : kSpan ε E u ≤ wtSpan E (Real.sqrt (ckv ε μ)) := by
  have hl := (kLow V n ε E μ u (glRel_kRel ε E hE) hu).1
  rw [hl]
  refine Submodule.span_le.2 ?_
  rintro y ⟨w, hw, rfl⟩
  have hmem : ew E w u ∈ kSpan ε E u := by
    rw [hl]; exact Submodule.subset_span ⟨w, hw, rfl⟩
  by_cases h0 : ew E w u = 0
  · rw [h0]; exact Submodule.zero_mem _
  obtain ⟨ν, hν⟩ := exists_isWeight_word hE hu.1 w
  have hb := kWtBound V n ε E μ ν u _ (glRel_kRel ε E hE) hU hu hmem h0 hν
  refine Submodule.subset_span ⟨ν, hν, fun a => ?_⟩
  apply Real.abs_le_sqrt
  refine le_trans ?_ hb
  unfold Formalism.REAL.nsq Formalism.REAL.dot
  rw [sq]
  exact Finset.single_le_sum (f := fun a => ν a * ν a) (fun i _ => mul_self_nonneg _)
    (Finset.mem_univ a)

theorem pfil_le_wtSpan (hE : GlRel E) (hU : KUnit ε E) {μ : Fin n → ℝ} {u : V}
    (hu : KHighest ε E μ u) (j : ℕ) : pfil ε E u j ≤ wtSpan E (Real.sqrt (ckv ε μ) + j) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨w, hw, -, y, hy, rfl⟩
  refine wtSpan_mono ?_ (word_mem_wtSpan hE w (kSpan_le_wtSpan hE hU hu hy))
  have : (w.length : ℝ) ≤ j := by exact_mod_cast hw
  linarith

end Inner

theorem uGrowth : UGrowth := by
  intro V _ _ n ε E μ c u hE hU hu hc hfd j x hx
  have hK := isUnitary_kUnit ε E hU
  obtain ⟨-, -, hst, -, hcyc, -, hfin⟩ := pfilFacts V n ε E u hE
  have hb := kCasBound V n ε E (pfil ε E u j) (Real.sqrt (ckv ε μ) + j) (hfin hfd j)
    (glRel_kRel ε E hE) hK (hst j) (by positivity)
    (fun ν y hy hy0 hν a => weight_le_of_mem_wtSpan hK (pfil_le_wtSpan hE hK hu j hy) hy0 hν a) x hx
  have hcas := casOnCyc V n E c u hE hc x (hcyc j hx)
  have hs := congrArg Complex.re (sumOfSquaresIdentity_holds V n ε E x hU)
  rw [Complex.ofReal_re, LinearMap.sub_apply, hcas, two_smul, LinearMap.add_apply, inner_sub_right,
    inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at hs
  have h2 : ((c : ℂ) * ((‖x‖ : ℂ)) ^ 2).re = c * ‖x‖ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.sub_re, Complex.add_re] at hs
  have h3 : ((c : ℂ) * (RCLike.ofReal ‖x‖ : ℂ) ^ 2).re = c * ‖x‖ ^ 2 := h2
  rw [h3] at hs
  rw [hs]
  have h4 : -c * ‖x‖ ^ 2 ≤ |c| * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (neg_le_abs c) (by positivity)
  linarith

end GlobalTheory.FilGrowth
