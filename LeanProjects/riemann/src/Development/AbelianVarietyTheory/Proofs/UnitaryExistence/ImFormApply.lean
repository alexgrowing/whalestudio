import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslateJetNeZero
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CoeffEqZeroOfOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableFderivApply

namespace GlobalTheory.UpperHalfImaginaryForm

open ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {ι : Type} [Fintype ι]

def imForm : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (Hf x y).im)
    (fun x y z => by simp [Hf, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Hf, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum, smul_eq_mul]
      simp)
    (fun x y z => by simp [Hf, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
        mul_left_comm _ (c : ℂ), ← Finset.mul_sum, smul_eq_mul]
      simp)

theorem imForm_apply (x y : EuclideanSpace ℂ ι) : imForm x y = (Hf x y).im := rfl

theorem imForm_swap (x y : EuclideanSpace ℂ ι) : imForm y x = -imForm x y := by
  have h : Hf y x = starRingEnd ℂ (Hf x y) := by
    simp [Hf, map_sum, mul_comm]
  rw [imForm_apply, imForm_apply, h, Complex.conj_im]

variable {n : ℕ}

def upper (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) :
    EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℝ :=
  b.constr ℝ fun i => b.constr ℝ fun j => if i < j then imForm (b i) (b j) else 0

theorem upper_basis (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) (i j : Fin n) :
    upper b (b i) (b j) = if i < j then imForm (b i) (b j) else 0 := by
  simp only [upper, b.constr_basis]

theorem upper_sub (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) (x y : EuclideanSpace ℂ ι) :
    imForm x y = upper b x y - upper b y x := by
  have key : imForm = upper b - (upper b).flip := by
    refine b.ext fun i => b.ext fun j => ?_
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, upper_basis]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, lt_asymm h]
    · subst h
      have := imForm_swap (b i) (b i)
      simp only [lt_irrefl, if_false, sub_zero]
      linarith
    · have := imForm_swap (b j) (b i)
      simp only [h, lt_asymm h, if_true, if_false, zero_sub]
      linarith
  rw [key]
  simp only [LinearMap.sub_apply, LinearMap.flip_apply]

theorem upper_int (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    {x y : EuclideanSpace ℂ ι} (hx : x ∈ lat b) (hy : y ∈ lat b) :
    ∃ k : ℤ, upper b x y = k := by
  have base : ∀ i j, ∃ k : ℤ, upper b (b i) (b j) = k := by
    intro i j
    rw [upper_basis]
    split_ifs
    · rw [imForm_apply]
      exact hint _ _ (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨j, rfl⟩)
    · exact ⟨0, by simp⟩
  have hrow : ∀ i, ∃ k : ℤ, upper b (b i) y = k := by
    intro i
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact base i j
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨k₁, h₁⟩ := hz
      obtain ⟨k₂, h₂⟩ := hw
      exact ⟨k₁ + k₂, by simp [map_add, h₁, h₂]⟩
    | smul n z _ hz =>
      obtain ⟨k₁, h₁⟩ := hz
      exact ⟨n * k₁, by simp [map_zsmul, h₁, zsmul_eq_mul]⟩
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact hrow i
  | zero => exact ⟨0, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨k₁, h₁⟩ := hz
    obtain ⟨k₂, h₂⟩ := hw
    exact ⟨k₁ + k₂, by simp [map_add, LinearMap.add_apply, h₁, h₂]⟩
  | smul n z _ hz =>
    obtain ⟨k₁, h₁⟩ := hz
    exact ⟨n * k₁, by simp [map_zsmul, LinearMap.smul_apply, h₁, zsmul_eq_mul]⟩

theorem exists_coc {ι : Type} [Fintype ι]
    (b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    (hperf : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b,
      (φ y : ℝ) = (Hf x (y : EuclideanSpace ℂ ι)).im) :
    ∃ Y : GT ι, Y.b = b ∧ FPw.Coc Y 1 := by
  refine ⟨⟨b, hint, hperf, fun x => Complex.exp (((Real.pi * upper b x x : ℝ) : ℂ) * Complex.I),
    fun x _ => Complex.norm_exp_ofReal_mul_I _⟩, rfl, ?_⟩
  intro γ hγ γ' hγ'
  obtain ⟨k, hk⟩ := upper_int b hint hγ hγ'
  have him : (Hf γ γ').im = upper b γ γ' - upper b γ' γ := by
    rw [← imForm_apply]
    exact upper_sub b γ γ'
  have hadd : upper b (γ + γ') (γ + γ') =
      upper b γ γ + upper b γ γ' + upper b γ' γ + upper b γ' γ' := by
    simp only [map_add, LinearMap.add_apply]
    ring
  dsimp only
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  rw [hadd, him, hk]
  push_cast
  ring

end

end GlobalTheory.UpperHalfImaginaryForm
