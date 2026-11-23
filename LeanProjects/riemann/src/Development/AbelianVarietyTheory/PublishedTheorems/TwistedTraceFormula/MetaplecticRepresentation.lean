import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.Published

namespace Metaplectic

variable {ι : Type} [Fintype ι]

def eChar : AddChar ℝ ℂ := Circle.coeHom.compAddChar Real.fourierChar

theorem eChar_apply (x : ℝ) : eChar x = cexp (2 * π * x * I) := by
  show ((Real.fourierChar x : Circle) : ℂ) = _
  rw [Real.fourierChar_apply]
  push_cast
  ring_nf

theorem hasTemperateGrowth_eChar : Function.HasTemperateGrowth (eChar : ℝ → ℂ) := by
  have hf : (eChar : ℝ → ℂ) = fun x : ℝ => cexp (2 * π * x * I) := funext eChar_apply
  have hlin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (2 * π * y * I : ℂ)) (2 * π * I) x := by
    intro x
    have h := (((hasDerivAt_id x).ofReal_comp).const_mul (2 * π : ℂ)).mul_const I
    simpa using h
  have hd : ∀ c : ℂ, deriv (fun x : ℝ => c * cexp (2 * π * x * I)) =
      fun x : ℝ => c * (2 * π * I) * cexp (2 * π * x * I) := by
    intro c
    funext x
    rw [((hlin x).cexp.const_mul c).deriv]
    ring
  have hit : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => cexp (2 * π * x * I)) =
      fun x : ℝ => (2 * π * I) ^ n * cexp (2 * π * x * I) := by
    intro n
    induction n with
    | zero => funext x; simp
    | succ n ih => rw [iteratedDeriv_succ, ih, hd, pow_succ]
  have hnorm : ∀ x : ℝ, ‖cexp (2 * π * x * I)‖ = 1 := by
    intro x
    rw [show (2 * π * x * I : ℂ) = ((2 * π * x : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hf]
  refine ⟨?_, fun n => ⟨0, (2 * π) ^ n, fun x => ?_⟩⟩
  · exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const).cexp
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hit n]
    simp only [norm_mul, norm_pow, hnorm, mul_one, pow_zero]
    simp [abs_of_pos Real.pi_pos]

def rho (w : (ι → ℝ) × (ι → ℝ)) : 𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => eChar (x ⬝ᵥ w.2 + ⅟(2 : ℝ) * (w.1 ⬝ᵥ w.2))) ∘L
    SchwartzMap.compSubConstCLM ℂ (-w.1)

private lemma hasTemperateGrowth_eChar_dotProduct_phase (w : (ι → ℝ) × (ι → ℝ)) :
    (fun x : ι → ℝ => eChar (x ⬝ᵥ w.2 + ⅟(2 : ℝ) * (w.1 ⬝ᵥ w.2))).HasTemperateGrowth := by
  have hl : (fun x : ι → ℝ => x ⬝ᵥ w.2).HasTemperateGrowth := by
    have h : (fun x : ι → ℝ => x ⬝ᵥ w.2) = fun x => ∑ i, x i * w.2 i := rfl
    rw [h]
    exact Function.HasTemperateGrowth.sum fun i _ =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).hasTemperateGrowth.mul
        (Function.HasTemperateGrowth.const _)
  exact hasTemperateGrowth_eChar.comp (hl.add (Function.HasTemperateGrowth.const _))

theorem coe_rho (w : (ι → ℝ) × (ι → ℝ)) (φ : 𝓢(ι → ℝ, ℂ)) : ⇑(rho w φ) = GlobalTheory.WeilM.schr eChar w φ := by
  funext x
  simp only [rho, ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_eChar_dotProduct_phase w), SchwartzMap.compSubConstCLM_apply]
  simp [GlobalTheory.WeilM.schr]

theorem rho_apply (p q : ι → ℝ) (φ : 𝓢(ι → ℝ, ℂ)) (x : ι → ℝ) :
    rho (p, q) φ x = cexp (2 * π * ((x ⬝ᵥ q + p ⬝ᵥ q / 2 : ℝ) : ℂ) * I) * φ (x + p) := by
  rw [coe_rho]
  simp only [GlobalTheory.WeilM.schr, eChar_apply, invOf_eq_inv]
  congr 2
  push_cast
  ring

def act (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (w : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  ((g *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (g *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_fromBlocks (A B C D : Matrix ι ι ℝ) (p q : ι → ℝ) :
    act (fromBlocks A B C D) (p, q) = (A *ᵥ p + B *ᵥ q, C *ᵥ p + D *ᵥ q) := by
  simp [act, Matrix.fromBlocks_mulVec]

def holPart (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : Matrix ι ι ℂ := fun i j =>
  ((g (.inl i) (.inl j) + g (.inr i) (.inr j) : ℝ) + I * (g (.inr i) (.inl j) - g (.inl i) (.inr j) : ℝ)) / 2

end Metaplectic

open Metaplectic

def MetaplecticRepresentation : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (pr : G →* symplecticGroup ι ℝ)
      (Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))))
      (ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ))) (φ₀ : 𝓢(ι → ℝ, ℂ)),
      Function.Surjective pr ∧ IsCoveringMap pr ∧ Nat.card pr.ker = 2 ∧
      (∀ g f, ‖Ω g f‖ = ‖f‖) ∧ (∀ f, Continuous fun g => Ω g f) ∧
      (∀ g (φ : 𝓢(ι → ℝ, ℂ)), Ω g (φ.toLp 2) = (ω g φ).toLp 2) ∧
      (Continuous fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) ∧
      (∀ g w φ, ω g (rho w φ) = rho (act (pr g).1 w) (ω g φ)) ∧
      (∀ g, pr g = 1 → g ≠ 1 → ∀ φ, ω g φ = -φ) ∧
      (∀ x, φ₀ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))) ∧
      (∀ g, (∫ x, ω g φ₀ x * conj (φ₀ x)) ^ 2 * (holPart (pr g).1).det = (∫ x, φ₀ x * conj (φ₀ x)) ^ 2) ∧
      (∀ g, (pr g).1ᵀ * (pr g).1 = 1 → ∃ c : ℂ, c ^ 2 * (holPart (pr g).1).det = 1 ∧ ω g φ₀ = c • φ₀)

end GlobalTheory.Published

end
