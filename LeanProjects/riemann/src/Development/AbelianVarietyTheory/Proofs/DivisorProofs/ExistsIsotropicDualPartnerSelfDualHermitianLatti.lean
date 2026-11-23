import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.TraceCorrection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, add_dotProduct]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  have h : (fun i => σ ((y + y') i)) = (fun i => σ (y i)) + fun i => σ (y' i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  have h : (fun i => σ ((c • y) i)) = σ c • fun i => σ (y i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_symm (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (form σ J x y) = form σ J y x := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ x y₀ : Fin n → E, form σ J x x = 0 → form σ J y₀ x = 1 →
    (∀ z ∈ L, form σ J z x • y₀ ∈ L) →
    ∃ y : Fin n → E, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z y • x ∈ L ∧ form σ J z x • y ∈ L := by
  intro F E _ _ _ _ _ σ hσ n J L hJ hL θ hθ x y₀ hxx hy₀x hL0
  have hsa : σ (form σ J y₀ y₀) = form σ J y₀ y₀ := form_symm σ J hσ hJ y₀ y₀
  have hxw : ∀ w, form σ J x w = σ (form σ J w x) := fun w => (form_symm σ J hσ hJ w x).symm
  have hxy₀ : form σ J x y₀ = 1 := by rw [hxw, hy₀x, map_one]
  have hsθ : σ (θ : E) = 1 - θ := by linear_combination hθ
  have hθi : IsIntegral ℤ (θ : E) := θ.isIntegral_coe
  have hA : ∀ z ∈ L, ∀ w ∈ L,
      IsIntegral ℤ (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
    intro z hz w hw
    have h := (hL _).1 (hL0 z hz) _ (hL0 w hw)
    rw [form_smul_left, form_smul_right] at h
    have k : form σ J z x * (σ (form σ J w x) * form σ J y₀ y₀) =
        form σ J y₀ y₀ * form σ J z x * σ (form σ J w x) := by ring
    rw [← k]; exact h
  refine ⟨y₀ + (-((θ : E) * form σ J y₀ y₀)) • x, ?_, ?_, ?_⟩
  · simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hxx, hxy₀, hy₀x,
      map_neg, map_mul, hsθ, hsa]
    ring
  · simp only [form_add_right, form_smul_right, hxx, hxy₀]
    ring
  intro z hz
  constructor
  · have e : form σ J z (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) • x =
        form σ J z y₀ • x + (σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x) • x := by
      rw [form_add_right, form_smul_right, add_smul]
    rw [e]
    refine L.add_mem ((hL _).2 fun w hw => ?_) ((hL _).2 fun w hw => ?_)
    · have h := (hL z).1 hz _ (hL0 w hw)
      rw [form_smul_right] at h
      rw [form_smul_left, hxw, mul_comm]
      exact h
    · rw [form_smul_left, hxw]
      have h := (hA z hz w hw).neg.add (hθi.mul (hA z hz w hw))
      have k : σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x * σ (form σ J w x) =
          -(form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) +
            (θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
        rw [map_neg, map_mul, hsθ, hsa]; ring
      rw [k]; exact h
  · have e : form σ J z x • (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) =
        form σ J z x • y₀ + (form σ J z x * (-((θ : E) * form σ J y₀ y₀))) • x := by
      rw [smul_add, mul_smul]
    rw [e]
    refine L.add_mem (hL0 z hz) ((hL _).2 fun w hw => ?_)
    rw [form_smul_left, hxw]
    have h := (hθi.mul (hA z hz w hw)).neg
    have k : form σ J z x * (-((θ : E) * form σ J y₀ y₀)) * σ (form σ J w x) =
        -((θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x))) := by ring
    rw [k]; exact h

end GlobalTheory.TraceCorrection
