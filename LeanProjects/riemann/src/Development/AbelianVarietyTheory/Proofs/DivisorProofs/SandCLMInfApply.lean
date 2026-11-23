import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW
open scoped FourierTransform

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def IsRapidFamInf {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X)
    (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ) :
    Prop :=
  (∀ i j, Measurable fun x =>(γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) ∧
  (∀ (X₀ : Type) [MeasurableSpace X₀] (γ₀ : X₀ → GL (Fin n) (Cinf E)),
    (∀ i j, Measurable fun x =>(γ₀ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) →
      Measurable (fun p : X₀ × X =>k (γ₀ p.1) p.2) ∧ ∀ z, Measurable fun p : X₀ × X =>η (γ₀ p.1) p.2 z) ∧
  ∀ N : ℕ, ∃ (C : ℝ) (M : ℕ), ∀ q, Integrable (fun x =>‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N) ν ∧
    ∫ x, ‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N ∂ν ≤ C * htInf q ^ M

def sandCLMInf (A B : Matrix (Fin n) (Fin n) (Cinf E)) :
    (Fin n → Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i j =>(A * Matrix.of x * B) i j
      map_add' := fun x y =>by
        funext i j
        change (A * (Matrix.of x + Matrix.of y) * B) i j = (A * Matrix.of x * B) i j + (A * Matrix.of y * B) i j
        rw [mul_add, add_mul, Matrix.add_apply]
      map_smul' := fun c x =>by
        funext i j
        change (A * (c • Matrix.of x) * B) i j = c • (A * Matrix.of x * B) i j
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] }

theorem sandCLMInf_apply (A B : Matrix (Fin n) (Fin n) (Cinf E)) (x : Fin n → Fin n → Cinf E) (i j : Fin n) :
    sandCLMInf A B x i j = (A * Matrix.of x * B) i j := rfl

def jacInf (x : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ := ∏ w : InfinitePlace E, Complex.normSq (x.det w) ^ n

open Classical in

def secKInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : ℂ :=
  if IsUnit (Matrix.of p.1) ∧ htInf (toGLInf (Matrix.of p.1)) ≤ R * htInf q then
    ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * κ p.2 *
      (𝐞 (τ p.2 (0, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1) σ₀)) : ℂ)
  else 0

def secEtaInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : Z →L[ℝ] (Fin n → Fin n → Cinf E))
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : Z →L[ℝ] ℝ :=
  (τ p.2).comp ((ContinuousLinearMap.id ℝ Z).prod
    ((sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1)).comp L))

theorem jacInf_mul (x y : Matrix (Fin n) (Fin n) (Cinf E)) : jacInf (x * y) = jacInf x * jacInf y := by
  simp only [jacInf, Matrix.det_mul, Pi.mul_apply, map_mul, mul_pow, Finset.prod_mul_distrib]

example (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    IsRapidFamInf (Measure.dirac ()) (fun (_ : GL (Fin n) (Cinf E)) (_ : Unit) =>(1 : ℂ)) (fun _ =>1)
      (fun _ _ =>(0 : Z →L[ℝ] ℝ)) := by
  refine ⟨fun _ _ =>measurable_const, fun X₀ _ γ₀ _ =>⟨measurable_const, fun _ =>measurable_const⟩, fun N =>
    ⟨htInf (1 : GL (Fin n) (Cinf E)) ^ N, 0, fun q =>⟨integrable_const _, ?_⟩⟩⟩
  simp

end GlobalTheory.JSW.MirCinf
