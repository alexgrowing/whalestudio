import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

noncomputable section

namespace GlobalTheory.ConeSoB

open MeasureTheory Filter
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}

variable (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (K : Subgroup (UA σ X.J))
  (μK : Measure K) (μ : Measure (AE F E)ˣ) (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)

def coneInt (Φ : Fn F n d) (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → AF F) : ℂ :=
  e (M.co.rho B.ψ (u l) (om (k, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z

def IntOK (Φ : Fn F n d) : Prop :=
  ∀ y, (∀ k : K, Integrable (fun l => coneInt B M om e u ν z Φ k.1 l y) μ) ∧
    Integrable (fun k : K => ∫ l, coneInt B M om e u ν z Φ k.1 l y ∂μ) μK

theorem cone_apply (Φ : Fn F n d) (y : Fin n₁ × Fin d₁ → AF F) :
    cone B M om e K μK μ u ν z Φ y = ∫ k, ∫ l, coneInt B M om e u ν z Φ k.1 l y ∂μ ∂μK := rfl

variable {B M om e K μK μ u ν z}

theorem rho_lin (w : Matrix (Fin n) (Fin d) (AE F E)) (a b : ℂ) (Φ Ψ : Fn F n d) :
    M.co.rho B.ψ w (a • Φ + b • Ψ) = a • M.co.rho B.ψ w Φ + b • M.co.rho B.ψ w Ψ := by
  have hT : IsLinearMap ℂ (M.co.rho B.ψ w) :=
    ⟨fun f g => funext fun x => mul_add _ _ _, fun c f => funext fun x => mul_left_comm _ _ _⟩
  rw [hT.map_add, hT.map_smul, hT.map_smul]

theorem coneInt_lin (a b : ℂ) (Φ Ψ : Fn F n d) (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → AF F) :
    coneInt B M om e u ν z (a • Φ + b • Ψ) k l y =
      a * coneInt B M om e u ν z Φ k l y + b * coneInt B M om e u ν z Ψ k l y := by
  simp only [coneInt, map_add, map_smul, rho_lin, LinearMap.map_add, LinearMap.map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem coneInt_zero (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → AF F) :
    coneInt B M om e u ν z 0 k l y = 0 := by
  have h := coneInt_lin (B := B) (M := M) (om := om) (e := e) (u := u) (ν := ν) (z := z) 0 0 0 0 k l y
  simpa using h

theorem intOK_zero : IntOK B M om e K μK μ u ν z 0 := fun y => by
  simp only [coneInt_zero, integral_zero]
  exact ⟨fun _ => integrable_zero _ _ _, integrable_zero _ _ _⟩

theorem intOK_lin (a b : ℂ) {Φ Ψ : Fn F n d} (hΦ : IntOK B M om e K μK μ u ν z Φ) (hΨ : IntOK B M om e K μK μ u ν z Ψ) :
    IntOK B M om e K μK μ u ν z (a • Φ + b • Ψ) ∧
      cone B M om e K μK μ u ν z (a • Φ + b • Ψ) = a • cone B M om e K μK μ u ν z Φ + b • cone B M om e K μK μ u ν z Ψ := by
  have inner : ∀ y (k : K), ∫ l, coneInt B M om e u ν z (a • Φ + b • Ψ) k.1 l y ∂μ =
      a * ∫ l, coneInt B M om e u ν z Φ k.1 l y ∂μ + b * ∫ l, coneInt B M om e u ν z Ψ k.1 l y ∂μ := fun y k => by
    simp only [coneInt_lin]
    rw [integral_add (((hΦ y).1 k).const_mul a) (((hΨ y).1 k).const_mul b), integral_const_mul, integral_const_mul]
  refine ⟨fun y => ⟨fun k => ?_, ?_⟩, ?_⟩
  · simp only [coneInt_lin]
    exact (((hΦ y).1 k).const_mul a).add (((hΨ y).1 k).const_mul b)
  · simp only [inner y]
    exact ((hΦ y).2.const_mul a).add ((hΨ y).2.const_mul b)
  · funext y
    rw [cone_apply]
    simp only [inner y]
    rw [integral_add ((hΦ y).2.const_mul a) ((hΨ y).2.const_mul b), integral_const_mul, integral_const_mul]
    rfl

end GlobalTheory.ConeSoB
