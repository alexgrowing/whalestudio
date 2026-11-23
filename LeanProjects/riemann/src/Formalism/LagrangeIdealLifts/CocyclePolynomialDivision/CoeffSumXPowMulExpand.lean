import Formalism.LagrangeIdealLifts.Statement

noncomputable section

namespace Formalism.LIFT

open Polynomial

def polyBase (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) : Base ℓ (Polynomial ℤ_[ℓ]) where
  φA := AlgHom.id ℤ_[ℓ] (Polynomial ℤ_[ℓ])
  γA := aeval (C (u : ℤ_[ℓ]) * X)
  X := X
  Q := 1
  u := u
  comm := fun _ => rfl
  φX := (mul_one _).symm
  γX := ⟨0, by
    change aeval (C (u : ℤ_[ℓ]) * X) (X : Polynomial ℤ_[ℓ]) =
      X * (algebraMap ℤ_[ℓ] (Polynomial ℤ_[ℓ]) (u : ℤ_[ℓ]) + X * 0)
    rw [aeval_X, mul_zero, add_zero, Polynomial.algebraMap_eq, mul_comm]⟩
  γQ := ⟨0, by simp⟩

lemma X_dvd_aeval_sub (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ_[ℓ]) (p : Polynomial ℤ_[ℓ]) :
    X ∣ aeval (C c * X) p - p := by
  rw [X_dvd_iff, coeff_sub, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero,
    ← comp_eq_aeval, eval_comp]
  simp

def polyWD (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) : WD (polyBase ℓ u) 0 (Polynomial ℤ_[ℓ]) where
  N := ⊤
  φ := LinearMap.id
  γ := (aeval (C (u : ℤ_[ℓ]) * X) : Polynomial ℤ_[ℓ] →ₐ[ℤ_[ℓ]] Polynomial ℤ_[ℓ]).toLinearMap
  φ_smul := fun _ _ => rfl
  γ_smul := fun a x => by
    simp only [AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
    rfl
  comm := fun _ => rfl
  X_inj := fun x hx => by
    change (X : Polynomial ℤ_[ℓ]) * x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left X_ne_zero
  Q_bij := by
    change Function.Bijective (fun x : Polynomial ℤ_[ℓ] => (1 : Polynomial ℤ_[ℓ]) • x)
    simp only [one_smul]
    exact Function.bijective_id
  φ_N := fun _ _ => Submodule.mem_top
  γ_N := fun x _ => by
    obtain ⟨c, hc⟩ := X_dvd_aeval_sub ℓ (u : ℤ_[ℓ]) x
    exact ⟨c, Submodule.mem_top, by
      simp only [AlgHom.toLinearMap_apply, smul_eq_mul]; exact hc⟩

theorem wDNonempty_proof : WDNonempty := by
  intro ℓ _ u
  refine ⟨polyBase ℓ u, polyWD ℓ u, rfl, ?_, ?_⟩
  · exact top_ne_bot
  · exact not_isUnit_X

section Decomp

variable {R : Type} [CommRing R]

def piece (ℓ : ℕ) (g : R[X]) (i : ℕ) : R[X] := contract ℓ (divX^[i] g)

end Decomp

end Formalism.LIFT
