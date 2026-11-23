import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IsRadicalAway {R : Type*} [CommRing R] (K : Ideal R) (g : R) : Prop :=
  ∀ f ∈ K.radical, ∃ k : ℕ, g ^ k * f ∈ K

def fibreIdeal {σ : Type*} {n : ℕ} (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ))) (t : σ → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  K.map (MvPolynomial.map (eval t))

theorem fibreIdeal_map_C {σ : Type*} {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (t : σ → ℂ) :
    fibreIdeal (J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ))) t = J := by
  have h : (MvPolynomial.map (eval t)).comp (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ)) =
      RingHom.id (MvPolynomial (Fin n) ℂ) := by
    ext p <;> simp
  rw [fibreIdeal, Ideal.map_map, h, Ideal.map_id]

def GenericFibreRadicalAway.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (n : ℕ) (K : Ideal (MvPolynomial (Fin n) (MvPolynomial σ ℂ)))
    (g : MvPolynomial (Fin n) (MvPolynomial σ ℂ)), IsRadicalAway K g →
    ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      IsRadicalAway (fibreIdeal K t) (MvPolynomial.map (eval t) g)

end

end GroundTheory.Heights₂.Heights
