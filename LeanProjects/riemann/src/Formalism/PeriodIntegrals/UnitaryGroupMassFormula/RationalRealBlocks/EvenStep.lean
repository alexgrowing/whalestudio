import Mathlib
import Formalism.PeriodIntegrals.BlockRatReal

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal

def EvenStep : Prop :=
  ∀ (m : ℕ) (LL : Type) [Field LL] (embLL : LL →+* ℂ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∀ (M0 : GL (Fin (m + 1)) LL) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ),
      f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam) →
      ∃ F ∈ dualWeyl LL (m + 1) (m + 1) (nuOf lam), ∀ y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, IsUnit y.det →
        (M0.1.map embLL * y).det ^ lam (Fin.last m) *
            eval (fun x => (M0.1.map embLL * y) x.1 x.2) (MvPolynomial.map embLL F) =
          y.det ^ lam (Fin.last m) * eval (fun x => y x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)

def OddStep : Prop :=
  ∀ (m : ℕ) (LL : Type) [Field LL] (embLL : LL →+* ℂ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∀ (M0 : GL (Fin (m + 1)) LL) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ),
      f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam) →
      ∃ F ∈ dualWeyl LL (m + 1) (m + 1) (nuOf fun i => -lam i.rev),
        ∀ y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, IsUnit y.det →
          (((M0.1.map embLL * y)⁻¹)ᵀ.submatrix id Fin.rev).det ^ (-lam (Fin.last m).rev) *
              eval (fun x => ((M0.1.map embLL * y)⁻¹)ᵀ.submatrix id Fin.rev x.1 x.2) (MvPolynomial.map embLL F) =
            y.det ^ lam (Fin.last m) * eval (fun x => y x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)

end PI.BlockRatReal
