import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.IsPairFrame

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.CM (omegaK)

def MulRing : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ z : ℂ, (∀ ω ∈ (cmL a b d ha hd lam hlam).lattice, z * ω ∈ (cmL a b d ha hd lam hlam).lattice) →
      ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * omegaK d

def IotaOK : Prop :=
  ∀ (d : ℕ), d % 4 = 3 → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
    ‖ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ))‖ = ‖(d : ℂ_[p])‖ ^ (1 / 2 : ℝ) ∧
    ∀ m n : ℤ, ‖ι ((m : ℂ) + (n : ℂ) * omegaK d)‖ ≤ 1 ∧
      ι ((m : ℂ) + (n : ℂ) * omegaK d) - ι (conj ((m : ℂ) + (n : ℂ) * omegaK d)) =
        ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * (n : ℂ_[p])

def GramTransfer : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
      ¬ p ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a b d ha hd lam hlam) Λ (v j)) →
    ∃ (D : Fin 4 × n → Fin 4 × J → ℂ_[p]) (q0 : Fin 4 × J → Fin 4 × J → ℂ_[p]),
      (∀ w x, ‖D w x‖ ≤ 1) ∧ (∀ x y, ‖q0 x y‖ ≤ 1) ∧
      (∀ (a' : Fin 4) (i : n) (b' : Fin 4) (j : J),
        ∑ w, ι (g.symm (Pi.single w 1) (a', i)) * D w (b', j) = if a' = b' then ι (v j i) else 0) ∧
      ∀ x y, ∑ w, D w x * D w y =
        (if x.1 = y.1 then ι (hOK (cmL a b d ha hd lam hlam) h (v x.2) (v y.2)) else 0)
          + ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * q0 x y

end Formalism.L2.Th1.GD
