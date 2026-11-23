import Formalism.PeriodIntegrals.UnimodLocStd

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

def SatMem {m : Type*} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) (x : m → ℂ) : Prop := ∃ n : ℕ, ¬ l ∣ n ∧ n • x ∈ Λ

def KeyRep : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ →
      (∀ x ∈ Λ, cmTheta b d • x ∈ Λ) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0 →
      relIdx Λ (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∀ x y : ℤ, ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2 →
      ∀ (T : Finset m) (i₀ : m), i₀ ∉ T →
        (∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) →
        ∃ v : m → ℂ, SatMem l Λ v ∧ (∀ j ∈ T, v j = 0) ∧
          stdH (cmL a b d ha hd lam hlam) m v v =
            stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))
              (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))

end PI.UnitaryGroupMassFormula.UnimodLocStd
