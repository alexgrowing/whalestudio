import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactVersion
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.UnitaryConstant
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.GaussDegenerate

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

def cmL (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) : PeriodPair :=
  Formalism.L2.Th1.F.scalePair (Formalism.L2.Th1.F.cmPair a b d ha hd) lam hlam

def CmStdCharScale : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), 4 * (a : ℤ) * c = b ^ 2 + d →
    Odd a → d % 8 = 7 → ∀ (n : Type) [Fintype n] [DecidableEq n], ∀ x ∈ stdLat (cmL a b d ha hd lam hlam) n,
      alphaQ (Real.sqrt d / 2) (stdH (cmL a b d ha hd lam hlam) n) x = stdChar (cmL a b d ha hd lam hlam) (lam * a) x

def CmOK (a : ℕ) (b c : ℤ) (d : ℕ) : Prop := 4 * (a : ℤ) * c = b ^ 2 + d ∧ Odd a ∧ d % 8 = 7 ∧ d.Prime

def StdDataCm : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), 4 * (a : ℤ) * c = b ^ 2 + d → Odd a → d % 8 = 7 →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
      IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b d • x ∈ Λ) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 →
      relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
        (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) ≠ 0 →
      StdData (cmL a b d ha hd lam hlam) (lam * a) h Λ (alphaQ (Real.sqrt d / 2) (matH h))
        (alphaQ (Real.sqrt d / 2) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))) g

def KernelRatio : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ)
    (g₀ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), StdData L ω₀ h Λ α β g₀ → StdData L ω₀ h Λ α β g₁ →
    (∀ x, g₁ x = g₀ x → x = 0) →
    ∃ c : ℂ, c ^ 8 = LinearMap.det ((g₀.symm.trans g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
          (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ^ 4 ∧
      kernel4 L ω₀ Λ β g₀ = c • kernel4 L ω₀ Λ β g₁

def quadraticSemicharacterIdentityEquivalent : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (ω₀ : ℂ) (lg linv ph : PowerSeries ℂ_[l]),
    Formalism.L2.Th1.C.IsLogPair lg linv → PowerSeries.constantCoeff ph = 0 → TransInt l L ι ω₀ lg ph →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
      (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (β : (Fin 4 × n → ℂ) → ℂ)
      (g₀ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), StdData L ω₀ h Λ α β g₀ → StdData L ω₀ h Λ α β g₁ →
    (∀ x, g₁ x = g₀ x → x = 0) →
    ¬ l ∣ relIdx (stdLat L (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∀ κ : ℂ, ‖ι κ‖ ^ 2 * ‖ι (LinearMap.det ((g₀.symm.trans g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
          (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))‖ = 1 →
    ∀ θ ∈ Th (matH h) α Λ, tens4 θ = κ • kernel4 L ω₀ Λ β g₀ →
    ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
    ∀ (O : Type) [Semiring O] (τ : O →+* ℂ_[l]) (γ : Matrix (Fin 4 × n) (Fin 4 × n) O)
      (B' : Matrix n n ℂ_[l]),
      (∀ (a : Fin 4) (i : n) (w : Fin 4 × n),
        ∑ j, B' i j * τ (γ (a, j) w) = ι (g₁.symm (Pi.single w 1) (a, i))) →
      Formalism.L2.Th1.E.ThetaFourthTensorPowerProductShape lg linv ph τ (thetaU (ι : ℂ →+* ℂ_[l]) lg B' (opU (matH h) t θ)) γ

def LocalStandard : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, Formalism.L2.Th1.F.cmTheta b d • x ∈ Λa) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∃ δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧ (∀ x, δ x = x → x = 0) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0

def KappaExists : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, Formalism.L2.Th1.F.cmTheta b d • x ∈ Λa) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ : ℂ ≃+* ℂ, ‖σ κ‖ = 1) ∧
        ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
          IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
            (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) →
          relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 →
          ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
          relIdx (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
          ‖ι κ‖ ^ 2 * ‖ι (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)))‖ = 1

def quadraticSemicharacterIdentityReformulated : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
      (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)),
      IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
      IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b d • x ∈ Λ) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
        (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0 →
      relIdx (imgLat (g₀ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
        (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) ≠ 0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ : ℂ ≃+* ℂ, ‖σ κ‖ = 1) ∧
        ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt d / 2) (matH h)) Λ,
          tens4 θ = κ • kernel4 (cmL a b d ha hd lam hlam) (lam * a) Λ
            (alphaQ (Real.sqrt d / 2) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))) g₀ →
        ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]), ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
          IsIsom (matH (blk4 h)) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))
            (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
          ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n))
            (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
          relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
            (stdLat (cmL a b d ha hd lam hlam) (Fin 4 × n)) ≠ 0 ∧
          (∃ ε : ℂ, ‖ι ε‖ = 1 ∧ tens4 θ = ε • kernel4 (cmL a b d ha hd lam hlam) (lam * a) Λ
            (alphaQ (Real.sqrt d / 2) (stdH (cmL a b d ha hd lam hlam) (Fin 4 × n))) g₁) ∧
          ∀ (lg linv ph : PowerSeries ℂ_[l]), Formalism.L2.Th1.C.IsLogPair lg linv →
            PowerSeries.constantCoeff ph = 0 →
            TransInt l (cmL a b d ha hd lam hlam) ι (lam * a) lg ph →
          ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
          ∀ (O : Type) [Semiring O] (τ : O →+* ℂ_[l]) (γ : Matrix (Fin 4 × n) (Fin 4 × n) O)
            (B' : Matrix n n ℂ_[l]),
            (∀ (i' : Fin 4) (i : n) (w : Fin 4 × n),
              ∑ j, B' i j * τ (γ (i', j) w) = ι (g₁.symm (Pi.single w 1) (i', i))) →
            Formalism.L2.Th1.E.ThetaFourthTensorPowerProductShape lg linv ph τ (thetaU (ι : ℂ →+* ℂ_[l]) lg B' (opU (matH h) t θ)) γ

end Formalism.L2.Th1.H
