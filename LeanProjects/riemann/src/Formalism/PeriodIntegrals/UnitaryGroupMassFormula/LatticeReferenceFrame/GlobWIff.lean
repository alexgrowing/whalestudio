import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Development

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Sk

def Concl (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) : Prop :=
    ∃ (z : Fin I.n → I.E) (b bd : Fin k → Fin I.n → I.E),
      z ∈ I.L ∧ (∀ i, b i ∈ I.L ∧ bd i ∈ I.L) ∧
      (∀ a, hG I (e a) z = 0 ∧ hG I (f a) z = 0) ∧
      (∀ a i, hG I (e a) (b i) = 0 ∧ hG I (f a) (b i) = 0 ∧
        hG I (e a) (bd i) = 0 ∧ hG I (f a) (bd i) = 0) ∧
      GE I g (hG I z z + 1) ∧
      (∀ i, GE I g ((θ : I.E) * hG I z (b i)) ∧ GE I g (star (θ : I.E) * hG I z (bd i))) ∧
      (∀ i j, GE I g ((θ : I.E) * (hG I (bd i) (b j) - if i = j then 1 else 0))) ∧
      ∀ y ∈ I.L, y ∈ Submodule.span (𝓞 I.E)
        (Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪ {z} ∪
          Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)) ⊔ gL I g

def Hyp (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) : Prop :=
  1 ≤ g ∧ SplitG I g ∧ IsTheta I g θ ∧ I.n = 2 * r + k + 1 ∧
    (∀ a b, hG I (e a) (e b) = 0) ∧ (∀ a b, hG I (f a) (f b) = 0) ∧
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) ∧
    Nat.Coprime M g ∧ (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L)

def GWpp : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    p.Prime → 1 ≤ m → Hyp I (p ^ m) r k θ e f M → Concl I (p ^ m) r k θ e f M

def GWcrt : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g₁ g₂ r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    Nat.Coprime g₁ g₂ → Hyp I (g₁ * g₂) r k θ e f M →
    Concl I g₁ r k θ e f M → Concl I g₂ r k θ e f M → Concl I (g₁ * g₂) r k θ e f M

end PI.ScRefExists.Sk
