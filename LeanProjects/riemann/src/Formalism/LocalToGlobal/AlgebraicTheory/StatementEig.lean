import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer

noncomputable section
open scoped BigOperators
open NumberField IsDedekindDomain

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL)
open Formalism.L2.Th1.GD (InMul frameM)
open Formalism.L2.Col (Fields Sp)
open Formalism.L2.Ker (Amb DVar)

open Classical in

def EigenFrameDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), ¬ (p : ℤ) ∣ NumberField.discr E →
  ∀ τ₀ : E →+* ℂ, ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ_[p], (∀ i, ‖r i‖ ≤ 1) ∧
    ∀ φ : E →+* ℂ, ∑ i, r i * ι (φ ((NumberField.RingOfIntegers.basis E i : 𝓞 E) : E)) = if φ = τ₀ then 1 else 0

def vecE {X : Fields} (σ₀ : X.K →+* ℂ) {a b : ℕ} (r : X.E) (β : Fin b) (α : Fin a) : DVar X.Tau a b → ℂ :=
  fun k => if k.2.1 = β ∧ k.2.2 = α then X.embC σ₀ k.1 r else 0

def KerFrame : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (L : PeriodPair) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
    ¬ (p : ℤ) ∣ NumberField.discr X.E → Function.Injective (X.embC A.σ₀) → (∀ τ, ‖ι (A.cD τ)‖ ≤ 1) →
    (∃ n₀ : ℕ, ¬ p ∣ n₀ ∧ ∀ (r : 𝓞 X.E) (β : Fin b) (α : Fin a),
      InMul L (lamF A N N') ((n₀ : ℂ) • vecE A.σ₀ (r : X.E) β α)) →
    ∃ (J : Type) (_ : Fintype J) (v : J → DVar X.Tau a b → ℂ) (M : J → DVar X.Tau a b → ℂ_[p]),
      (∀ j, InMul L (lamF A N N') (v j)) ∧ (∀ j k, ‖M j k‖ ≤ 1) ∧
      ∀ i k, frameM (ι : ℂ →+* ℂ_[p]) v M i k = if i = k then ι (A.cD k.1) else 0

end Formalism.L2.AlgTh
