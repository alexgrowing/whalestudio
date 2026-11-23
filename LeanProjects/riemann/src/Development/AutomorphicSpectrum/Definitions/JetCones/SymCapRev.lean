import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.RealPlaceAnalysis.StatementB
import Formalism.RealPlaceAnalysis.StatementE

open scoped InnerProductSpace
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible

def symCap {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : Fin n → ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
    (((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (x k) (σ k) (τ k)).prod

def symCapRev {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : Fin n → ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
    (((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (x k) (σ k) (τ k)).reverse.prod

def TensRule {A : Type*} [Ring A] {n : ℕ} (θ β : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, θ a b * β c d - β c d * θ a b =
    (if b = c then β a d else 0) - (if d = a then β c b else 0)

def KRel {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (D : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, ε a = ε b → ε c = ε d → D a b * D c d - D c d * D a b =
    (if b = c then D a d else 0) - (if d = a then D c b else 0)

def KAdj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (D : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ x y : V, ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ

def CAR {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (p m : Fin n → Fin n → A) : Prop :=
  (∀ a b, ε a = ε b → p a b = 0 ∧ m a b = 0) ∧
  (∀ a b c d, m a b * p c d + p c d * m a b = if a = c ∧ b = d ∧ ε a ≠ ε b then 1 else 0) ∧
  (∀ a b c d, p a b * p c d + p c d * p a b = 0) ∧
  (∀ a b c d, m a b * m c d + m c d * m a b = 0)

def kap {A : Type*} [Ring A] {n : ℕ} (p m : Fin n → Fin n → A) (a b : Fin n) : A :=
  ∑ d, p a d * m b d - ∑ c, p c b * m c a

def num {A : Type*} [Ring A] {n : ℕ} (p m : Fin n → Fin n → A) : A :=
  ∑ a, ∑ b, p a b * m a b

def ncCard {n : ℕ} (ε : Fin n → Bool) : ℕ :=
  (univ.filter fun x : Fin n × Fin n => x.1 < x.2 ∧ ε x.1 ≠ ε x.2).card

def Base {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E p m : Fin n → Fin n → Module.End ℂ W) : Prop :=
  Formalism.REAL.GlRel E ∧ (∀ a b x y, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ) ∧ CAR ε p m ∧
  (∀ a b x y, ⟪p a b x, y⟫_ℂ = ⟪x, m a b y⟫_ℂ) ∧
  ∀ a b c d, Commute (E a b) (p c d) ∧ Commute (E a b) (m c d)

def Vac {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E p m : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) (w : W) : Prop :=
  w ≠ 0 ∧ Formalism.REAL.IsWeight E ν w ∧ ∀ a b, a < b → E a b w = 0 ∧ p a b w = 0 ∧ m b a w = 0

def WtBd {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) : Prop :=
  ∀ (φ : Fin n → ℝ) (v : W), v ≠ 0 → Formalism.REAL.IsWeight E φ v →
    ∀ (w : Equiv.Perm (Fin n)) (x : Fin n → ℝ), Antitone x →
      PI.UpqRep.dot x (φ ∘ w) ≤ PI.UpqRep.dot x ν

def WigMod {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E p m : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) : Prop :=
  Base ε E p m ∧ (∃ w, Vac E p m ν w) ∧ WtBd E ν ∧
  ∀ (u : ℂ) (v : W), Formalism.REAL.qdet E u v = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + (ν k : ℂ))) • v

def KMap {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] {n : ℕ}
    (ε : Fin n → Bool) (D : Fin n → Fin n → Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ X)
    (ω : W →ₗ[ℂ] X) : Prop :=
  ∀ a b, ε a = ε b → ∀ w, ω (D a b w) = E a b (ω w)

def IsDer {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (j : X →ₗᵢ[ℂ] H) (E : Fin n → Fin n → Module.End ℂ X) : Prop :=
  Set.range j = PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ ∧
  ∀ a b x, j (E a b x) = PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM (a, b)) (j x)

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible

end
