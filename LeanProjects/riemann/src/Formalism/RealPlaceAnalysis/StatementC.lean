import Formalism.RealPlaceAnalysis.StatementB

open Finset

noncomputable section

namespace Formalism.REAL

def cyc {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  sInf {W : Submodule ℂ V | v ∈ W ∧ ∀ a b, ∀ x ∈ W, E a b x ∈ W}

def cval {n : ℕ} (ν : Fin n → ℂ) : ℂ :=
  ∑ a, ν a ^ 2 + ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (ν a - ν b)

def chamber {n : ℕ} (G : Fin n → Fin n → ℤ) : Set (Fin n → ℤ) :=
  {m | ∀ a b, a < b → G a b ≤ m a - m b}

def CasHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v → Cas E v = cval ν • v

def CasCyc : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ x ∈ cyc E v, Cas E x = cval ν • x

def CharId : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ x ∈ cyc E v, ∀ a b : Fin n,
      ∑ i ∈ range (n + 1),
        (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b x = 0

def DegVand : Prop :=
  ∀ (n : ℕ) (c : ℂ) (G : Fin n → Fin n → ℤ) (f : (Fin n → ℤ) → ℂ),
    (∀ a b, a < b → 1 ≤ G a b) →
    (∀ (m : Fin n → ℤ) (s : Fin n), m ∈ chamber G → m - Pi.single s 1 ∈ chamber G →
      f (m - Pi.single s 1) = Dfac (fun a => c + (m a : ℂ)) s * f m) →
    ∀ m m', m ∈ chamber G → m' ∈ chamber G →
      f m * vand (fun a => c + (m' a : ℂ)) = f m' * vand (fun a => c + (m a : ℂ))

end Formalism.REAL
