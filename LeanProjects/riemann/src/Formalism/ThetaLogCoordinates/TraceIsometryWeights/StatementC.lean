import Formalism.MahlerMeasure.StatementT

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M

def kapC (p n d : ℕ) : ℕ := n.choose 2 * Nat.log p (d + n - 1)

def FockAdj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (c d : Fin r)
    (F G : MvPolynomial (Fin N × Fin r) ℚ_[p]), fock p (glAct p LL j c d F) G = fock p F (glAct p LL j d c G)

def SpanIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)),
    (⨆ la : Fin r → ℤ, IsoC p LL j Cs la) = ⊤

def OrthIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la mu : Fin r → ℤ),
    (∃ c ∈ Cs, la c ≠ mu c) → ∀ x ∈ IsoC p LL j Cs la, ∀ y ∈ IsoC p LL j Cs mu, fock p x y = 0

def ProjP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ)),
    CsSaturated Cs T → ∃ P, IsTypeProj p LL j Cs T P ∧ ∀ F G, fock p (P F) G = fock p F (P G)

def CommP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j j' : ℕ) (Cs Cs' : Finset (Fin r))
    (T T' : Set (Fin r → ℤ)) (P P'), j ≤ j' → Cs' ⊆ Cs →
    IsTypeProj p LL j Cs T P → IsTypeProj p LL j' Cs' T' P' → P ∘ₗ P' = P' ∘ₗ P

def IntP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ)) (P),
    CsSaturated Cs T → IsTypeProj p LL j Cs T P →
    ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ kapC p Cs.card LL.total) • P F ∈ IntPol p (Fin N × Fin r)

def WeylP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N), HypW p (r := r) LL (kapC p r LL.total)

def ExtP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r), HypE p LL ρ (kapC p (r - 1) LL.total)

end Formalism.InvariantFactorPaths.PW
