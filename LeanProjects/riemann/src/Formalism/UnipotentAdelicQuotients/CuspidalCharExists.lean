import Mathlib

open Polynomial

noncomputable section

namespace Formalism.D.Classical

def grRootsBar {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Multiset (AlgebraicClosure (ZMod g)) :=
  (f.map (algebraMap (ZMod g) (AlgebraicClosure (ZMod g)))).roots

def grIp {G : Type} [Fintype G] (χ ψ : G → ℂ) : ℂ := ∑ x, χ x * star (ψ x)

def grIsChar {G : Type} [Group G] (χ : G → ℂ) : Prop :=
  ∃ (n : ℕ) (ρ : G →* GL (Fin n) ℂ), ∀ x, χ x = Matrix.trace (ρ x : Matrix (Fin n) (Fin n) ℂ)

def grIsIrrChar {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : Prop :=
  grIsChar χ ∧ grIp χ χ = (Fintype.card G : ℂ)

section
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def grUnipBlock (d a : ℕ) : Set (GL (Fin d) F) :=
  {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}

def grIsCuspChar {d : ℕ} (χ : GL (Fin d) F → ℂ) : Prop :=
  grIsIrrChar χ ∧ ∀ a, 0 < a → a < d →
    ∑ u : GL (Fin d) F, (open _root_.Classical in if u ∈ (grUnipBlock d a : Set (GL (Fin d) F)) then χ u else 0) = 0
end

variable {g : ℕ} [Fact g.Prime]

def grEllipticValues (teich : AlgebraicClosure (ZMod g) →* ℂ) {d : ℕ} (χ : GL (Fin d) (ZMod g) → ℂ) (k : ℕ) : Prop :=
  ∀ x : GL (Fin d) (ZMod g), Irreducible (Matrix.charpoly (x : Matrix (Fin d) (Fin d) (ZMod g))) →
    χ x = (-1) ^ (d - 1) *
      ((grRootsBar (Matrix.charpoly (x : Matrix (Fin d) (Fin d) (ZMod g)))).map fun α => teich α ^ k).sum

def grIsGenSys (ζ : ℕ → AlgebraicClosure (ZMod g)) : Prop :=
  ∀ d, 0 < d → orderOf (ζ d) = g ^ d - 1 ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = ζ d

def grLab (ζ : ℕ → AlgebraicClosure (ZMod g)) (d k : ℕ) : (ZMod g)[X] := minpoly (ZMod g) (ζ d ^ k)

end Formalism.D.Classical

namespace Formalism.D.Classical

def CuspidalCharExists : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (teich : AlgebraicClosure (ZMod g) →* ℂ) (ζ : ℕ → AlgebraicClosure (ZMod g)),
    (∀ x y : AlgebraicClosure (ZMod g), x ≠ 0 → y ≠ 0 → teich x = teich y → x = y) → grIsGenSys ζ →
    ∀ d k : ℕ, 0 < d → (grLab ζ d k).natDegree = d →
      ∃ χ : GL (Fin d) (ZMod g) → ℂ, grIsCuspChar χ ∧ grEllipticValues teich χ k

end Formalism.D.Classical
