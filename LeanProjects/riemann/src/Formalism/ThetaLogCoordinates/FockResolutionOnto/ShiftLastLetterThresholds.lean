import Formalism.MahlerMeasure.StatementTM

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset

def setLast {K : ℕ} (LL : Letters (K + 1)) (o : ℕ) : Letters (K + 1) where
  vec := LL.vec
  deg := Function.update LL.deg (Fin.last K) o

def shiftLastLetterThresholds (K : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (e : ℕ) : Fin q → WithTop ℤ :=
  fun k => if K + 1 ≤ J k then M k + ((-(e : ℤ) : ℤ) : WithTop ℤ) else M k

def shiftWt {r : ℕ} (w : Fin r → ℤ) (ρ : Fin r) (e : ℕ) : Fin r → ℤ :=
  Function.update w ρ (w ρ - e)

noncomputable def FreeOf (p : ℕ) [Fact p.Prime] {σ : Type} (v : σ) : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p] {m | m v = 0}

noncomputable def TypesLE (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (M : WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (la : Fin r → ℤ) (_ : ((la 0 : ℤ) : WithTop ℤ) ≤ M), IsoC p LL j Cs la

noncomputable def XSp (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  Pol p r LL ⊓ FreeOf p (Fin.last K, ρ) ⊓
    ⨅ k, (if K + 1 ≤ J k then YCond p LL K (M k) ⊓ TypesLE p LL (K + 1) (univ.erase ρ) (M k)
      else YCond p LL (J k) (M k))

noncomputable def XH (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  XSp p LL J M ρ ⊓ HWC p LL (K + 1) (univ.erase ρ) w ⊓ WtSpC p LL (K + 1) univ w

def ResOntoK (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Prop :=
  ∀ x ∈ XSp p LL J M ρ, ∃ h ∈ Y p LL J M, initPart (Fin.last K, ρ) 0 h = x

def ResSat (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Prop :=
  ∀ x ∈ XSp p LL J M ρ, x ∈ IntPol p (Fin (K + 1) × Fin r) →
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧ initPart (Fin.last K, ρ) 0 h = x

def DivModP (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) : Prop :=
  ∀ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) →
    ∀ a ∈ IntPol p (Fin (K + 1) × Fin r), ∀ b ∈ IntPol p (Fin (K + 1) × Fin r),
      h = X (Fin.last K, ρ) * a + (p : ℚ_[p]) • b →
      ∃ h₁ ∈ IntPol p (Fin (K + 1) × Fin r), ∃ b' ∈ IntPol p (Fin (K + 1) × Fin r),
        X (Fin.last K, ρ) * h₁ ∈ Y p LL J M ∧ h = X (Fin.last K, ρ) * h₁ + (p : ℚ_[p]) • b'

noncomputable def grSpan (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ) :
    Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  Submodule.span ℚ_[p] (grLat p LLw J M ρ w (Fin.last K, ρ) e : Set (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]))

def ProjAt (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e D : ℕ) : Prop :=
  ∃ Pr : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
    ∀ m : Fin (K + 1) × Fin r →₀ ℕ, MultiDeg LLw m →
      Pr (monomial m 1) ∈ grSpan p LLw J M ρ w e ∧
      ((p : ℚ_[p]) ^ D) • Pr (monomial m 1) ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      ∀ g ∈ grSpan p LLw J M ρ w e, fock p g (Pr (monomial m 1)) = fock p g (monomial m 1)

def SatAt (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e c : ℕ) : Prop :=
  ∀ x ∈ grSpan p LLw J M ρ w e, x ∈ IntPol p (Fin (K + 1) × Fin r) →
    ((p : ℚ_[p]) ^ c) • x ∈ grLat p LLw J M ρ w (Fin.last K, ρ) e

end Formalism.InvariantFactorPaths.L4
