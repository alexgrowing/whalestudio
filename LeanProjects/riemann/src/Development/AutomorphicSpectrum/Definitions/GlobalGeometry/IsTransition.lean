import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def tauE {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : E →+* c.F := (τ.codRestrict c.F.toSubfield (c.conj τ) :)

def IsLocBasis (O : Type) [CommRing O] {M : Type} [AddCommGroup M] [Module O M] (p : ℕ) {I : Type} (x : I → M) : Prop :=
  LinearIndependent O x ∧ ∃ n : ℕ, ¬ p ∣ n ∧ ∀ y, n • y ∈ Submodule.span O (Set.range x)

def gramE (D : Datum H) {I : Type} (x : I → D.La) : Matrix I I E := Matrix.of fun m n => sesq D (x m) (x n)

def IsTransition (D : Datum H) {I : Type} [Fintype I] (x e : I → D.La) (T : Matrix I I E) : Prop :=
  ∀ m y, sesq D (x m) y = ∑ n, T m n * sesq D (e n) y

def sgnRt (H : Host E) (b : Bool) : ℂ := if b then H.rt0 else -H.rt0

def IsPure {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {p q : ℕ}
    (x : Fin p ⊕ Fin q → D.La) : Prop :=
  (∀ a, x (.inl a) ∈ PureType.lat hP (sgnRt H true)) ∧ ∀ j, x (.inr j) ∈ PureType.lat hP (sgnRt H false)

end GlobalTheory.CompanionTheory.Ar.Fl
