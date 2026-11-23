import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

def IsPlaceRing (E : Type) [Field E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (R : Subring ℂ) : Prop :=
  IsDiscreteValuationRing R ∧ (∀ x ∈ R, Sz l lam 0 x) ∧ (∀ q : ℚ, 0 ≤ padicValRat l q → (q : ℂ) ∈ R) ∧
    ∀ (σ : E →+* ℂ) (x : E), ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ σ x * b = a

variable {E : Type} [Field E] [NumberField E] {I : Type} {𝔠 : FracId (FR E)} {R : Subring ℂ}

def IsPeriodGen (X₀ : Obj (FR E) 𝔠 (Sp R)) {φ : I → E →+* ℂ} {L : Set E} {X : Obj (FR E) 𝔠 (Sp ℂ)} (U : Unif φ L 0 X)
    (p : X.A.left ⟶ X₀.A.left) (i : I) (e : X₀.Lie →ₗ[R] R) (a : ℂ) : Prop :=
  ∀ (v : X₀.Lie) (v' : X.Lie) (W : Fin (Module.finrank ℚ (FR E)) → ℂ), Obj.LieCorr R.subtype p v v' → U.u.IsDiff W v'.hom →
    ((e v : R) : ℂ) = a * W (U.e.symm i)

def HasLatModel [IsCMField E] (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ) (l : ℕ) [Fact l.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (r : ℝ) (Ω : ℂ) : Prop :=
  ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsPlaceRing E l lam R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ))
    (U : Unif φ (lattice c y) 0 X) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A),
    X.IsPullBy X₀ (spMap R.subtype) p ∧
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) ∧
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
      ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) ∧
    ∀ i, ∃ (e : X₀.Lie →ₗ[R] R) (a : ℂ), a ≠ 0 ∧ Sz l lam r (a / Ω) ∧ IsPeriodGen X₀ U p i e a ∧
      ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e

end GlobalTheory.LatModel
