import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X)

def Pres (p : ℕ) (b : Bool) {g M : ℕ} (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left))
    (h : Fin (M + 1) → Fin g → R) : Prop :=
  (∃ N : ℕ, ∀ i, Pi.single i ((p : R) ^ N) ∈ Submodule.span R (Set.range h)) ∧
  ∀ (C : SCF p) (φ : R →+* ↥(intO ↥C.S)) (cf : Fin g → ↥C.S) (w : Sp (DualNumber ↥C.S) ⟶ t.G.left),
    IsCombAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x)
      (fun i => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ e i) cf w →
    (w ∈ lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b ↔ ∀ j, ‖∑ i, ((φ (h j i) : ↥(intO ↥C.S)) : ↥C.S) * cf i‖ ≤ 1)

end Lattice

section Ratio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def RatioAt (Z : Mdl Y i₀) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (U : Z.X.Opens) {m m' : ℕ} (A : Fin m → Γ(Z.X, U))
    (B : Fin m' → Γ(Z.X, U)) : Prop :=
  (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range A)).radical ∧ (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range B)).radical ∧
  ∀ (y : Z.Pt) a (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen → ⊤ ≤ y.z ⁻¹ᵁ U →
    lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p true st - lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p false st =
      Real.log ‖fun j => valF y.gen U (A j)‖ - Real.log ‖fun j => valF y.gen U (B j)‖

def HasRatio (Z : Mdl Y i₀) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : Prop :=
  ∀ z : Z.X, ∃ (U : Z.X.Opens) (m m' : ℕ) (A : Fin m → Γ(Z.X, U)) (B : Fin m' → Γ(Z.X, U)),
    z ∈ U ∧ IsAffineOpen U ∧ RatioAt Z st U A B

def HasPRatio (Z : Mdl Y i₀) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : Prop :=
  ∀ z : Z.X, ∃ (U : Z.X.Opens) (A B : Γ(Z.X, U)), z ∈ U ∧ IsAffineOpen U ∧ RatioAt Z st U ![A] ![B]

end Ratio

end GlobalTheory.HTLine
