import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatV

abbrev bo (R : Type) [CommRing R] (f : R) : (Sp R).affineOpens :=
  (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f)

abbrev resV (R : Type) [CommRing R] (f : R) : R →+* Γ(Sp R, (bo R f).1) :=
  ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

abbrev cst {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) : Γ(X, V) →+* Γ(Y, O) :=
  (π.appLE V O h).hom

def opV {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {n : ℕ} (dd : Fin n → Fld Y) (Θ : Matrix (Fin n) (Fin n) Γ(X, V))
    (u : Fin n → Γ(X, V)) (d : Fld Y) {W : Y.Opens} (p p' : Γ(Y, W)) (k : ℕ) (O : Y.Opens) (h : O ≤ π ⁻¹ᵁ V)
    (f : Γ(Y, O)) : Γ(Y, O) :=
  2 * (k : Γ(Y, O)) * d O f - ∑ a, ∑ b, cst π V h (Θ a b) * dd a O (dd b O f) +
    2 * ∑ a, cst π V h (u a) * dd a O f + (2 * (k : Γ(Y, O)) ^ 2 * rsT p O + 2 * (k : Γ(Y, O)) * rsT p' O) * f

end GlobalTheory.HeatV
