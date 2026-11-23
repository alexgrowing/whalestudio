import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TriFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def IsLocFr {A : Type} [CommRing A] (s : X ⟶ Sp A) (ε : 𝓞 E →+* A) {R : Type} [CommRing R] (x₀ : Sp R ⟶ X) {n : ℕ}
    (w : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∃ (N : ℕ) (e : Fin n ↪ Fin N) (u : Fin N → (Sp (DualNumber R) ⟶ t.G.left)), (∀ m, u (e m) = w m) ∧ IsTanBasis t x₀ u) ∧
  ∀ (R' : Type) [CommRing R'] (α : R →+* R') (ψ : A →+* R'), (spMap α ≫ x₀) ≫ s = spMap ψ →
    (∀ (m : Fin n) (c : 𝓞 E), (spMap (dualMap α) ≫ w m) ≫ (t.act.act c).left =
      spMap (epsMul (ψ (ε c))) ≫ spMap (dualMap α) ≫ w m) ∧
    ∀ w', IsTanAtG t (spMap α ≫ x₀) w' → (∀ c : 𝓞 E, w' ≫ (t.act.act c).left = spMap (epsMul (ψ (ε c))) ≫ w') →
      ∃! cf : Fin n → R', IsCombAtG t (spMap α ≫ x₀) (fun m => spMap (dualMap α) ≫ w m) cf w'

def IsTriOf {R : Type} [CommRing R] (x : Sp R ⟶ X) {n : ℕ} (u : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) (d : Fin n → R)
    (w : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  ∀ m, ∃ cf : Fin n → R, cf m = d m ∧ (∀ m', m < m' → cf m' = 0) ∧ IsCombAtG t x u cf (w m)

end GlobalTheory.TriFlag
