import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeIntEmbEmbP
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayExist

def SpansAt {X : Scheme.{0}} (G : Over X) (L : LB G.left) {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (k : ℕ) : Prop :=
  ∀ s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (Over.mk x0) G).left) fun _ => (k : ℤ)),
    ∃ (N : ℕ) (c : Fin N → S) (σ : Fin N → H0 L k), ∀ y J, Good L y J → sval s (𝟙 _) y J =
      ∑ i, gs (fst (Over.mk x0) G).left y ⊤ (toΓ S (c i)) * sval (σ i) (snd (Over.mk x0) G).left y J

def VanMod {R : Type} [CommRing R] (I : Ideal R) (l : ℕ) (Z : Over (Sp R)) {B : Scheme.{0}} {L : LB B} {K : Type}
    [Fintype K] {φ : K → (Z.left ⟶ B)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (T : Scheme.{0}) (r : T ⟶ Z.left) (t : T ⟶ Sp (R ⧸ I ^ (l + 1))), r ≫ Z.hom = t ≫ thick R I l →
    ∀ y J, Good L y J → sval s r y J = 0

end GlobalTheory.RayExist
