import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_iso_of_compatible_abelianThickenings : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A) (v : ∀ e : ℕ, LB.Iso (P'.L.pull (fstG I e P'.A).left) (P.L.pull ((β e).hom.left ≫ (fstG I e P.A).left))), (∀ e, (v e).IsGen) → (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι), (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' → Geo.Tor.gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z j (fun _ => j') = Geo.Tor.gw (v e) r z j (fun _ => j')) → ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso P'.L (P.L.pull Φ.hom.left)), w.IsGen ∧ ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι), (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' → Geo.Tor.gw w (r ≫ (fstG I e P'.A).left) z j j' = Geo.Tor.gw (v e) r z j (fun _ => j') := by
  first | exact @GlobalTheory.exists_iso_of_compatible_thickenings | exact GlobalTheory.exists_iso_of_compatible_thickenings | (intros; apply GlobalTheory.exists_iso_of_compatible_thickenings <;> assumption)
