import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkMapInjectiveBirational
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_map_injective_birational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ z : Z.X, Function.Injective (π.stalkMap z).hom ∧ ∀ b : Z.X.presheaf.stalk z, ∃ a s : X.X.presheaf.stalk (π z), (π.stalkMap z).hom s ≠ 0 ∧ (π.stalkMap z).hom s * b = (π.stalkMap z).hom a := by
  first | exact @GlobalTheory.ChartBir.stalkMap_birational | exact GlobalTheory.ChartBir.stalkMap_birational | (intros; apply GlobalTheory.ChartBir.stalkMap_birational <;> assumption)
