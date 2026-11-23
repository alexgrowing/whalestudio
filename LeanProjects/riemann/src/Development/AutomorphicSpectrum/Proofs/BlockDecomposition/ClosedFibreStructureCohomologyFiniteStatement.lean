import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedFibreStructureCohomologyFinite
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_fibre_structure_cohomology_finite : FlatBCSt → ∀ (k : Type) [Field k] (A : Over (Sp k)) [IsSeparated A.hom] [QuasiCompact A.hom], Module.Finite k (HO1 A.hom) → ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : Sp R ⟶ Sp k) (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ (A ⊗ Over.mk t).left), IsPullback φ s' (snd A (Over.mk t)).left (spMap (algebraMap R (IsLocalRing.ResidueField R))) → Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧ Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ Module.finrank k (HO1 A.hom) := by
  first | exact @GlobalTheory.CompanionTheory.FlatFibre.closed_fibre_first_cohomology_finite | exact GlobalTheory.CompanionTheory.FlatFibre.closed_fibre_first_cohomology_finite | (intros; apply GlobalTheory.CompanionTheory.FlatFibre.closed_fibre_first_cohomology_finite <;> assumption)
