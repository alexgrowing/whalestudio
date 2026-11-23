import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

theorem UpperTheory.Gal.KunnethLefschetz.Di.rootNat_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.RootNat := by
  intro q _ i V U g ζ
  have hroot := (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.2
  have hnat := (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) U).2.2.2.1 g (twGen i ζ)
  have hres := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 V U g ζ
  rw [hroot i U ζ, hroot i V (ζ.map g.appTop.hom), ← hres]
  exact hnat
