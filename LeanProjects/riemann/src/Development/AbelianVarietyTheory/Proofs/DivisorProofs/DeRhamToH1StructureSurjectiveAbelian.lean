import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem toH1O_surjective_of_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) := by
  intro hH R _ A _ g hab hdim
  rw [Category.comp_id]
  have hsm : Smooth A.hom := hab.smooth
  have hsep : IsSeparated A.hom := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact A.hom := by haveI := hab.proper; infer_instance
  have hcmp := GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.bijective_cechDeRhamComparison_degreeOne A.hom hsm hsep hqc
  have hsurj : Function.Surjective (GlobalTheory.CechDR.toHO1 A.hom) := (hH R A g hab hdim).2.2.2.2.1.2.2
  intro u
  obtain ⟨h, hh⟩ := hsurj (GlobalTheory.CechDR.cmpO A.hom u)
  obtain ⟨c, rfl⟩ := hcmp.2 h
  refine ⟨c, GlobalTheory.CechDR.cmpO_injective R A.left A.hom ?_⟩
  rw [← GlobalTheory.CechDR.structureSheaf_comparison_comm, hh]

end GlobalTheory.PtExt
