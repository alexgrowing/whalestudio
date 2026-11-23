import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem isProper_hom_of_relAmple {T : Scheme.{0}} {A : Over T} [GrpObj A] {B : LB A.left} (h : RelAmple A B) :
    IsProper A.hom := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (fun U : T.affineOpens => U.1)
    (iSup_affineOpens_eq_top T) fun U => ?_
  have h₁ := projProper _ _ _ (GlobalTheory.ProjSpace.isProjOver_morphismRestrict_of_relAmple h U.2)
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper) _ U.2.isoSpec.hom).1 h₁

theorem abOpen_of_isOpen_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → IsOpen (abLocus Z.G) → GlobalTheory.Models.AbOpen Z.G := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Z _ hO
  letI := Z.grp
  let W : M.Z.Opens := ⟨abLocus Z.G, hO⟩
  refine ⟨W, rfl, ?_⟩
  have h : IsProper (pullback.snd Z.G.hom W.ι) := isProper_hom_of_relAmple (Z.pol W le_rfl).1
  unfold morphismRestrict
  infer_instance

end GlobalTheory.ZH
