import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbPartTorus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev torTriple (H : Host E) (K : Type) [Field K] : SAB H (Sp K) :=
  GlobalTheory.Models.Inhab.trivTriple H (splitTorus (Sp K) (𝓞 E)) (GlobalTheory.Diag.isSemiAbelian _ _) (GlobalTheory.Diag.diagAct _ _ _)

def torExt (E : Type) [Field E] [NumberField E] (K : Type) [Field K] : TorusExtension (splitTorus (Sp K) (𝓞 E)) :=
  torusExtOfIso (GlobalTheory.Diag.baseChangeIso (𝟙 (Sp K)) (𝓞 E)) (GlobalTheory.Diag.torusExtension (Sp K) (𝓞 E) (𝟙 (Sp K)))

def abPartTorus (H : Host E) (K : Type) [Field K] : GlobalTheory.CompanionTheory.Ar.AbPart (torTriple H K) (𝟙 (Sp K)) where
  tK := torTriple H K
  m := (GlobalTheory.ObjMaps.exists_sab_id (torTriple H K)).choose
  τ := torExt E K
  tB := GlobalTheory.Models.Inhab.zeroTriple H (Sp K)
  e := Iso.refl _
  e_hom := by
    let := (torExt E K).grpB
    exact ⟨toUnit_unique _ _, toUnit_unique _ _⟩
  act a := toUnit_unique _ _
  pp := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _ (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (fun _ _ => rfl))⟩

attribute [local instance] TorusExtension.addCommGroup

end GlobalTheory.CompanionTheory.Ar.AbPartTorus
