import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section
open scoped GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
namespace GlobalTheory.NormBelow
open GlobalTheory.UnitaryHeckeBaseChange

theorem ideleNorm_eq_found (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (AdeleRing (𝓞 E) E)ˣ) :
    ideleNorm E x = GroundTheory.Global.ideleNorm (maximalRealSubfield E) E x := by
  apply Units.ext
  obtain ⟨z, hz⟩ := (adeleEquiv (isCMExt_real E)).surjective (x : AdeleRing (𝓞 E) E)
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  have h2 : ∀ z, toAdele (maximalRealSubfield E) E z =
      GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft (maximalRealSubfield E) E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a l =>
      rw [toAdele_tmul, GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul]
      exact mul_comm _ _
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  change adeleNorm E (x : AdeleRing (𝓞 E) E) = _
  rw [GroundTheory.Global.coe_ideleNorm, ← hz, h]
  have h3 : adeleEquiv (isCMExt_real E) z = _ := h2 z
  rw [h3]
  exact (Algebra.norm_eq_of_algEquiv _ _).symm

theorem ideleNorm_localIdele (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (y : (w.adicCompletion E)ˣ) :
    ideleNorm E (localIdele E w y) = localIdele (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E)))
      (GroundTheory.LocalField.normUnits _ (w.adicCompletion E) y) := by
  rw [ideleNorm_eq_found]
  exact GroundTheory.Global.ideleNorm_finiteEmbedding (K := maximalRealSubfield E) w y

end GlobalTheory.NormBelow

namespace GlobalTheory.NormBelow
open GlobalTheory.UnitaryHeckeBaseChange

theorem unrAt_under_of_compNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)), ¬ GlobalTheory.UnitaryBC.IsSplitAt w →
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (compNorm E χ).UnrAt w →
    χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  intro E _ _ _ χ w _ hur hχ x hx
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 :=
    Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 (maximalRealSubfield E))
  haveI : w.asIdeal.LiesOver (w.under (𝓞 (maximalRealSubfield E))).asIdeal := ⟨rfl⟩
  have hxm : x ∈ (Submonoid.ofClass ((w.under (𝓞 (maximalRealSubfield E))).adicCompletionIntegers
      (maximalRealSubfield E))).units := by
    unfold IsUnitAt at hx
    refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  obtain ⟨y, hy, hyn⟩ := GroundTheory.Global.IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one _ w he hxm
  have hyu : IsUnitAt w y := by
    obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ _).1 hy
    have h1' := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1
    have h2' := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h2
    unfold IsUnitAt
    refine le_antisymm h1' ?_
    have e : Valued.v (y : w.adicCompletion E) * Valued.v ((y⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc (1 : _) = _ := e.symm
      _ ≤ Valued.v (y : w.adicCompletion E) := mul_le_of_le_one_right' h2'
  have key : χ.loc (w.under (𝓞 (maximalRealSubfield E))) x = (compNorm E χ).loc w y := by
    show χ.1 (localIdele _ _ x) = χ.1 (ideleNorm E (localIdele E w y))
    rw [ideleNorm_localIdele]
    congr 2
    apply Units.ext
    rw [GroundTheory.LocalField.coe_normUnits]
    exact hyn.symm
  rw [key]
  exact hχ y hyu

end GlobalTheory.NormBelow
