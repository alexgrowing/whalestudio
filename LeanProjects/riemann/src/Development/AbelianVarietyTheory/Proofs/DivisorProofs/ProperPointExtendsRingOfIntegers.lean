import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet

namespace GlobalTheory.ProjPointExt

theorem exists_integral_extension : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp (𝓞 F)), IsProjOver s → ∀ (K : Type) [Field K] [NumberField K] (fK : F →+* K) (yK : Sp K ⟶ X), yK ≫ s = spMap (fK.comp (algebraMap (𝓞 F) F)) → ∃ xO : Sp (𝓞 K) ⟶ X, spMap (algebraMap (𝓞 K) K) ≫ xO = yK := by
  intro F _ _ X s hs K _ _ fK yK hy
  let jO : 𝓞 F →+* 𝓞 K := RingOfIntegers.mapRingHom fK
  have hring : (algebraMap (𝓞 K) K).comp jO = fK.comp (algebraMap (𝓞 F) F) := by
    ext x; rfl
  haveI : IsProper s := GlobalTheory.SchemeWords.isProper_of_isProjOver hs
  let X' : Over (Sp (𝓞 K)) := Over.mk (Limits.pullback.snd s (spMap jO))
  have hP : IsProper X'.hom := by
    show IsProper (Limits.pullback.snd s (spMap jO))
    infer_instance
  have hsq : yK ≫ s = spMap (algebraMap (𝓞 K) K) ≫ spMap jO := by
    rw [hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [hring]
  let x : Sp K ⟶ X'.left := Limits.pullback.lift _ _ hsq
  have hx : x ≫ X'.hom = Formalism.L2.Pj.abelian₂.gmap K := Limits.pullback.lift_snd _ _ _
  obtain ⟨t, ht⟩ := GlobalTheory.CuspFamilyCompare.exists_integral_point K X' hP x hx
  refine ⟨t.left ≫ Limits.pullback.fst _ _, ?_⟩
  have : x ≫ Limits.pullback.fst _ _ = yK := Limits.pullback.lift_fst _ _ _
  rw [← this, ht, Category.assoc]

end GlobalTheory.ProjPointExt
