import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemTest
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormDiag
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open UpperTheory.Gal.InertialTypesAlt.L

theorem UpperTheory.Gal.InertialTypesAlt.L.elemPair :
    UpperTheory.Gal.InertialTypesAlt.L.ElemPair := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp v w hw inst8 _ _ _ hmap n r hr0 hr1
  obtain ⟨x0, _, _, _, s, hs, hfin, hinc, hgal, -⟩ :=
    UpperTheory.V.Z.Tf.Orb.placeData_holds F E σ hσ v w hw
  have hx : x0 = inst8 := Algebra.algebra_ext _ _ fun a => (hinc a).symm.trans (hmap a)
  subst hx
  obtain ⟨⟨mE0, bE, mF0, bF, mE, mF, hmE, hmF, h1, h2⟩, hone⟩ := UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v
  letI : MeasurableSpace (GL (Fin n) (HeightOneSpectrum.adicCompletion E w.1)) := borel _
  haveI : BorelSpace (GL (Fin n) (HeightOneSpectrum.adicCompletion E w.1)) := ⟨rfl⟩
  obtain ⟨hμE, k2⟩ :=
    UpperTheory.V.Z.Tf.Orb.placeOfLocal_holds F E σ hσ v w hw s hs hfin hinc hgal n mE mF hmE hmF
  obtain ⟨r₀, hr₀0, hr₀1, hr₀⟩ := UpperTheory.Gal.InertialTypesAlt.L.elemLoc _ _ s hs n _ mF hμE hmF r hr0 hr1
  refine ⟨r₀, hr₀0, hr₀1, fun r' hr' hr'0 => ?_⟩
  obtain ⟨hsurj, c, hc0, hc⟩ := hr₀ r' hr' hr'0
  refine ⟨hsurj, c, hc0, fun t ht => ?_⟩
  have hr'1 : r' < 1 := lt_of_le_of_lt hr' hr₀1
  have hT1 := UpperTheory.Gal.InertialTypesAlt.L.elemTest _ n r hr0 hr1 {t} isCompact_singleton
  have hcpt := ((UpperTheory.Gal.InertialTypesAlt.L.normDiag _ _ s hs n).2.2 r hr1 t ht).2
  have hT2 := UpperTheory.Gal.InertialTypesAlt.L.elemTest _ n r' hr'0 hr'1 _ hcpt
  refine ⟨hT1.2.2.1, hT2.2.2.1, ?_, ?_⟩
  · apply UpperTheory.Gal.InertialTypesAlt.L.matchSmul F E σ n v _ (by exact_mod_cast hc0.ne')
    apply hone mE mF hmE hmF h1 h2
    exact k2 _ hT1.2.2.2.1 _ (Submodule.smul_mem _ _ hT2.2.2.2.1) (hc t ht)
  · intro g hg η hη
    obtain ⟨t', ⟨u, -, rfl⟩, x, hx, hdet⟩ := hT2.2.2.2.2 g hg
    obtain ⟨y, -, hy⟩ := hsurj x hx
    have hy' : x = Units.map (Algebra.norm (HeightOneSpectrum.adicCompletion F v)) y := Units.ext hy
    have hprod : (∏ i, nrmT (HeightOneSpectrum.adicCompletion F v) (t * u) i) =
        Units.map (Algebra.norm (HeightOneSpectrum.adicCompletion F v)) (∏ i, (t * u) i) := by
      simp only [nrmT, map_prod]
    rw [hdet, hprod, hy', ← map_mul]
    exact UpperTheory.Gal.InertialTypesAlt.L.normLoc F E σ hσ hp v w hw hmap η hη _
