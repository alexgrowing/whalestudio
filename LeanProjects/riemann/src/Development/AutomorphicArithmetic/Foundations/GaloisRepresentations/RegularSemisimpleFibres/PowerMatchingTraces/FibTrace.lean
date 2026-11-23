import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LocTw
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.IsIntegralOpUntw
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursIff
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.fibTrace :
    UpperTheory.Gal.InertialTypesAlt.G.FibTrace := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ π P V Λ t hC hAt hW V₀ Λ₀ t₀ hS hAt₀ hΛ ht v _ m τ τ₀ hτ hO f z hf hz
  obtain ⟨π₀, hπ₀, -⟩ := Dp.exCusp F n μF V₀ hS
  obtain ⟨-, -, hcl, -⟩ := T.carryLift F E σ hσ hp n hn μE μF
  have hl := hcl π₀ P V₀ V Λ₀ t₀ Λ t hπ₀ hC hAt₀ hAt hΛ ht
  obtain ⟨η, hη, hiso⟩ := (R.fibre_holds F E hp n hn (.cx π₀) (.cx P) hl.1).2 (.cx π) hW
  have he : π₀.twist η = π := (Dp.isoEq F n _ _).1 hiso
  subst he
  have hτ₀ : (Cusp.cx π₀).locComp v τ₀ :=
    ((Dp.locIff F n μF π₀ V₀ hπ₀ v τ₀).trans (occursIff F n μF V₀ hπ₀.summand v τ₀).symm).2 hO
  obtain ⟨e, hTw⟩ := (locTw F n hn π₀ η v τ₀ hτ₀).2 τ hτ
  have hfe : (fun g => f g * chiAt n η v g) = f := by
    funext g
    by_cases h0 : f g = 0
    · simp [h0]
    · have h1 : chiAt n η v g = 1 := by
        rcases hη with rfl | hη
        · rfl
        · simp only [chiAt]
          rw [(hf g h0) η hη]
          rfl
      rw [h1, mul_one]
  have h := ((trTw (Gw n v) m (chiAt n η v) τ₀ τ e hTw f z).1).2 hz
  rwa [hfe] at h
