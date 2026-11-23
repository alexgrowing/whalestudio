import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.IsIntegralOpUntw
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LocTw
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.ChiBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.trEx :
    UpperTheory.Gal.InertialTypesAlt.G.TrEx := by
  intro K _ _ _ n hn π v _ _ m hm τ hτ f hf
  haveI := hm
  let μ : Measure (normOneGL K n) := Measure.haar
  obtain ⟨χ, -, V, hV⟩ := Dp.exTwist K n μ π hn
  obtain ⟨⟨τ₁, h₁⟩, htw⟩ := locTw K n hn π χ v τ hτ
  obtain ⟨e, he⟩ := htw τ₁ h₁
  have hocc : Occurs μ V v τ₁ :=
    (occursIff K n μ V hV.summand v τ₁).2 ((Dp.locIff K n μ (π.twist χ) V hV v τ₁).1 h₁)
  obtain ⟨-, -, h₃⟩ := occursBasics K n μ V v m hV.summand
  obtain ⟨z, hz⟩ := h₃ τ₁ hocc (fun g => f g * chiAt n χ⁻¹ v g) ((chiBasic K n χ⁻¹ v).2.2 f hf)
  have ht := (trTw _ m (chiAt n χ v) τ τ₁ e he (fun g => f g * chiAt n χ⁻¹ v g) z).1.2 hz
  have hfun : (fun g => f g * chiAt n χ⁻¹ v g * chiAt n χ v g) = f := by
    funext g
    have h := (chiBasic K n χ v).2.1 g
    rw [mul_assoc, mul_comm (chiAt n χ⁻¹ v g), h, mul_one]
  rw [hfun] at ht
  exact ⟨z, ht⟩
