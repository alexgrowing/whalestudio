import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LocTw
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPow
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocGalEx
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursIff

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.G

theorem varEx : VarEx := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn P hP v w hv
  let μE : Measure (normOneGL E n) := Measure.haar
  let μF : Measure (normOneGL F n) := Measure.haar
  obtain ⟨hw, s, hs, hloc⟩ := locGalEx F E σ hp n v w hv
  refine ⟨s, hs, fun τ' hτ' => ?_⟩
  obtain ⟨χ', ⟨z, hz'⟩, V, hV⟩ := Dp.exTwist E n μE P hn
  obtain ⟨hex, htw⟩ := T.powTwist F E
  obtain ⟨χ, hz⟩ := (hex z).1
  obtain ⟨-, -, h1⟩ := htw z χ χ' hz hz'
  obtain ⟨-, -, -, hconj, -⟩ := h1 n hn
  obtain ⟨-, -, -, -, -, θ, hθ, hst⟩ := T.carryLift F E σ hσ hp n hn μE μF
  have hstab := (hst _ V hV).1 fun g => hconj P _ (hP g)
  obtain ⟨⟨τ₁, hτ₁⟩, hall⟩ := locTw E n hn P χ' w.1 τ' hτ'
  obtain ⟨e, he⟩ := hall τ₁ hτ₁
  have hocc : Occurs μE V w.1 τ₁ :=
    (occursIff E n μE V hV.summand w.1 τ₁).2 ((Dp.locIff E n μE _ V hV w.1 τ₁).1 hτ₁)
  obtain ⟨I₁, hI₁⟩ := (hloc μE θ hθ).2 V τ₁ hV.summand hstab hocc
  have hχ : ∀ g, chiAt n χ' w.1 (s g) = chiAt n χ' w.1 g :=
    (matchPow F E σ hσ hp n hn z χ χ' hz hz' v w hw).1 (s : Gw n w.1 →* Gw n w.1) hs
  have hne : ∀ g, chiAt n χ' w.1 g ≠ 0 := fun g => Units.ne_zero _
  refine ⟨e.trans (I₁.trans e.symm), fun g x => ?_⟩
  have h2 : e (τ'.ρ g x) = (chiAt n χ' w.1 g)⁻¹ • τ₁.ρ g (e x) := by
    rw [← he g x, map_smul, smul_smul, inv_mul_cancel₀ (hne g), one_smul]
  have h3 : τ₁.ρ (s g) (I₁ (e x)) = chiAt n χ' w.1 (s g) • e (τ'.ρ (s g) (e.symm (I₁ (e x)))) := by
    rw [← map_smul, he (s g) (e.symm (I₁ (e x))), e.apply_symm_apply]
  simp only [LinearEquiv.trans_apply]
  rw [h2, map_smul, hI₁, h3, smul_smul, hχ g, inv_mul_cancel₀ (hne g), one_smul, e.symm_apply_apply]

end UpperTheory.Gal.InertialTypesAlt.G
