import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.FdFixed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.WeakPow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LocTw
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.IsIntegralOpUntw
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.ChiBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.varTrace :
    UpperTheory.Gal.InertialTypesAlt.G.VarTrace := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hP hW v w hv _ _ _ _ mF mE hmF hmE τ τ' hτ hτ' s I hs hI
  let μE : Measure (normOneGL E n) := Measure.haar
  obtain ⟨χ', ⟨z₀, hz'⟩, V, hV⟩ := Dp.exTwist E n μE P hn
  obtain ⟨hex, htw⟩ := T.powTwist F E
  obtain ⟨χ, hz⟩ := (hex z₀).1
  obtain ⟨hi, hi', h1⟩ := htw z₀ χ χ' hz hz'
  obtain ⟨-, -, -, hconj, -⟩ := h1 n hn
  have hone : ∀ u : PlacesOver E v, u = w := fun u =>
    ((T.places F E hp).2.2.2.1 v hv) w u
  have hW' := weakPow F E σ hσ hp n hn z₀ χ χ' hz hz' π P hW
  obtain ⟨⟨τ₁, hτ₁⟩, he⟩ := locTw F n hn π χ v τ hτ
  obtain ⟨⟨τ₁', hτ₁'⟩, he'⟩ := locTw E n hn P χ' w.1 τ' hτ'
  obtain ⟨e, heT⟩ := he τ₁ hτ₁
  obtain ⟨e', heT'⟩ := he' τ₁' hτ₁'
  obtain ⟨hfix, -⟩ := matchPow F E σ hσ hp n hn z₀ χ χ' hz hz' v w hone
  obtain ⟨-, hmatch⟩ := matchPow F E σ hσ hp n hn (-z₀) χ⁻¹ χ'⁻¹ hi hi' v w hone
  have hI₁ : ∀ g x, (e'.symm.trans (I.trans e')) (τ₁'.ρ g x) = τ₁'.ρ (s g) ((e'.symm.trans (I.trans e')) x) := by
    intro g x
    obtain ⟨y, rfl⟩ := e'.surjective x
    have a := heT' g y
    have b := heT' (s g) (I y)
    rw [hfix s hs g] at b
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← a, ← b, LinearEquiv.symm_apply_apply, map_smul, hI]
  obtain ⟨c, hc, H⟩ := core F E σ hσ hp n hn μE (π.twist χ) (P.twist χ') V hV
    (fun g => hconj P _ (hP g)) hW' v w hv mF mE hmF hmE τ₁ τ₁' hτ₁ hτ₁' s _ hs hI₁
  refine ⟨c, hc, fun φ f c₁ z hφ hf hM hsupp htr => ?_⟩
  have hcE : ∀ g, chiAt n χ'⁻¹ w.1 g * chiAt n χ' w.1 g = 1 := fun g => by
    rw [mul_comm]
    exact (chiBasic E n χ' w.1).2.1 g
  have hcF : ∀ g, chiAt n χ⁻¹ v g * chiAt n χ v g = 1 := fun g => by
    rw [mul_comm]
    exact (chiBasic F n χ v).2.1 g
  have eφ : (fun g => (φ g * chiAt n χ'⁻¹ w.1 g) * chiAt n χ' w.1 g) = φ := by
    funext g
    rw [mul_assoc, hcE, mul_one]
  have ef : (fun g => (f g * chiAt n χ⁻¹ v g) * chiAt n χ v g) = f := by
    funext g
    rw [mul_assoc, hcF, mul_one]
  have htr₁ : HasTrace mF τ₁.ρ (fun g => f g * chiAt n χ⁻¹ v g) z := by
    refine ((trTw _ mF _ τ τ₁ e heT _ z).1).1 ?_
    rw [ef]
    exact htr
  have hsupp₁ : ∀ g, f g * chiAt n χ⁻¹ v g ≠ 0 → g ∈ normSet E n v := fun g hg =>
    hsupp g (left_ne_zero_of_mul hg)
  have key := H (fun g => φ g * chiAt n χ'⁻¹ w.1 g) (fun g => f g * chiAt n χ⁻¹ v g) c₁ z
    ((chiBasic E n χ'⁻¹ w.1).2.2 φ hφ) ((chiBasic F n χ⁻¹ v).2.2 f hf) (hmatch c₁ φ f hM) hsupp₁ htr₁
  have := (((trTw _ mE _ τ' τ₁' e' heT' _ _).2 I).2 key)
  rwa [eφ] at this
