import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNatMulIsIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNatMulMemRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormNatCastAdicCompletionLeOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNatMulNormLeOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormNatCastLe
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothForms

theorem denom_norm_natCast_le_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one
  | exact _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one
  | (apply _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicNatCastNorm.norm_natCast_adicCompletion_le_one ..)

theorem denom_global {F : Type} [Field F] [NumberField F] (H : HeightOneSpectrum (𝓞 F) → NNReal)
    (hH : ∀ v, 1 ≤ H v) (hf : (Function.mulSupport H).Finite) :
    ∃ d : ℕ, 0 < d ∧ (d : NNReal) ≤ ∏ᶠ v, H v ∧
      ∀ v, ∀ y : v.adicCompletion F, ‖y‖₊ ≤ H v → ‖(d : v.adicCompletion F) * y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator
  | exact _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator
  | (apply _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicNormZpowEstimates.exists_denominator ..)

theorem denom_exists_int {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ k : ℕ, 0 < k ∧ ∃ r : 𝓞 E, (r : E) = k * e := by
  first
  | exact @_root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers
  | exact _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers
  | (apply _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulMemRingOfIntegers.exists_nat_mul_mem_ringOfIntegers ..)

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies Formalism.L2.Pj in

theorem denomBound : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    DenomBound θ V := by
  first
  | exact @_root_.GlobalTheory.AdeleDenominators.denomBound
  | exact _root_.GlobalTheory.AdeleDenominators.denomBound
  | (apply _root_.GlobalTheory.AdeleDenominators.denomBound <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdeleDenominators.denomBound <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdeleDenominators.denomBound <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdeleDenominators.denomBound ..)

end GlobalTheory.SmoothForms
