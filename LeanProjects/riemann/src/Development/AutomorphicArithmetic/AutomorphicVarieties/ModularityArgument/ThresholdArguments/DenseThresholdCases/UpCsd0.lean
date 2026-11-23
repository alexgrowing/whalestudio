import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.IsIrrOfMatIrr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PolarizedAutomorphicOfAutP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private tf cyc_conj isIrr_of_matIrr matIrr_tw pair_of from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.IsIrrOfMatIrr
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
namespace UpperTheory.V.Th.End3
open UpperTheory.V.U3 UpperTheory.V.Base
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing
attribute [local instance] tf
theorem autCsd0_comp_galEmb_of_isPair_of_isIrr_of_isAut (hP : _root_.UpperTheory.V.Af.HypothesesH') (K L Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [IsCMField L]
    [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    [hsol : Group.IsSolvable (L ≃ₐ[K] L)] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (σ : G ℚ Ω) (hσ : Sd.IsCC σ) (hr : Continuous r) (P : GL (Fin n) (Qbar l))
    (hPr : Sd.IsPair σ r (cycBar K Ω l ^ (1 - (n : ℤ))) P) (hirr : Af.IsIrr (r.comp (galEmb K L Ω)))
    (haut : Af.IsAut ι r) : AutCsd0 ι (r.comp (galEmb K L Ω)) := by
  obtain ⟨j, hj⟩ := hσ
  haveI : IsAlgClosure K Ω := algClo K Ω
  haveI : IsAlgClosure L Ω := algClo L Ω
  haveI : IsAlgClosure (maximalRealSubfield K) Ω := algClo (maximalRealSubfield K) Ω
  let c : G (maximalRealSubfield K) Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap K Ω))
  have hc : Af.IsConjEl c := ⟨j, hj⟩
  have hpc : Af.IsPairing c r (cycBar K Ω l ^ (1 - (n : ℤ))) P := fun s s' hs =>
    hPr s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have halg : Af.IsAlgChar ι (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP (maximalRealSubfield K) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, 1 - (n : ℤ), 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  refine _root_.UpperTheory.GalN.V.csdOf0_alt hP ℚ L Ω inferInstance l ι n hn _ σ P ⟨j, hj⟩ ?_
    fun s s' hs => hPr (galEmb K L Ω s) (galEmb K L Ω s') hs
  refine (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida hP) (maximalRealSubfield K) K L Ω hsol
    ⟨inferInstance, Or.inr ⟨?_, inferInstance⟩⟩ inferInstance inferInstance
    l ι n hn r (cycBar (maximalRealSubfield K) Ω l ^ (1 - (n : ℤ))) hr hirr halg (fun a b ha hb => ?_) ⟨c, P, hc, ?_⟩).1 haut
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, cyc_conj l ha hb]
  · exact hpc
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {K L : Type} [Field K] [NumberField K]
  [IsCMField K] [Algebra K Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {σ : G ℚ Ω} {R : G ℚ Ω →* GG 3 (PadicAlgCl l)} {ρ : G K Ω →* GL (Fin 3) (Qbar l)}
end UpperTheory.V.Th.End3
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing
end
