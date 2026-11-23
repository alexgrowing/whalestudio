import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.DownCsdK
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAUpDownOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdThruL
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAIsoTwOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAAcrossOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.GalN.V UpperTheory.V.Z.Win
set_option linter.unusedVariables false
namespace UpperTheory.V.Z.Win.Dn
theorem isoTw_alt : _root_.UpperTheory.V.Z.Win.AIsoTwAlt := _root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws ImaginaryQuadraticEtaCharacter.winTw
theorem aUpDown_alt (H : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Win.AUpDownAlt :=
  _root_.UpperTheory.V.Z.Win.aUpDownOf_alt weakOfAtt flagLaws (thruAway plainRec) (_root_.UpperTheory.V.Z.Ord.thruL_alt H.toClassicalTheorems plainRec) ImaginaryQuadraticEtaCharacter.winUpDown ImaginaryQuadraticEtaCharacter.winOf
theorem aAcross_alt (H : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Win.AAcrossAlt := _root_.UpperTheory.V.Z.Win.a_across_of_statement flagLaws (_root_.UpperTheory.V.Z.Win.Dn.aUpDown_alt H) _root_.UpperTheory.V.Z.Win.Dn.isoTw_alt
theorem ends_rank_three_of_local (H : _root_.UpperTheory.V.Af.HypothesesH') : RowT := _root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal
local instance  (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
  (K : Type) [Field K] [NumberField K] [IsCMField F] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsGalois F K]
theorem automorphy_up_base_change (H : _root_.UpperTheory.V.Af.HypothesesH') (hs : Group.IsSolvable (K ≃ₐ[F] K)) (hn : 1 ≤ n) (hc : Continuous r)
    (hi : IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) (hp : Sol.Pol ι r) (ha : IsRegAlgAutomorphicAttached ι r) (hF : Flagged r)
    (h : WitA ι r) : WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
  (_root_.UpperTheory.V.Z.Win.Dn.aUpDown_alt H H (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local H) F K Ω hs l ι n hn r hc hi hp ha hF).1 h
theorem down'_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hs : Group.IsSolvable (K ≃ₐ[F] K)) (hn : 1 ≤ n) (hc : Continuous r)
    (hi : IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) (hp : Sol.Pol ι r) (ha : IsRegAlgAutomorphicAttached ι r) (hF : Flagged r)
    (hI : IneAb r) (hK : Keeps r K) (h : WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) : WitA ι r :=
  (_root_.UpperTheory.V.Z.Win.Dn.aUpDown_alt H H (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local H) F K Ω hs l ι n hn r hc hi hp ha hF).2 hI hK h
end
theorem across'_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    (hK : Module.finrank ℚ K = 2) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hs : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x)
    {r : G ℚ Ω →* GL (Fin n) (Qbar l)} (hc : Continuous r) (ha : IsAutomorphicOverImagQuad ι r) (hd : ∃ θ, IsAlgChar ι θ ∧ DualTw r θ) (hI : IneAb r)
    (hF : Flagged r) (hi : IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)))
    (h : WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) : WitAQ ι r :=
  _root_.UpperTheory.V.Z.Win.Dn.aAcross_alt H H (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local H) K Ω hK l ι n hn hs r hc ha hd hI hF hi h
theorem twist'_alt (P : _root_.UpperTheory.V.Af.Hypotheses') {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {μ : G F Ω →* (Qbar l)ˣ} (hμ : IsAlgChar ι μ)
    (hc : Continuous μ) (h : WitA ι r) : WitA ι (tw r μ) :=
  (_root_.UpperTheory.V.Z.Win.Dn.isoTw_alt P F Ω l ι n r h).2 μ hμ
def DownCsdKAlt : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (σ : G ℚ Ω), Sd.IsCC σ → Continuous r →
    (∃ P, Sd.IsPair σ r (cycBar K Ω l ^ (1 - (n : ℤ))) P) → IsIrr (r.comp (galEmb K L Ω)) →
    IneAb r → Flagged r → Keeps r L → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (r.comp (galEmb K L Ω)) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r
end UpperTheory.V.Z.Win.Dn
end
end
