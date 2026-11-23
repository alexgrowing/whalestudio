import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitComp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_integralSection_splitPlace_componentMap_cast {E : Type} [Field E] [NumberField E] [IsCMField E] (F1 : Subfield E)
    (hF : F1 = maximalRealSubfield E) (sp : SplitPlace E) :
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield E) → FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E,
      (∀ t, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E),
        sec t ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)}) ∧
      (∀ x ∈ AddSubgroup.closure {y | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F1, ∃ x : 𝓞 E, y = a ⊗ₜ[F1] (x : E)},
        sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield E)) ∧
      ∀ x : E, sp.proj (Formalism.IndefR.principalLevelFrame.tensCastR hF ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x)) = sp.i x := by
  classical
  subst hF
  have hc : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      Formalism.IndefR.principalLevelFrame.tensCastR (rfl : maximalRealSubfield E = maximalRealSubfield E)
        (a ⊗ₜ[maximalRealSubfield E] x) = x ⊗ₜ[maximalRealSubfield E] a := fun a x => rfl
  have hp : ∀ (a : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (x : E),
      sp.proj (x ⊗ₜ[maximalRealSubfield E] a) = sp.i x * a sp.v := fun a x => rfl
  refine ⟨fun t => singleV (maximalRealSubfield E) sp.v t ⊗ₜ[maximalRealSubfield E] (1 : E), ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hc, hp, map_one, one_mul]
    exact RestrictedProduct.single_eq_same _ _ _
  · intro t ht
    apply AddSubgroup.subset_closure
    refine ⟨singleV (maximalRealSubfield E) sp.v t, ?_, 1, by simp⟩
    intro w
    show (singleV (maximalRealSubfield E) sp.v t) w ∈ _
    by_cases h : w = sp.v
    · subst h
      have e : (singleV (maximalRealSubfield E) sp.v t) sp.v = t := RestrictedProduct.single_eq_same _ _ _
      rw [e]
      exact ht
    · have e : (singleV (maximalRealSubfield E) sp.v t) w = 0 := RestrictedProduct.single_eq_of_ne _ _ h
      rw [e]
      exact zero_mem _
  · intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, z, rfl⟩ := hy
      rw [hc, hp]
      refine mul_mem ?_ (ha sp.v)
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (sp.split_le_one z)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, map_add]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [map_neg, map_neg]
      exact neg_mem hy
  · intro x
    rw [hc, hp]
    show sp.i x * 1 = sp.i x
    exact mul_one _

theorem proj_tensCast_section : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) ∧
      (∀ x ∈ Formalism.L2.Theta.intAE D,
        sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) ∧
      ∀ x : D.host.E, sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x))) = sp.i x := by
  intro D sp hF
  obtain ⟨sec, h1, h2, h3, h4⟩ := exists_integralSection_splitPlace_componentMap_cast D.host.F hF sp
  refine ⟨sec, h1, h2, h3, fun x => ?_⟩
  have e : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
    simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  rw [e]
  exact h4 x

end GlobalTheory.SplitComp
