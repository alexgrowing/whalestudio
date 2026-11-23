import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

open Topology

theorem conjU_measurableEmbedding {D : D7} (S : HSp D) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    (c : D.host.E) (hJ : J = c • S.gram) : MeasurableEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) := by
  haveI : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  let κ : GL (Fin S.rank) (AE D) → GL (Fin S.rank) (AE D) := fun g => GeneralLinearGroup.map (cA D) g
  have hκc : Continuous κ := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact Units.continuous_val.matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
    · exact Units.continuous_coe_inv.matrix_map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conj D)
  have hκκ : Function.LeftInverse κ κ := fun g => by
    ext i j
    exact Formalism.L2.Theta.cA_cA _
  have hκe : IsEmbedding κ := hκκ.isEmbedding hκc hκc
  have hmat : IsEmbedding (matHom S) := IsEmbedding.subtypeVal
  have hcomp : (Subtype.val : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J → GL (Fin S.rank) (AE D)) ∘ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ =
      κ ∘ matHom S := rfl
  have hemb : IsEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) := by
    refine ⟨IsInducing.of_comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU S c hJ) continuous_subtype_val ?_, ?_⟩
    · rw [hcomp]; exact (hκe.comp hmat).isInducing
    · intro a b hab
      apply (hκe.comp hmat).injective
      rw [← hcomp]
      exact congrArg Subtype.val hab
  refine hemb.measurableEmbedding ?_
  have hrange : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) =
      (κ ∘ Subtype.val) ⁻¹' (HR (AF D.host.F) D.sp.cm.sig S.gram : Set (GL (Fin S.rank) (AE D))) := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      show κ (κ (matHom S g)) ∈ (HR (AF D.host.F) D.sp.cm.sig S.gram : Set (GL (Fin S.rank) (AE D)))
      rw [hκκ]
      exact g.2
    · intro hy
      refine ⟨(⟨κ y.1, hy⟩ : HR (AF D.host.F) D.sp.cm.sig S.gram), Subtype.ext ?_⟩
      exact hκκ y.1
  rw [hrange]
  exact ((PI.AdicCompletionValuation.isClosed_HR _ _ _).preimage (hκc.comp continuous_subtype_val)).measurableSet

theorem thetaInt_eq_modelI : ∀ (D : D7) (S X : HSp D) (d : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Wd) (c : D.host.E)
    (hJ : Y.J = c • S.gram)
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (ω : WRep S X) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Wd)
    (κ : GA D X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
    M.μ = ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ) → M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕 →
    (∀ g h, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ g) (κ h) = thetaKO ω g h f) →
    ∀ h, thetaInt ω ν 𝓕 f h = M.I om Φ (κ h) := by
  intro D S X d Y Wd M c hJ ν 𝓕 ω om κ Φ f hμ hdom hθ h
  have he := conjU_measurableEmbedding S c hJ
  rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.I, hμ, hdom, he.restrict_map, Set.preimage_image_eq _ he.injective, he.integral_map]
  simp only [hθ]
  rfl

end GlobalTheory.SquareAgree
