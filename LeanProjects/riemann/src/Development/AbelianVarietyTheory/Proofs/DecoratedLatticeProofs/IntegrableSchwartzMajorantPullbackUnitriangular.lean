import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalShStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarAdelicUpperUnitriangularEntryTranslateInvariStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
namespace GlobalTheory.Unf

theorem pull_integrable : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m ρ : ℕ) (vU : VolU D ρ) (x : Matrix (Fin m) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∃ N : ℕ, ∀ K : Set (Mx D m ρ), IsCompact K → Integrable (fun u : UX D ρ => maj θ K N ((rat x : Mx D m ρ) ⬝ u.1.1)) vU.ν := by
  intro D θ hθ m ρ vU x hx
  have hH : vU.ν.IsHaarMeasure := vU.unit.1
  obtain ⟨hf, hfin, hinv⟩ := GlobalTheory.T.haar_adelicUpperUnitriangular_entry_translate_invariant D ρ vU.ν hH
  have hae : ∀ᵐ y ∂(Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) vU.ν), ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j := by
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
    have hS : MeasurableSet {y : Mx D ρ ρ | ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j} := by
      have hc : IsClosed {y : Mx D ρ ρ | ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
      exact hc.measurableSet
    rw [ae_map_iff hf.aemeasurable hS]
    refine ae_of_all _ fun u i j hij => ?_
    have hU := (GlobalTheory.UniIndexPrime.mem_uniSub u.1).1 u.2
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [Matrix.one_apply_ne h.ne']
      exact hU.1 i j h
    · subst h
      rw [Matrix.one_apply_eq]
      exact hU.2 _
  obtain ⟨N, hN⟩ := GlobalTheory.T.integrable_majorant_coordinate_coset_measure D θ hθ ρ ρ (fun i j => i < j) 1 _ hfin hae hinv
  obtain ⟨hmaj, hmove⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ
  refine ⟨N, fun K hK => ?_⟩
  obtain ⟨K', hK', hb⟩ := hmove m ρ ρ x hx K hK
  obtain ⟨C, hC⟩ := hb N
  have h1 : Integrable (maj θ K' N) (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) vU.ν) := hN K' hK'
  have h2 : Integrable (fun u : UX D ρ => maj θ K' N (u.1.1 : Mx D ρ ρ)) vU.ν :=
    (integrable_map_measure ((hmaj ρ ρ K' hK').2.2.1 N).aestronglyMeasurable hf.aemeasurable).1 h1
  have hmul : Measurable (fun y : Mx D ρ ρ => (rat x : Mx D m ρ) ⬝ y) := by
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : BorelSpace (Mx D m ρ) := ⟨rfl⟩
    exact (continuous_const.matrix_mul continuous_id).measurable
  refine (h2.const_mul C).mono' (((hmaj m ρ K hK).2.2.1 N).comp (hmul.comp hf)).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (maj_nonneg θ K N _)]
  exact hC _

end GlobalTheory.Unf
