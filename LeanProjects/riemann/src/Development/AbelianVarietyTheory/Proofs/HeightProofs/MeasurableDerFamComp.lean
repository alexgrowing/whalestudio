import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormSubLeOfDerivIcc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

namespace GlobalTheory.TypeSum

theorem measurable_derFam_comp (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ)
    (hF : GlobalTheory.TypeSum.IsDerFam ε F) (h0 : ContinuousOn (F []) (UJset ε)) :
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  intro l
  induction l with
  | nil =>
    intro _ T _ _ _ φ hφ hφU
    exact (h0.comp_continuous hφ hφU).measurable
  | cons X l ih =>
    intro hl T _ _ _ φ hφ hφU
    have hX : X ∈ lieSet ε := hl X (List.mem_cons_self ..)
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)

    let q : ℕ → T → ℂ := fun m t =>
      (((m : ℝ) + 1)⁻¹)⁻¹ • (F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X)) - F l (φ t))
    have hq : ∀ m, Measurable (q m) := by
      intro m
      have h1 : Measurable (fun t => F l (φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))) :=
        ih hl' T (fun t => φ t * NormedSpace.exp ((((m : ℝ) + 1)⁻¹) • X))
          (hφ.mul continuous_const) (fun t => mul_mem_UJ (hφU t) (exp_mem_UJ hX _))
      have h2 : Measurable (fun t => F l (φ t)) := ih hl' T φ hφ hφU
      exact (h1.sub h2).const_smul ((((m : ℝ) + 1)⁻¹)⁻¹ : ℝ)
    have hlim : ∀ t, Tendsto (fun m => q m t) atTop (𝓝 (F (X :: l) (φ t))) := by
      intro t
      have hd := hF l hl' X hX (φ t) (hφU t)
      have hs := hd.tendsto_slope_zero
      have hseq : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => ?_⟩
        · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; positivity
      have := hs.comp hseq
      refine this.congr fun m => ?_
      simp [q, Function.comp, zero_add]
    exact measurable_of_tendsto_metrizable hq (tendsto_pi_nhds.2 hlim)

end GlobalTheory.TypeSum
