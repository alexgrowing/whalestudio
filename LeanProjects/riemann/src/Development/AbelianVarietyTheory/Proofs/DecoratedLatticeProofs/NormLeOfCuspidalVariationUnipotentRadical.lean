import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspGeo

theorem norm_le_of_unipRad_variation : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → IsCuspFun V φ →
    ∀ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ → ∀ (g : GA D V) (e : ℝ),
      (∀ m ∈ NI V C₀, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  intro D V φ hφ hcusp r C₀ hC g e he
  set 𝔉 := GlobalTheory.Cusp.frameFlag hC with h𝔉
  have hc : GlobalTheory.Cusp.Cocompact (GQ V) (GlobalTheory.Cusp.NA 𝔉) := GlobalTheory.Cusp.cocompact_single _
  have hP := hc.isProbabilityMeasure
  have h0 : GlobalTheory.Cusp.constTerm 𝔉 φ g = 0 :=
    congrFun ((GlobalTheory.Cusp.isCuspFun_iff hφ.left).1 hcusp _ _) g
  have hI := hc.integrable hφ.left hφ.cont g
  have hmem : ∀ n : GlobalTheory.Cusp.NA 𝔉, (n : GA D V) ∈ NI V C₀ := fun n => by
    exact (SetLike.ext_iff.1 (GlobalTheory.Cusp.NA_frameFlag hC) _).1 n.2
  have key : φ g = ∫ q, (φ g - φ ((q.out : GlobalTheory.Cusp.NA 𝔉) * g)) ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA 𝔉) := by
    rw [integral_sub (integrable_const _) hI]
    have h0' : ∫ q, φ ((q.out : GlobalTheory.Cusp.NA 𝔉) * g) ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA 𝔉) = 0 := h0
    rw [h0', integral_const]
    simp
  rw [key]
  have hb := norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA 𝔉))
    (f := fun q => φ g - φ ((q.out : GlobalTheory.Cusp.NA 𝔉) * g)) (C := e)
    (.of_forall fun q => by rw [norm_sub_rev]; exact he _ (hmem _))
  simpa using hb

end GlobalTheory.CuspGeo
