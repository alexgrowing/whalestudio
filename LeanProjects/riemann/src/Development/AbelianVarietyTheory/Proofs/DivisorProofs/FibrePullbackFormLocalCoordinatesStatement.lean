import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackFormLocalCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_pullback_form_local_coordinates : ∀ (M : Type) [TopologicalSpace M] (A : HolAtlas M 1) (α : (famAtlas A).Fld), (famAtlas A).IsForm α → ∀ (j : A.ι) (k : sphere.ι) (t : OnePoint ℂ), t ∈ (sphere.e k).source → ∀ v : V 1, A.loc ((famAtlas A).pullback A (fib t) α) j v = pull headIn ((famAtlas A).loc α (j, k) (appendV 1 1 (v, sphere.e k t))) := by
  first | exact @GlobalTheory.BcUnique.loc_pullback_fib | exact GlobalTheory.BcUnique.loc_pullback_fib | (intros; apply GlobalTheory.BcUnique.loc_pullback_fib <;> assumption)
