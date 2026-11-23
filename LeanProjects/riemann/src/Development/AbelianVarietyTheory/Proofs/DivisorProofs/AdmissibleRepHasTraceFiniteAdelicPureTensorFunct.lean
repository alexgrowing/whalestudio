import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionFiniteAdelicPureTensorEqLocalConvolut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinTrace

variable {D : D7}

theorem finFn_mem_SB (V : HSp D) {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) : finFn V ff ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  have hm := hff.tensorFin_mem
  rw [show finFn V ff = tensorFin D.sp.cm.sig V.gram ff ∘ (finPtsEquiv D.sp.cm.sig V.gram).symm from
    funext fun y => GlobalTheory.TrConv.finFn_eq_tensorFin V ff y]
  exact ⟨hm.1.comp_continuous (finPtsEquiv D.sp.cm.sig V.gram).symm.continuous,
    hm.2.comp_homeomorph (finPtsEquiv D.sp.cm.sig V.gram).symm.toHomeomorph⟩

theorem hasTrace_finFn : ∀ (D : D7) (V : HSp D) (ν : Measure (GfC V)) [ν.IsHaarMeasure] (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c) ∧ ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → IsCompact (K : Set (GfC V)) → (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x := by
  intro D V ν _ ff hff W _ _ σ hσ
  obtain ⟨hlc, hcs⟩ := finFn_mem_SB V hff
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) (smoothOp σ ν (finFn V ff)) := by
    intro v l
    refine ⟨?_, ?_⟩
    · have h := GlobalTheory.OpTrace.integrable_map (μ := ν) (hσ.1.smoothOp_integrand hlc hcs v).1
        (hσ.1.smoothOp_integrand hlc hcs v).2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using h
    · rw [hσ.1.map_smoothOp hlc hcs l v]
      simp only [smul_eq_mul]
  obtain ⟨K₀, ho, hc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hfd := hσ.finiteDimensional_range_smoothOp (μ := ν) hlc hcs ho hc
  refine ⟨⟨_, _, hA, hfd, rfl⟩, fun K _ _ hK hne => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, smoothOp σ ν (finFn V ff) v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (by convert hA using 1; exact (LinearMap.ext h).symm)
  exact ⟨_, hv, GlobalTheory.OpTrace.mem_fixed.1 (hσ.1.smoothOp_mem_fixed hlc hcs hK v)⟩

end GlobalTheory.FinTrace

end
