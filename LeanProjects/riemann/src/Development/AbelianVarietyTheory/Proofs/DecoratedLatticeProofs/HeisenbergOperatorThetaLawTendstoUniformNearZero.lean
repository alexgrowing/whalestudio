import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeisNearZero

theorem heisO_near_zero_unif : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (q : WO A T → ℂ), Continuous q → (∀ (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), q (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * q u) → ∀ ε : ℝ, 0 < ε → ∃ N ∈ 𝓝 (0 : WO A T), ∀ a ∈ N, ∀ w, ‖heisO ψ A T a q w - q w‖ ≤ ε := by
  intro D ψ hψ A T q hq hlaw ε hε
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
  have hc : Continuous ψ := hψ.1.1
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  let Φ : WO A T × WO A T → ℂ := fun p => heisO ψ A T p.1 q p.2 - q p.2
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun p : WO A T × WO A T => symplOH A T p.2 p.1 :=
      GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd continuous_fst
    exact ((hc.comp h1).mul (hq.comp (continuous_snd.add continuous_fst))).sub (hq.comp continuous_snd)
  have hΦ0 : ∀ w, Φ (0, w) = 0 := by
    intro w
    simp only [Φ, heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero, sub_self]
  have hev : ∀ᶠ a in 𝓝 (0 : WO A T), ∀ w ∈ K, ‖Φ (a, w)‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun w _ => ?_
    have ht : Filter.Tendsto Φ (𝓝 ((0 : WO A T), w)) (𝓝 0) := by
      have := hΦ.tendsto ((0 : WO A T), w); rwa [hΦ0] at this
    exact (ht.norm.eventually (gt_mem_nhds (by simpa using hε))).mono fun z hz => by simpa using hz
  refine ⟨_, hev, fun a ha w => ?_⟩
  obtain ⟨g, hg, hgw⟩ := hKc w
  obtain ⟨γ, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hg
  have e : Φ (a, GlobalTheory.MixModel.rat γ + w) = ψ (-(symplOH A T (ratW T A γ) w)) * Φ (a, w) := by
    simp only [Φ]
    rw [← GlobalTheory.MixModel.ratW_eq, GlobalTheory.OrientedHeis.heisO_quasi a q hlaw γ w, hlaw γ w, mul_sub]
  have h := ha _ hgw
  rw [e, norm_mul, hn, one_mul] at h
  exact h.le

end GlobalTheory.HeisNearZero
