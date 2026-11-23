import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdThetaInt

theorem integrable_theta : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ (Φ : schwartzA θ V.rank n) (g : G D n), Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g)) (autMeasure V ν) := by
  intro hP D n V hn hr θ hθ ω ν hν Φ g
  set φ := ω g Φ with hφdef
  have hfin : GlobalTheory.SiegelFormula.absThetaInt V ν φ.1 < ⊤ := hP D n V hn (Or.inr hr) θ hθ ν hν φ
  have hcont : Continuous φ.1 := (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ _ φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ _ φ.1 φ.2)).1
  have hleft := GlobalTheory.SiegelWeilLitCompare.leftInv_theta ω Φ g
  have hterm : ∀ h, theta ω Φ g h = ∑' ξ, φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ) := fun h => rfl
  refine ⟨?_, ?_⟩
  · rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, hleft.lift_descend]
    have hae : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ.1) q < ⊤ :=
      ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hcont) hfin.ne
    have hae' : ∀ᵐ h ∂ν, GlobalTheory.SiegelFormula.absTheta V φ.1 h < ⊤ := by
      have := (quasiMeasurePreserving_mk (Γ := GQ V) (μ := ν)).ae hae
      filter_upwards [this] with h hh
      rwa [(GlobalTheory.SiegelFormula.leftInv_absTheta V φ.1).descend_mk] at hh
    haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
    haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
      inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
    have hsum : ∀ᵐ h ∂ν, Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E =>
        φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ) :=
      hae'.mono fun h hh => Summable.of_enorm hh.ne
    have hlim := aestronglyMeasurable_of_tendsto_ae (μ := ν)
      (Filter.atTop : Filter (Finset (Matrix (Fin V.rank) (Fin n) D.host.E)))
      (f := fun F h => ∑ ξ ∈ F, φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ))
      (fun F => (continuous_finset_sum F fun ξ _ =>
        hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).aestronglyMeasurable)
      (hsum.mono fun h hh => hh.hasSum)
    exact hlim.congr (Filter.Eventually.of_forall fun h => (hterm h).symm)
  · refine lt_of_le_of_lt (lintegral_mono fun q => ?_) hfin
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, GlobalTheory.SiegelFormula.absTheta]
    exact enorm_tsum_le_tsum_enorm

end GlobalTheory.StdThetaInt

end
