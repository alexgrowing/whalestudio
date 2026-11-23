import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens

theorem eLpNorm_sub_tendsto_of_unif {X : Type} [MeasurableSpace X] (ν : Measure X) (hν : ν Set.univ = 1)
    (g : ℕ → X → ℂ) (f : X → ℂ) (h : TendstoUniformly g f Filter.atTop) :
    Filter.Tendsto (fun j => eLpNorm (g j - f) 2 ν) Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  filter_upwards [Metric.tendstoUniformly_iff.1 h δ hδ0'] with j hj
  have hb : ∀ᵐ x ∂ν, ‖(g j - f) x‖ ≤ δ := Filter.Eventually.of_forall fun x => by
    have := (hj x).le
    rwa [dist_comm, dist_eq_norm] at this
  refine (eLpNorm_le_of_ae_bound hb).trans ?_
  simpa [hν] using hδ.le

theorem wordAct_heisDer_sub {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) :
    GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (f - g) =
      GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f - GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [GlobalTheory.Size.wordAct_cons, ih, GlobalTheory.Size.wordAct_cons, GlobalTheory.Size.wordAct_cons, sub_eq_add_neg, sub_eq_add_neg,
      ← neg_one_smul ℂ, ← neg_one_smul ℂ (GlobalTheory.Size.heisDer ψ θ a _)]
    simp only [GlobalTheory.Size.heisDer]
    rw [GlobalTheory.Size.dRho_add hψ hθ a.1 _ (GlobalTheory.Size.theta_word hψ hθ l hf)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Size.theta_word hψ hθ l hg)), GlobalTheory.Size.dRho_smul]

theorem sobO_sub_tendsto_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (u : ℕ → WO S T → ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ j, IsThetaFunO ψ S T (u j)) → (∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) Filter.atTop) → ∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0) := by
  intro D ψ hψ θ hθ S T μ 𝓕 hμ u f hf hu hl d
  have key : ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), Filter.Tendsto
      (fun j => GlobalTheory.Size.l2O μ 𝓕 (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j - f))) Filter.atTop (nhds 0) := by
    intro l
    simp only [wordAct_heisDer_sub hψ hθ (hu _) hf l, GlobalTheory.Size.l2O]
    exact eLpNorm_sub_tendsto_of_unif _ (by rw [Measure.restrict_apply_univ]; exact hμ.2.2) _ _ (hl l)
  have := tendsto_finset_sum (Finset.range (d + 1)) fun k _ =>
    tendsto_finset_sum (Finset.univ : Finset (Fin k → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
      fun a _ => key (List.ofFn a)
  simp only [Finset.sum_const_zero] at this
  exact this

end GlobalTheory.ThetaDens
