import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

open Filter Topology

theorem arFun_tendsto_PP {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem)
    (h : M.Converges II) (F : RPA Ψ N) :
    Tendsto (fun t => M.arFun II t F) (𝓝[>] 0) (𝓝 (M.PP II F)) := by
  classical
  simp only [GlobalTheory.CompanionTheory.Ar.Top.RootModel.arFun, GlobalTheory.CompanionTheory.Ar.Top.RootModel.PP, Module.Basis.constr_apply, Finsupp.sum]
  refine tendsto_finsetSum _ (fun m _ => ?_)
  obtain ⟨L, hL⟩ := h m
  exact (tendsto_nhds_limUnder ⟨L, hL⟩).const_smul _

theorem PP_eq_add_of_arFun_eq_add :
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M M' : RootModel Ψ N) (II : IntersectionSystem), M.Converges II →
      M'.Converges II → ∀ (F : RPA Ψ N) (c : ℝ), (∀ t : ℝ, 0 < t → M.arFun II t F = M'.arFun II t F + c) →
      M.PP II F = M'.PP II F + c := by
  intro Ψ _ N M M' II hM hM' F c hF
  have h1 := arFun_tendsto_PP M II hM F
  have h2 := (arFun_tendsto_PP M' II hM' F).add_const c
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hF t ht).symm

end GlobalTheory.CompanionTheory.Ar.Num
