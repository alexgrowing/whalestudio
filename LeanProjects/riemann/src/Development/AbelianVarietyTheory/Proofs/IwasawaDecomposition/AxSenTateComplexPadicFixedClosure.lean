import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPointStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem ax_sen_tate : ∀ (l : ℕ) [Fact l.Prime], ∀ (H : Subgroup (GQ l)) (x : ℂ_[l]),
    (∀ g ∈ H, Per.σC g x = x) →
      x ∈ closure ((fun y : Om l => (y : ℂ_[l])) '' {y | ∀ g ∈ H, g y = y}) := by
  intro l _ H x hx
  obtain ⟨c, hc, hax⟩ := GlobalTheory.T.bounded_orbit_has_nearby_fixed_point l
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hd : DenseRange (fun y : Om l => (y : ℂ_[l])) := by
    intro z
    induction z using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_closure
    | ih a => exact subset_closure ⟨a, rfl⟩
  have hδ : 0 < ε / (2 * c + 2) := by positivity
  obtain ⟨a, ha⟩ := hd.exists_dist_lt x hδ
  set δ := ε / (2 * c + 2) with hδdef
  have hmul : δ * (2 * c + 2) = ε := by
    rw [hδdef]; field_simp
  rw [dist_eq_norm] at ha
  have hsub : ∀ u v : Om l, ‖u - v‖ = ‖(u : ℂ_[l]) - (v : ℂ_[l])‖ := by
    intro u v
    rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, PadicComplex.coe_eq,
      PadicComplex.coe_eq, map_sub]
  obtain ⟨y, hy, hxy⟩ := hax H a (2 * δ) (by
    intro g hg
    have h1 : ((g a : Om l) : ℂ_[l]) - (a : ℂ_[l])
        = (x - (a : ℂ_[l])) - Per.σC g (x - (a : ℂ_[l])) := by
      rw [map_sub, hx g hg, GlobalTheory.RingBasics.σC_coe]; ring
    rw [hsub, h1]
    have h2 := norm_sub_le (x - (a : ℂ_[l])) (Per.σC g (x - (a : ℂ_[l])))
    rw [GlobalTheory.RingBasics.norm_σC] at h2
    linarith)
  refine ⟨(y : ℂ_[l]), ⟨y, hy, rfl⟩, ?_⟩
  rw [hsub] at hxy
  have h3 := norm_add_le (x - (a : ℂ_[l])) ((a : ℂ_[l]) - (y : ℂ_[l]))
  rw [sub_add_sub_cancel] at h3
  rw [dist_eq_norm]
  nlinarith

end GlobalTheory.MemLoc
