import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPoint
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.AxLemma

theorem ax_lemma_complete : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (y : ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ‖Per.σC g y - y‖ ≤ r) → ∃ z : Om l, (∀ g ∈ H, g z = z) ∧ ‖y - (z : ℂ_[l])‖ ≤ c * r := by
  intro l _
  obtain ⟨c, hc, hax⟩ := ax_lemma l
  refine ⟨c + 1, by linarith, fun H y r hr hy => ?_⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Om l, ‖y - (y₀ : ℂ_[l])‖ ≤ r := by
    have hd : DenseRange ((↑) : PadicAlgCl l → ℂ_[l]) := UniformSpace.Completion.denseRange_coe
    obtain ⟨b, hb⟩ := Metric.denseRange_iff.1 hd y r hr
    exact ⟨b, by rw [← dist_eq_norm]; exact hb.le⟩
  have hsub : ∀ a b : Om l, ((a - b : Om l) : ℂ_[l]) = (a : ℂ_[l]) - (b : ℂ_[l]) := by
    intro a b
    rw [PadicComplex.coe_eq, map_sub, ← PadicComplex.coe_eq, ← PadicComplex.coe_eq]
  obtain ⟨z, hz, hyz⟩ := hax H y₀ r (fun g hg => by
    rw [← PadicComplex.norm_extends l, hsub, ← GlobalTheory.RingBasics.σC_coe]
    have e : Per.σC g (y₀ : ℂ_[l]) - (y₀ : ℂ_[l])
        = Per.σC g ((y₀ : ℂ_[l]) - y) + ((Per.σC g y - y) + (y - (y₀ : ℂ_[l]))) := by
      rw [map_sub]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [GlobalTheory.RingBasics.norm_σC, norm_sub_rev]; exact hy₀
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy g hg) hy₀))
  refine ⟨z, hz, ?_⟩
  rw [← PadicComplex.norm_extends l, hsub] at hyz
  have e : y - (z : ℂ_[l]) = (y - (y₀ : ℂ_[l])) + ((y₀ : ℂ_[l]) - (z : ℂ_[l])) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end GlobalTheory.AxLemma
