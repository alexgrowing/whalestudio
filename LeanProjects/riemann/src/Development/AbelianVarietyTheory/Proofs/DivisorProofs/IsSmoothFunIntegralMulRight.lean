import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import GroundTheory.AutomorphicForms.GKModules.Garding
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff Manifold

namespace GlobalTheory

theorem isSmoothFun_integral_mul_right : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] (K : Set G), IsCompact K → ν Kᶜ = 0 → ∀ κ : G → ℂ, h.IsSmoothFun κ → h.IsSmoothFun (fun z => ∫ y, κ (z * y) ∂ν) := by
  intro 𝔸 _ _ _ _ G 𝔤 h _ _ ν _ K hK hν κ hκ
  haveI := secondCountableTopology_subgroup_units G
  haveI := h.locallyCompactSpace
  obtain ⟨ψ, hψ1, -, hψc, -⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g
  have hae : ∀ᵐ y ∂ν, y ∈ K := by
    rw [ae_iff]; exact hν
  have e : (fun Y : 𝔤 => ∫ y, κ (g * h.expG Y * y) ∂ν) =
      fun Y => ∫ y, ((ψ y : ℝ) : ℂ) * κ (g * h.expG Y * y) ∂ν := by
    funext Y
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp [hψ1 hy]
  rw [e]
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hκg : ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (fun x : G => κ (g * x)) :=
    ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hκ (contMDiff_const.mul contMDiff_id)
  set Φ : 𝔤 → G → ℂ := fun Y y => κ (g * h.expG Y * y) with hΦdef
  have hΦ : ∀ y₀ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => Φ q.1 (y₀ * h.expG q.2)) := by
    intro y₀
    have := h.contDiff_comp_expG_mul_expG hκg contDiff_fst y₀ contDiff_snd
    simpa [hΦdef, mul_assoc] using this
  have hΦY : ∀ y : G, ContDiff ℝ ∞ (fun Y => Φ Y y) := by
    intro y
    have := h.contDiff_comp_expG_mul_expG hκg contDiff_id y (contDiff_const (c := (0 : 𝔤)))
    simpa [hΦdef, mul_assoc] using this
  have hD : ∀ (k : ℕ) (Y : 𝔤) (y : G),
      iteratedFDeriv ℝ k (fun Y => ((ψ y : ℝ) : ℂ) * Φ Y y) Y =
        ((ψ y : ℝ) : ℂ) • iteratedFDeriv ℝ k (fun Y => Φ Y y) Y := by
    intro k Y y
    have e : (fun Y => ((ψ y : ℝ) : ℂ) * Φ Y y) = ((ψ y : ℝ) : ℂ) • fun Y => Φ Y y := by
      funext Y; simp [smul_eq_mul]
    rw [e, iteratedFDeriv_const_smul_apply ((hΦY y).contDiffAt.of_le (by exact_mod_cast le_top))]
  change ContDiff ℝ ∞ fun Y : 𝔤 => ∫ y, ((ψ y : ℝ) : ℂ) * Φ Y y ∂ν
  refine contDiff_integral_of_iteratedFDeriv (μ := ν) (fun (Y : 𝔤) (y : G) => ((ψ y : ℝ) : ℂ) * Φ Y y)
    (fun y => contDiff_const.mul (hΦY y)) (fun k => ?_) (fun Y₀ => ?_)
  · have hc := h.continuous_iteratedFDeriv_param Φ hΦ k
    refine (((Complex.continuous_ofReal.comp ψ.continuous).comp continuous_snd).smul hc).congr fun q => ?_
    exact (hD k q.1 q.2).symm
  · refine ⟨Set.univ, Filter.univ_mem, tsupport ψ, hψc, fun Y _ y hy => ?_⟩
    simp [image_eq_zero_of_notMem_tsupport hy]

end GlobalTheory
