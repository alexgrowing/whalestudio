import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCMean

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def Hh (Y : Finset H) (κ : H → H → ℂ) (hat : Fin f → ℂ → H → H → ℂ) (σ : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, hat v (σ v) h h'

theorem eventually_norm_gt (v : Fin f) (a : ℝ) : ∀ᶠ x in crystallineComparison.atInfAll f, a < ‖x v‖ := by
  have h : ∀ᶠ x in Filter.comap (fun x : crystallineComparison.V f => ‖x v‖) atTop, a < ‖x v‖ :=
    (Filter.eventually_gt_atTop a).comap _
  unfold crystallineComparison.atInfAll
  exact Filter.mem_iInf_of_mem v h

theorem eventually_good (σ : crystallineComparison.V f) : ∀ᶠ x in crystallineComparison.atInfAll f, Good x ∧ Good (x + σ) := by
  have h1 : ∀ v, ∀ᶠ x in crystallineComparison.atInfAll f, x v ≠ 0 ∧ x v + σ v ≠ 0 := by
    intro v
    filter_upwards [eventually_norm_gt v ‖σ v‖] with x hx
    constructor
    · intro h
      rw [h, norm_zero] at hx
      exact absurd hx (not_lt.mpr (norm_nonneg _))
    · intro h
      have e : x v = -σ v := eq_neg_of_add_eq_zero_left h
      rw [e, norm_neg] at hx
      exact lt_irrefl _ hx
  filter_upwards [Filter.eventually_all.mpr h1] with x hx
  exact ⟨fun v => (hx v).1, fun v => (hx v).2⟩

theorem tendsto_coord (v : Fin f) : Tendsto (fun x : crystallineComparison.V f => x v) (crystallineComparison.atInfAll f) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop, Filter.tendsto_comap_iff]
  exact Filter.tendsto_comap.mono_left (iInf_le (fun v => Filter.comap (fun x : crystallineComparison.V f => ‖x v‖) atTop) v)

theorem phiG_tendsto (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ)
    (hat : Fin f → ℂ → H → H → ℂ)
    (hlim : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => K v (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (hat v σ h h'))) (σ : crystallineComparison.V f) :
    Tendsto (fun x => phiG Y κ K x (x + σ)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)) := by
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun x => phi Y κ K x (x + σ)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)))
  · filter_upwards [eventually_good σ] with x hx
    rw [phiG, if_pos hx]
  · unfold phi Hh
    refine tendsto_finset_sum _ (fun h hh => tendsto_finset_sum _ (fun h' hh' => ?_))
    refine Tendsto.const_mul _ ?_
    refine tendsto_finset_prod _ (fun v _ => ?_)
    exact (hlim v h hh h' hh' (σ v)).comp (tendsto_coord v)

theorem phiG_conj_tendsto (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (K : Fin f → H × ℂ → H × ℂ → ℂ)
    (hat : Fin f → ℂ → H → H → ℂ)
    (hlim : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => conj (K v (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (hat v σ h h'))) (σ : crystallineComparison.V f) :
    Tendsto (fun x => conj (phiG Y κ K (x + σ) x)) (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)) := by
  have hherm : ∀ h ∈ Y, ∀ h' ∈ Y, conj (κ h' h) = κ h h' := by
    intro h hh h' hh'
    have := hκ.1.apply ⟨h, hh⟩ ⟨h', hh'⟩
    simp only [Matrix.of_apply] at this
    exact this
  refine Tendsto.congr' ?_ (?_ : Tendsto (fun x => ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, conj (K v (h', x v + σ v) (h, x v)))
    (crystallineComparison.atInfAll f) (𝓝 (Hh Y κ hat σ)))
  · filter_upwards [eventually_good σ] with x hx
    symm
    rw [phiG, if_pos ⟨hx.2, hx.1⟩, phi]
    simp only [map_sum, map_mul, map_prod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun h' hh' => ?_))
    rw [hherm h hh h' hh']
    rfl
  · unfold Hh
    refine tendsto_finset_sum _ (fun h hh => tendsto_finset_sum _ (fun h' hh' => ?_))
    refine Tendsto.const_mul _ ?_
    refine tendsto_finset_prod _ (fun v _ => ?_)
    exact (hlim v h hh h' hh' (σ v)).comp (tendsto_coord v)

section mean

variable (Λ : AddSubgroup (crystallineComparison.V f)) (LIM : (Λ → ℂ) → ℂ)

theorem bdd_add {α : Type} {g k : α → ℂ} (hg : crystallineComparison.Bdd g) (hk : crystallineComparison.Bdd k) : crystallineComparison.Bdd (g + k) := by
  obtain ⟨B1, h1⟩ := hg
  obtain ⟨B2, h2⟩ := hk
  exact ⟨B1 + B2, fun x => (norm_add_le _ _).trans (add_le_add (h1 x) (h2 x))⟩

theorem mean_smul (hL : crystallineComparison.IsMean LIM) (c : ℂ) {g : Λ → ℂ} (hg : crystallineComparison.Bdd g) :
    LIM (fun x => c * g x) = c * LIM g := by
  exact hL.2.1 c g hg

end mean

end

end Formalism.FourierDecayAlt.P.PBC
