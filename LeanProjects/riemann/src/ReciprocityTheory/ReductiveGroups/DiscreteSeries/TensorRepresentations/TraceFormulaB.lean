import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaA

noncomputable section

open MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

theorem tf_rep_closure {n : ℕ} {G : Type*} [MeasurableSpace G] {μ : Measure G}
    (ρ : G → (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ) →L[ℂ] PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hρ : ∀ g x, ‖ρ g x‖ ≤ ‖x‖) (w : Fin n → PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ))
    (S : Submodule ℂ (PiLp 2 (fun _ : Fin n => Lp ℂ 2 μ)))
    (hS : ∀ v ∈ S, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v)) :
    ∀ v ∈ S.topologicalClosure, ∀ c, ((v c : Lp ℂ 2 μ) : G → ℂ) =ᵐ[μ] fun g => inner ℂ (w c) (ρ g v) := by
  intro v hv c
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hv
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hv
  have huc : Tendsto (fun k => u k c) atTop (𝓝 (v c)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun k => PiLp.dist_apply_le _ _ c) (tendsto_iff_dist_tendsto_zero.1 hu))
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp huc).exists_seq_tendsto_ae
  have hall : ∀ᵐ g ∂μ, ∀ k, ((u k c : Lp ℂ 2 μ) : G → ℂ) g = inner ℂ (w c) (ρ g (u k)) :=
    ae_all_iff.2 (fun k => hS (u k) (huS k) c)
  filter_upwards [hns, hall] with g hg hgall
  have h2 : Tendsto (fun i => inner ℂ (w c) (ρ g (u (ns i)))) atTop (𝓝 (inner ℂ (w c) (ρ g v))) := by
    have h3 : Tendsto (fun i => u (ns i)) atTop (𝓝 v) :=
      hu.comp (hmono.tendsto_atTop)
    exact ((continuous_const.inner continuous_id).tendsto _).comp ((ρ g).continuous.tendsto v |>.comp h3)
  simp only [hgall] at hg
  exact tendsto_nhds_unique hg h2

end ReciprocityTheory.ChartRestriction.DS
