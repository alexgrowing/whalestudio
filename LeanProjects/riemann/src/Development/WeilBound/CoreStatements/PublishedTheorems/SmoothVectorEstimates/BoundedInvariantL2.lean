import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace BoundedInvariantL2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]

theorem memL2Quotient_of_bounded_left_invariant [IsFiniteMeasure (quotMeasure Γ μ)] (φ : G →ᵇ ℂ) (h : LeftInv Γ φ) : MemL2Quotient Γ μ φ := by
  refine ⟨h, MemLp.of_bound ?_ ‖φ‖ (Eventually.of_forall fun q => φ.norm_coe_le_norm q.out)⟩
  rw [aestronglyMeasurable_quotMeasure_iff_lift, h.lift_descend]
  exact φ.continuous.aestronglyMeasurable

theorem norm_toL2_sub_le_sup_norm [IsFiniteMeasure (quotMeasure Γ μ)] (φ ψ : G →ᵇ ℂ) (hφ : MemL2Quotient Γ μ φ)
    (hψ : MemL2Quotient Γ μ ψ) :
    ‖hφ.toL2 - hψ.toL2‖ ≤ (measureUnivNNReal (quotMeasure Γ μ) : ℝ) ^ (2 : ENNReal).toReal⁻¹ * ‖φ - ψ‖ := by
  have hd : LeftInv Γ ⇑(φ - ψ) := fun γ hγ g => by simp [hφ.1 γ hγ g, hψ.1 γ hγ g]
  have h := memL2Quotient_of_bounded_left_invariant (μ := μ) (φ - ψ) hd
  have e : hφ.toL2 - hψ.toL2 = h.toL2 := (MemLp.toLp_sub hφ.2 hψ.2).symm
  rw [e]
  exact Lp.norm_le_of_ae_bound (norm_nonneg _)
    (h.coeFn_toL2.mono fun q hq => by rw [hq]; exact (φ - ψ).norm_coe_le_norm _)

end BoundedInvariantL2

theorem bounded_invariant_functions_in_L2 : G2b := by
  intro E _ _ _ a μ _ _ H hH
  have := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  let Y : Submodule ℂ (XB E a) :=
    { carrier := {φ | ∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H}
      add_mem' := by
        rintro φ ψ ⟨h1, m1⟩ ⟨h2, m2⟩
        have h : MemL2Quotient (latticeGL E a) μ ⇑(φ + ψ) :=
          ⟨fun γ hγ g => by simp [h1.1 γ hγ g, h2.1 γ hγ g], h1.2.add h2.2⟩
        have e : h.toL2 = h1.toL2 + h2.toL2 := MemLp.toLp_add h1.2 h2.2
        exact ⟨h, e ▸ H.add_mem m1 m2⟩
      zero_mem' := by
        have h : MemL2Quotient (latticeGL E a) μ ⇑(0 : XB E a) := ⟨fun γ hγ g => rfl, MemLp.zero⟩
        have e : h.toL2 = 0 := MemLp.toLp_zero h.2
        exact ⟨h, e ▸ H.zero_mem⟩
      smul_mem' := by
        rintro c φ ⟨h1, m1⟩
        have h : MemL2Quotient (latticeGL E a) μ ⇑(c • φ) :=
          ⟨fun γ hγ g => by simp [h1.1 γ hγ g], h1.2.const_smul c⟩
        have e : h.toL2 = c • h1.toL2 := MemLp.toLp_const_smul c h1.2
        exact ⟨h, e ▸ H.smul_mem c m1⟩ }
  refine ⟨Y, ?_, ?_, fun φ => Iff.rfl⟩
  · refine IsSeqClosed.isClosed fun {x p} hx hp => ?_
    choose hxm hxH using hx
    have hpl : LeftInv (latticeGL E a) ⇑p := fun γ hγ g => by
      have t1 : Tendsto (fun n => x n (γ * g)) atTop (𝓝 (p (γ * g))) :=
        ((continuous_eval_const (γ * g)).tendsto p).comp hp
      have t2 : Tendsto (fun n => x n (γ * g)) atTop (𝓝 (p g)) := by
        have := ((continuous_eval_const g).tendsto p).comp hp
        refine this.congr fun n => ?_
        exact ((hxm n).1 γ hγ g).symm
      exact tendsto_nhds_unique (f := fun n => x n (γ * g)) (l := (atTop : Filter ℕ)) t1 t2
    have hp2 := BoundedInvariantL2.memL2Quotient_of_bounded_left_invariant (μ := μ) p hpl
    refine ⟨hp2, hH.1.mem_of_tendsto (f := fun n => (hxm n).toL2) (b := (atTop : Filter ℕ)) ?_
      (Eventually.of_forall hxH)⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hn : Tendsto (fun n => ‖x n - p‖) atTop (𝓝 0) := (tendsto_iff_norm_sub_tendsto_zero).1 hp
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => BoundedInvariantL2.norm_toL2_sub_le_sup_norm (x n) p (hxm n) hp2) ?_
    simpa using hn.const_mul ((measureUnivNNReal (quotMeasure (latticeGL E a) μ) : ℝ) ^ (2 : ENNReal).toReal⁻¹)
  · rintro g φ ⟨h, m⟩
    have m' := hH.2 g _ m
    rw [right_translate_toL2] at m'
    exact ⟨h.mul_right g, m'⟩

end PositivityTheory.jumpWindows

end
