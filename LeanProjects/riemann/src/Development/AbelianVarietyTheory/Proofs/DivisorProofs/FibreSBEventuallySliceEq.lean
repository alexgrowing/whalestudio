import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt

namespace GlobalTheory.DetEqv

open Set Filter Topology

theorem fibreSB_eventually_slice_eq {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (Φ : X × Z → ℂ) (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) (z₀ : Z) :
    ∀ᶠ z in 𝓝 z₀, ∀ u, Φ (u, z) = Φ (u, z₀) := by
  have hK : IsCompact (Prod.fst '' tsupport Φ) := hc.isCompact.image continuous_fst
  have h1 : ∀ᶠ z in 𝓝 z₀, ∀ u ∈ Prod.fst '' tsupport Φ, Φ (u, z) = Φ (u, z₀) := by
    refine hK.eventually_forall_of_forall_eventually (P := fun z u => Φ (u, z) = Φ (u, z₀)) ?_
    intro u _
    have e := hl.eventually_eq (u, z₀)
    have c1 : Tendsto (fun q : Z × X => (q.2, q.1)) (𝓝 (z₀, u)) (𝓝 (u, z₀)) :=
      (continuous_snd.prodMk continuous_fst).tendsto (z₀, u)
    have c2 : Tendsto (fun q : Z × X => (q.2, z₀)) (𝓝 (z₀, u)) (𝓝 (u, z₀)) :=
      (continuous_snd.prodMk continuous_const).tendsto (z₀, u)
    filter_upwards [c1.eventually e, c2.eventually e] with q a b
    exact a.trans b.symm
  filter_upwards [h1] with z hz u
  by_cases hu : u ∈ Prod.fst '' tsupport Φ
  · exact hz u hu
  · have h0 : ∀ w, Φ (u, w) = 0 := fun w =>
      image_eq_zero_of_notMem_tsupport fun h => hu ⟨(u, w), h, rfl⟩
    rw [h0, h0]

theorem fibreSB_isLocallyConstant {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    [MeasurableSpace X] (m : MeasureTheory.Measure X)
    (Φ : X × Z → ℂ) (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    IsLocallyConstant (fun z : Z => ∫ u, Φ (u, z) ∂m) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z₀
  filter_upwards [fibreSB_eventually_slice_eq Φ hl hc z₀] with z hz
  simp only [hz]

theorem fibreSB_hasCompactSupport {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    [MeasurableSpace X] (m : MeasureTheory.Measure X)
    (Φ : X × Z → ℂ) (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    HasCompactSupport (fun z : Z => ∫ u, Φ (u, z) ∂m) := by
  have hK : IsCompact (Prod.snd '' tsupport Φ) := hc.isCompact.image continuous_snd
  have hL := fibreSB_isLocallyConstant m Φ hl hc
  have hcl : IsClosed (Function.support (fun z : Z => ∫ u, Φ (u, z) ∂m)) :=
    (hL.isClopen_fiber 0).compl.isClosed
  refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
  rw [tsupport, hcl.closure_eq]
  intro z hz
  by_contra hn
  apply hz
  have h0 : ∀ u, Φ (u, z) = 0 := fun u =>
    image_eq_zero_of_notMem_tsupport fun h => hn ⟨(u, z), h, rfl⟩
  simp [h0]

theorem fibre_integral_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : MeasureTheory.Measure k) [ν.IsAddHaarMeasure]
    (Z : Type) [TopologicalSpace Z] (p : ℕ) (Φ : (Fin p → k) × Z → ℂ), Φ ∈ GlobalTheory.SplitWeil.SB ((Fin p → k) × Z) →
      (fun z : Z => ∫ u, Φ (u, z) ∂(MeasureTheory.Measure.pi fun _ : Fin p => ν)) ∈ GlobalTheory.SplitWeil.SB Z := by
  intro k _ _ _ _ _ _ ν _ Z _ p Φ h
  exact ⟨fibreSB_isLocallyConstant _ Φ h.1 h.2, fibreSB_hasCompactSupport _ Φ h.1 h.2⟩

end GlobalTheory.DetEqv
