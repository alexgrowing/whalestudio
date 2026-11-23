import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.SplitWeil NumberField GlobalTheory.Orb Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AutomorphicL2Unitary (conv)
open scoped Topology ContDiff Matrix

noncomputable section

namespace GlobalTheory

namespace Published

def DixmierMalliavinFactorisation : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (n : Type) [Fintype n] [DecidableEq n] (ι : G →* Matrix n n ℂ),
    Topology.IsClosedEmbedding (ι.toHomUnits : G → GL n ℂ) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure], ∀ V ∈ 𝓝 (1 : G), ∀ f ∈ CcMat ι,
      ∃ (N : ℕ) (g h : Fin N → G → ℂ),
        (∀ i, g i ∈ CcMat ι ∧ h i ∈ CcMat ι ∧ tsupport (g i) ⊆ V ∧ tsupport (h i) ⊆ tsupport f) ∧
        f = ∑ i, conv μ (g i) (h i)

end Published

namespace SmoothFactor

theorem isClosedEmbedding_of_locallyCompact {H G : Type*} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {φ : H →* G} (h : Topology.IsEmbedding φ) :
    Topology.IsClosedEmbedding φ := by
  refine ⟨h, isClosed_of_closure_subset fun x hx => ?_⟩
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : H)
  rw [h.nhds_eq_comap] at hK1
  obtain ⟨U', hU', hUK⟩ := hK1
  obtain ⟨U, hUU, hU, h1⟩ := mem_nhds_iff.1 hU'
  have hx' : x ∈ φ.range.topologicalClosure := hx
  have hi : x⁻¹ ∈ closure (range φ) := φ.range.topologicalClosure.inv_mem hx'
  obtain ⟨_, hs, s, rfl⟩ := mem_closure_iff.1 hi _ (hU.preimage (continuous_mul_const x)) (by simpa using h1)
  have h2 : φ s * x ∈ closure (range φ) :=
    φ.range.topologicalClosure.mul_mem (φ.range.le_topologicalClosure ⟨s, rfl⟩) hx'
  have h3 : U ∩ range φ ⊆ φ '' K := by
    rintro _ ⟨hy, y, rfl⟩
    exact ⟨y, hUK (hUU hy), rfl⟩
  obtain ⟨k, -, e⟩ := closure_minimal h3 (hK.image h.continuous).isClosed (hU.inter_closure ⟨hs, h2⟩)
  exact ⟨s⁻¹ * k, by rw [map_mul, map_inv, e, inv_mul_cancel_left]⟩

theorem isClosedEmbedding_toHomUnits {H n : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [Fintype n] [DecidableEq n] {ι : H →* Matrix n n ℂ}
    (h : Topology.IsEmbedding (matCoord ι)) : Topology.IsClosedEmbedding (ι.toHomUnits : H → GL n ℂ) := by
  have hc : Continuous ι := h.continuous
  have h1 : Continuous (ι.toHomUnits : H → GL n ℂ) := Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩
  exact isClosedEmbedding_of_locallyCompact (Topology.IsEmbedding.of_comp h1 Units.continuous_val h)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem exists_sum_conv_ccArch (hDM : Published.DixmierMalliavinFactorisation) (h : IsCMExt F E σ) (w : InfinitePlace F)
    (μ : Measure (GArch σ J w)) [μ.IsHaarMeasure] {V : Set (GArch σ J w)} (hV : V ∈ 𝓝 1) {f : GArch σ J w → ℂ}
    (hf : f ∈ CcArch σ J w) :
    ∃ (N : ℕ) (g h : Fin N → GArch σ J w → ℂ),
      (∀ i, g i ∈ CcArch σ J w ∧ h i ∈ CcArch σ J w ∧ tsupport (g i) ⊆ V ∧ tsupport (h i) ⊆ tsupport f) ∧
      f = ∑ i, conv μ (g i) (h i) := by
  let τ : EmbOver E w := Classical.arbitrary _
  rw [ccArch_eq h τ] at hf ⊢
  exact hDM _ _ _ (isClosedEmbedding_toHomUnits (isEmbedding_archMat J h τ)) μ V hV f hf

open Classical in
variable (σ) in

def infMat : GInf σ J →* Matrix (Fin n × Σ w : InfinitePlace F, EmbOver E w) (Fin n × Σ w : InfinitePlace F, EmbOver E w) ℂ :=
  (Matrix.blockDiagonalRingHom (Fin n) _ ℂ).toMonoidHom.comp
    (MonoidHom.pi fun t => (archMat σ J t.2).comp (projInfArch σ J t.1))

open Classical in
variable (σ) in

theorem ccInf_eq : CcInf σ J = CcMat (infMat σ J) := by
  refine le_antisymm (ccSmooth_le (p := fun y w τ i j => y (i, ⟨w, τ⟩) (j, ⟨w, τ⟩)) (by fun_prop) fun g => ?_)
    (ccSmooth_le (p := fun y a b => if a.2 = b.2 then y a.2.1 a.2.2 a.1 b.1 else 0) ?_ fun _ => rfl)
  · funext w τ i j
    exact (Matrix.blockDiagonal_apply_eq (fun t : Σ w : InfinitePlace F, EmbOver E w =>
      archMat σ J t.2 (projInfArch σ J t.1 g)) i j ⟨w, τ⟩).symm
  · refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    split_ifs
    · exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id _) _) _) _
    · exact contDiff_const

open Classical in

theorem isEmbedding_infMat (h : IsCMExt F E σ) : Topology.IsEmbedding (matCoord (infMat σ J)) := by
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun _ => Classical.arbitrary _
  have h1 := (Topology.IsEmbedding.piMap fun w => isEmbedding_archMat J h (τ w)).comp
    (infContEquivPi σ J).toHomeomorph.isEmbedding
  have h2 : Continuous (matCoord (infMat σ J)) :=
    Continuous.matrix_blockDiagonal (continuous_pi fun t : Σ w : InfinitePlace F, EmbOver E w =>
      (continuous_archMat σ J t.2).comp (continuous_projInfArch σ J t.1))
  refine Topology.IsEmbedding.of_comp (g := fun y w i j => y (i, ⟨w, τ w⟩) (j, ⟨w, τ w⟩)) h2 (by fun_prop) ?_
  convert h1 using 1
  funext g w i j
  exact Matrix.blockDiagonal_apply_eq (fun t : Σ w : InfinitePlace F, EmbOver E w =>
      archMat σ J t.2 (projInfArch σ J t.1 g)) i j ⟨w, τ w⟩

theorem exists_sum_conv_ccInf (hDM : Published.DixmierMalliavinFactorisation) (h : IsCMExt F E σ)
    (μ : Measure (GInf σ J)) [μ.IsHaarMeasure] {V : Set (GInf σ J)} (hV : V ∈ 𝓝 1) {f : GInf σ J → ℂ}
    (hf : f ∈ CcInf σ J) :
    ∃ (N : ℕ) (g h : Fin N → GInf σ J → ℂ),
      (∀ i, g i ∈ CcInf σ J ∧ h i ∈ CcInf σ J ∧ tsupport (g i) ⊆ V ∧ tsupport (h i) ⊆ tsupport f) ∧
      f = ∑ i, conv μ (g i) (h i) := by
  classical
  rw [ccInf_eq] at hf ⊢
  exact hDM _ _ _ (isClosedEmbedding_toHomUnits (isEmbedding_infMat J h)) μ V hV f hf

example (h : IsCMExt F E σ) {V : Set (GInf σ J)} (hV : V ∈ 𝓝 1) :
    (Measure.haar : Measure (GInf σ J)).IsHaarMeasure ∧ ∃ f ∈ CcInf σ J, f 1 = 1 ∧ tsupport f ⊆ V := by
  obtain ⟨φ, h1, h2, -, h3⟩ := exists_bump (isEmbedding_infMat J h).isInducing hV
  refine ⟨inferInstance, fun x => (φ x : ℂ), (ccInf_eq σ J).ge h1, by simp [h2],
    subset_trans (closure_mono fun x hx => ?_) h3⟩
  simpa using hx

end SmoothFactor

end GlobalTheory
