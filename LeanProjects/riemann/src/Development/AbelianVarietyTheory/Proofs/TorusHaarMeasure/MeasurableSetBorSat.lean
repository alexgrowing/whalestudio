import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameMeas

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : Set (Frame X.Ψ r) :=
  {y | ∃ x ∈ C, ∃ b ∈ Bor X.Ψ r, y = rmul x b}

theorem borSat_subset_dom {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hC : C ⊆ X.dom) :
    borSat X C ⊆ X.dom := by
  rintro y ⟨x, hx, b, hb, rfl⟩
  exact OrthogonalFrameDomain.rmul_mem_dom X (hC hx) hb

theorem subset_borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : C ⊆ borSat X C :=
  fun x hx => ⟨x, hx, ExtFPf.oneF X, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X x).symm⟩

theorem rmul_mem_borSat_iff {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ borSat X C ↔ y ∈ borSat X C := by
  constructor
  · rintro ⟨x, hx, b', hb', h⟩
    refine ⟨x, hx, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨x, hx, b', hb', rfl⟩
    exact ⟨x, hx, rmul b' b, ExtFPf.mul_mem X hb' hb, ExtFPf.rmul_assoc X _ _ _⟩

theorem measurableSet_borSat {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hK : IsCompact C)
    (hC : C ⊆ X.dom) : MeasurableSet (borSat X C) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hK
  let T : Set (Frame X.Ψ r × C) := {p | ∀ τ : X.Ψ, ∀ a c : Fin r, c < a →
    ((mat p.2.1 τ).adjugate * ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat p.1 τ) a c = 0}
  have hm : ∀ τ : X.Ψ, Continuous fun y : Frame X.Ψ r => mat y τ := fun τ => continuous_apply τ
  have hT : IsClosed T := by
    simp only [T, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (((((hm τ).comp (continuous_subtype_val.comp continuous_snd)).matrix_adjugate).matrix_mul
      continuous_const).matrix_mul ((hm τ).comp continuous_fst)).matrix_elem a c
  have hT' : IsClosed (Prod.fst '' T) := isClosedMap_fst_of_compactSpace T hT
  have hU : IsOpen {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun τ => isOpen_ne_fun (hm τ).matrix_det continuous_const
  have heq : borSat X C = {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} ∩ Prod.fst '' T := by
    ext y
    constructor
    · intro hy
      have hyd : ∀ τ, (mat y τ).det ≠ 0 := fun τ => (borSat_subset_dom X hC hy τ).1
      obtain ⟨x, hx, b, hb, h⟩ := hy
      refine ⟨hyd, (y, ⟨x, hx⟩), ?_, rfl⟩
      exact (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mp
        ⟨b, hb, by rw [FundSetPf.lact_one]; exact h⟩
    · rintro ⟨hyd, ⟨y', x, hx⟩, hp, rfl⟩
      obtain ⟨b, hb, h⟩ := (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mpr hp
      rw [FundSetPf.lact_one] at h
      exact ⟨x, hx, b, hb, h⟩
  rw [heq]
  exact hU.measurableSet.inter hT'.measurableSet

theorem sat_eq_preimage {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {C : Set (Frame X.Ψ r)}
    (hC : C ⊆ X.dom) : sat X x0 C = cpt X x0 ⁻¹' borSat X C := by
  ext z
  exact ⟨fun h => h.2, fun h => ⟨borSat_subset_dom X hC h, h⟩⟩

theorem frameMeas_of_local (hI : MeasInvStatement (E := E))
    (hL : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 → ∀ b1 ∈ Bor X.Ψ r,
      ∃ U ∈ 𝓝 (rmul x1 b1), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
        ∫⁻ x in U, G x ≤ K * ∫⁻ z, G (cpt X x1 z) ∂muF X x1) :
    FrameMeasStatement (E := E) := by
  intro r X x0 hx0 C hK hC
  have key : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in C, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0 := by
    refine hK.induction_on (p := fun s => ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞,
      Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in s, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0) ?_ ?_ ?_ ?_
    · exact ⟨0, ENNReal.zero_lt_top, fun G _ _ => by simp⟩
    · rintro s t hst ⟨K, hK, h⟩
      exact ⟨K, hK, fun G hG hB => (lintegral_mono_set hst).trans (h G hG hB)⟩
    · rintro s t ⟨K, hK, h⟩ ⟨K', hK', h'⟩
      refine ⟨K + K', ENNReal.add_lt_top.mpr ⟨hK, hK'⟩, fun G hG hB => ?_⟩
      rw [add_mul]
      exact (lintegral_union_le _ _ _).trans (add_le_add (h G hG hB) (h' G hG hB))
    · intro x hx
      obtain ⟨x1, hx1, b1, hb1, rfl⟩ := ortho_holds r X x (hC hx)
      obtain ⟨U, hU, K, hK, h⟩ := hL r X x1 hx1 b1 hb1
      refine ⟨U, mem_nhdsWithin_of_mem_nhds hU, K, hK, fun G hG hB => ?_⟩
      rw [hI r X x0 x1 hx0 hx1 G hG hB]
      exact h G hG hB
  obtain ⟨K, hKt, h⟩ := key
  refine ⟨K, hKt, fun G hG hB => ?_⟩
  have hS := measurableSet_borSat X hK hC
  have h1 := h ((borSat X C).indicator G) (hG.indicator hS) (by
    intro x hx b hb
    by_cases hxS : x ∈ borSat X C
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem ((rmul_mem_borSat_iff X C hb).mpr hxS),
        hB x hx b hb]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem fun h => hxS ((rmul_mem_borSat_iff X C hb).mp h)])
  have h2 : ∫⁻ x in C, (borSat X C).indicator G x = ∫⁻ x in C, G x :=
    setLIntegral_congr_fun hK.measurableSet fun x hx =>
      Set.indicator_of_mem (subset_borSat X C hx) G
  have h3 : ∫⁻ z, (borSat X C).indicator G (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0 := by
    rw [sat_eq_preimage X x0 hC,
      ← lintegral_indicator ((FundSetPf.cont_cpt X x0).measurable hS)]
    rfl
  rw [← h2, ← h3]
  exact h1

end GlobalTheory.FrameMeas
