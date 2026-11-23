import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.CutQuot

section Abstract

variable {X : Type*} [MeasurableSpace X] {T : X → X → X} {G R : Set X} {μG μR ν : Measure X}

theorem null_of_stable (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    {B : Set X} (hB : MeasurableSet B) (hst : ∀ s ∈ R, ∀ x ∈ B, T s x ∈ B) (hn : μG B = 0) : ν B = 0 := by
  have h1 := hW (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hn] at h1
  have h2 : ∫⁻ x, B.indicator (fun _ => μR Set.univ) x ∂ν ≤
      ∫⁻ x, (∫⁻ s, B.indicator (1 : X → ℝ≥0∞) (T s x) ∂μR) ∂ν := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine le_of_eq (lintegral_congr_ae ?_)
      filter_upwards [hR] with s hs
      rw [Set.indicator_of_mem (hst s hs x hx)]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [← h1, lintegral_indicator_const hB, nonpos_iff_eq_zero, mul_eq_zero] at h2
  exact h2.resolve_left (by simpa using h0)

theorem exists_cut [SigmaFinite μG] [SFinite μR] (hT : Measurable (Function.uncurry T))
    (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    (hG : ∀ᵐ x ∂ν, x ∈ G)
    (hinv : ∀ ρ ∈ R, ∀ x, ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ s, f (T s (T ρ x)) ∂μR = ∫⁻ s, f (T s x) ∂μR) :
    ∃ φ : X → ℝ≥0∞, Measurable φ ∧ (∀ x, ∫⁻ ρ, φ (T ρ x) ∂μR ≤ 1) ∧
      ∀ F : X → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x ∈ G, F (T ρ x) = F x) →
        ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  obtain ⟨g, hg0, hgm, hgi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set ψ : X → ℝ≥0∞ := fun x => (g x : ℝ≥0∞) with hψ
  have hψm : Measurable ψ := hgm.coe_nnreal_ennreal
  have hTx : ∀ x, Measurable fun s => T s x := fun x => hT.comp (measurable_id.prodMk measurable_const)
  set I : X → ℝ≥0∞ := fun x => ∫⁻ s, ψ (T s x) ∂μR with hI
  have hIm : Measurable I := Measurable.lintegral_prod_left (f := fun s x => ψ (T s x)) (hψm.comp hT)
  have hI0 : ∀ x, I x ≠ 0 := by
    intro x hx
    have h := (lintegral_eq_zero_iff (hψm.comp (hTx x))).1 hx
    apply h0
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h] with s hs
    have := hg0 (T s x)
    simp [hψ] at hs
    exact this.ne' hs
  have hIfin : ∀ᵐ x ∂ν, I x < ∞ := by
    refine ae_lt_top hIm ?_
    rw [← hW ψ hψm]
    exact (hgi.trans ENNReal.one_lt_top).ne
  have key : ∀ x, ∫⁻ ρ, ψ (T ρ x) * (I (T ρ x))⁻¹ ∂μR = I x * (I x)⁻¹ := by
    intro x
    rw [show I x * (I x)⁻¹ = ∫⁻ ρ, ψ (T ρ x) * (I x)⁻¹ ∂μR from
      (lintegral_mul_const (I x)⁻¹ (f := fun s => ψ (T s x)) (hψm.comp (hTx x))).symm]
    refine lintegral_congr_ae ?_
    filter_upwards [hR] with s hs
    have : I (T s x) = I x := hinv s hs x ψ hψm
    rw [this]
  have hφm : Measurable fun x => ψ x * (I x)⁻¹ := hψm.mul hIm.inv
  refine ⟨fun x => ψ x * (I x)⁻¹, hφm, fun x => ?_, fun F hF hFi => ?_⟩
  · rw [key]; exact ENNReal.mul_inv_le_one _
  · show _ = ∫⁻ x, ψ x * (I x)⁻¹ * F x ∂μG
    rw [hW (fun x => ψ x * (I x)⁻¹ * F x) (hφm.mul hF)]
    refine lintegral_congr_ae ?_
    filter_upwards [hG, hIfin] with x hx hx'
    have h1 : ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F (T s x) ∂μR =
        ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F x ∂μR := by
      refine lintegral_congr_ae ?_
      filter_upwards [hR] with s hs
      rw [hFi s hs x hx]
    rw [h1, lintegral_mul_const (F x) (f := fun s => ψ (T s x) * (I (T s x))⁻¹) (hφm.comp (hTx x)), key,
      ENNReal.mul_inv_cancel (hI0 x) hx'.ne, one_mul]

end Abstract

theorem mul_mem_iff {k r : ℕ} {s : Mat k r} (hs : s ∈ GG k r) (x : Mat k r) :
    s * x ∈ GG k r ↔ x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x := by
    rw [conjTranspose_mul]
    conv_rhs => rw [← hs']
    simp only [Matrix.mul_assoc]
  show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r
  rw [this]

theorem measurable_G (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  refine IsClosed.measurableSet ?_
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact isClosed_eq (f := fun x : Mt k r => (Matrix.of x : Mat k r)ᴴ * Hpk k r * Matrix.of x)
    ((h.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h) continuous_const

theorem continuous_act (k r : ℕ) :
    Continuous (Function.uncurry fun s x : Mt k r => lmulM (Matrix.of s) x) := by
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact (h.comp continuous_fst).matrix_mul (h.comp continuous_snd)

theorem cut_quotient : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  intro k r R μG μR ν hR hG hμ hU hW
  haveI := hG.1
  haveI := hμ.1
  set T : Mt k r → Mt k r → Mt k r := fun s x => lmulM (Matrix.of s) x with hT
  have hTm : Measurable (Function.uncurry T) := (continuous_act k r).measurable
  have hae : ∀ᵐ s ∂μR, s ∈ {x : Mt k r | Matrix.of x ∈ R} := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν := hW
  have hmem : ∀ s : Mt k r, Matrix.of s ∈ R → ∀ x : Mt k r,
      (Matrix.of (T s x) ∈ GG k r ↔ Matrix.of x ∈ GG k r) := fun s hs x =>
    mul_mem_iff (hR.1 hs) (Matrix.of x)
  have h1 : ν {x | Matrix.of x ∉ GG k r} = 0 :=
    null_of_stable hae hμ.2.1 hW' (measurable_G k r).compl
      (fun s hs x hx h => hx ((hmem s hs x).1 h)) hG.2.2.1
  have h1' : ∀ᵐ x ∂ν, x ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := h1
  refine ⟨h1, fun A hA hst hn => ?_, ?_⟩
  · have h2 : ν (A ∩ {x : Mt k r | Matrix.of x ∈ GG k r}) = 0 :=
      null_of_stable hae hμ.2.1 hW' (hA.inter (measurable_G k r))
        (fun s hs x hx => ⟨(hst _ hs x hx.2).2 hx.1, (hmem s hs x).2 hx.2⟩)
        (measure_mono_null Set.inter_subset_left hn)
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h2 h1)
    by_cases h : Matrix.of x ∈ GG k r
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  · obtain ⟨φ, hφ, hle, hF⟩ := exists_cut hTm hae hμ.2.1 hW' h1' (by
      intro ρ hρ x f hf
      have hTx : Measurable fun s => T s x := hTm.comp (measurable_id.prodMk measurable_const)
      have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
      have hr : Measurable (rmulM (k := k) (r := r) (Matrix.of ρ)) :=
        by
        have hc' : Continuous (rmulM (k := k) (r := r) (Matrix.of ρ)) := hc.matrix_mul continuous_const
        exact hc'.measurable
      conv_rhs => rw [← hU.1 (Matrix.of ρ) hρ]
      rw [lintegral_map (f := fun s => f (T s x)) (hf.comp hTx) hr]
      refine lintegral_congr fun s => congrArg f ?_
      exact (Matrix.mul_assoc (Matrix.of s) (Matrix.of ρ) (Matrix.of x)).symm)
    exact ⟨φ, ⟨hφ, fun x _ => hle x⟩, fun F hFm hFi => hF F hFm fun ρ hρ x hx => hFi _ hρ x hx⟩

end GlobalTheory.Amp.CutQuot
