import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedCutoffStatement

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.QuotRightInv

open PI

theorem measurable_mul_left {m : ℕ} (x : MtM m) :
    Measurable (fun s : MtM m => (fun i j => (Matrix.of s * Matrix.of x) i j : MtM m)) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurable_rmulQ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : Measurable (rmulQ g) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rmulQ, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurableSet_not_mem {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) :
    MeasurableSet {x : MtM m | Matrix.of x ∉ G} := by
  have hc : IsClosed {x : MtM m | Matrix.of x ∈ G} := by
    have hof : Continuous (fun x : MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
    exact hG.1.preimage hof
  exact hc.measurableSet.compl

private lemma mul_not_mem_of_mem_of_not_mem {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G)
    (hSG : S ⊆ G) {s x : Matrix (Fin m) (Fin m) ℂ} (hs : s ∈ S) (hx : x ∉ G) : s * x ∉ G := by
  intro hsx
  apply hx
  obtain ⟨hinv, hone⟩ := hG.2.2.2 s (hSG hs)
  have hleft : s⁻¹ * s = 1 := mul_eq_one_comm.mp hone
  have h1 := hG.2.2.1 _ hinv _ hsx
  rwa [← Matrix.mul_assoc, hleft, Matrix.one_mul] at h1

private lemma continuous_mul_swap_pair {m : ℕ} :
    Continuous (fun p : MtM m × MtM m => (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : MtM m)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem ae_mem_of_quot {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
    (h : QuotientSetting G S μG μS ν) : ∀ᵐ x ∂ν, Matrix.of x ∈ G := by
  obtain ⟨hG, hS, hSG, hHG, hHS, -, -, hQ⟩ := h
  have : SigmaFinite μS := hHS.1
  have hBm : MeasurableSet {x : MtM m | Matrix.of x ∉ G} := measurableSet_not_mem hG
  have hSm : MeasurableSet {x : MtM m | Matrix.of x ∈ S} := by
    have h1 := (measurableSet_not_mem hS).compl
    simpa only [Set.compl_setOf, not_not] using h1
  have hf : Measurable ({x : MtM m | Matrix.of x ∉ G}.indicator (1 : MtM m → ℝ≥0∞)) :=
    measurable_one.indicator hBm
  have h0 := hQ _ hf
  rw [lintegral_indicator_one hBm, hHG.2.2.1] at h0
  have hinner : Measurable fun x : MtM m =>
      ∫⁻ s, {x : MtM m | Matrix.of x ∉ G}.indicator (1 : MtM m → ℝ≥0∞)
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS :=
    Measurable.lintegral_prod_right (hf.comp continuous_mul_swap_pair.measurable)
  have hae := (lintegral_eq_zero_iff hinner).mp h0.symm
  have hSpos : μS {s : MtM m | Matrix.of s ∈ S} ≠ 0 := by
    intro hz
    apply hHS.2.1
    rw [← Measure.measure_univ_eq_zero]
    have hu := measure_union_le (μ := μS) {s : MtM m | Matrix.of s ∈ S} {s : MtM m | Matrix.of s ∈ S}ᶜ
    rw [Set.union_compl_self] at hu
    have hc : μS {s : MtM m | Matrix.of s ∈ S}ᶜ = 0 := hHS.2.2.1
    rw [hz, hc, add_zero] at hu
    exact le_antisymm hu zero_le
  filter_upwards [hae] with x hx
  by_contra hxG
  apply hSpos
  refine le_antisymm ?_ zero_le
  refine le_trans ?_ (le_of_eq hx)
  rw [← lintegral_indicator_one hSm]
  refine lintegral_mono fun s => ?_
  by_cases hs : Matrix.of s ∈ S
  · have hs' : s ∈ {s : MtM m | Matrix.of s ∈ S} := hs
    have hmem : (fun i j => (Matrix.of s * Matrix.of x) i j : MtM m) ∈ {x : MtM m | Matrix.of x ∉ G} :=
      mul_not_mem_of_mem_of_not_mem hG hSG hs hxG
    have e1 : {s : MtM m | Matrix.of s ∈ S}.indicator (1 : MtM m → ℝ≥0∞) s = 1 :=
      Set.indicator_of_mem hs' _
    have e2 : {x : MtM m | Matrix.of x ∉ G}.indicator (1 : MtM m → ℝ≥0∞)
        (fun i j => (Matrix.of s * Matrix.of x) i j) = 1 := Set.indicator_of_mem hmem _
    exact (e1.trans e2.symm).le
  · have e1 : {s : MtM m | Matrix.of s ∈ S}.indicator (1 : MtM m → ℝ≥0∞) s = 0 :=
      Set.indicator_apply_eq_zero.mpr fun h' => absurd h' hs
    exact e1.trans_le zero_le

theorem lintegral_eq_cutoff {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν : Measure (MtM m)}
    (h : QuotientSetting G S μG μS ν) (φ : MtM m → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∀ x : MtM m, Matrix.of x ∈ G →
      ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1)
    (F : MtM m → ℝ≥0∞) (hF : Measurable F)
    (hFS : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x) :
    ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  have hνG := ae_mem_of_quot h
  obtain ⟨hG, hS, hSG, hHG, hHS, hRG, hRS, hQ⟩ := h
  rw [hQ (fun x => φ x * F x) (hφ.mul hF)]
  refine lintegral_congr_ae ?_
  filter_upwards [hνG] with x hx
  have hSae : ∀ᵐ s ∂μS, Matrix.of s ∈ S := ae_iff.mpr hHS.2.2.1
  have e : ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) *
        F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS
      = ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) * F x ∂μS := by
    refine lintegral_congr_ae ?_
    filter_upwards [hSae] with s hs
    rw [hFS _ hs x hx]
  rw [e, lintegral_mul_const (f := fun s : MtM m => φ (fun i j => (Matrix.of s * Matrix.of x) i j)) _
    (hφ.comp (measurable_mul_left x)), hφ1 x hx, one_mul]

theorem quotInv : PI.QuotInv := by
  intro m G S μG μS ν h F hF hFS g hg
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.T.exists_normalised_cutoff' m G S μS h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1
  have hG : IsMatGroup G := h.1
  have hxg : ∀ x : MtM m, Matrix.of x ∈ G →
      Matrix.of (fun i j => (Matrix.of x * g) i j : MtM m) ∈ G := fun x hx => hG.2.2.1 _ hx _ hg
  have hφ' : Measurable (fun x : MtM m => φ (fun i j => (Matrix.of x * g) i j)) :=
    hφ.comp (measurable_rmulQ g)
  have hφ'1 : ∀ x : MtM m, Matrix.of x ∈ G →
      ∫⁻ s, (fun x : MtM m => φ (fun i j => (Matrix.of x * g) i j))
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
    intro x hx
    rw [← hφ1 _ (hxg x hx)]
    refine lintegral_congr fun s => ?_
    show φ _ = φ _
    congr 1
    change (Matrix.of s * Matrix.of x) * g = Matrix.of s * (Matrix.of x * g)
    exact Matrix.mul_assoc _ _ _
  have hFg : Measurable (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) :=
    hF.comp (measurable_rmulQ g)
  have hFgS : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G →
      (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) (fun i j => (s * Matrix.of x) i j) =
        (fun x : MtM m => F (fun i j => (Matrix.of x * g) i j)) x := by
    intro s hs x hx
    have key := hFS s hs _ (hxg x hx)
    refine Eq.trans ?_ key
    show F _ = F _
    congr 1
    change (s * Matrix.of x) * g = s * (Matrix.of x * g)
    exact Matrix.mul_assoc _ _ _
  have e1 := lintegral_eq_cutoff h _ hφ' hφ'1 _ hFg hFgS
  have e2 := lintegral_eq_cutoff h φ hφ hφ1 F hF hFS
  refine e1.trans (Eq.trans ?_ e2.symm)
  calc ∫⁻ x, φ (fun i j => (Matrix.of x * g) i j) * F (fun i j => (Matrix.of x * g) i j) ∂μG
      = ∫⁻ x, (fun y => φ y * F y) (rmulQ g x) ∂μG := rfl
    _ = ∫⁻ x, (fun y => φ y * F y) x ∂(μG.map (rmulQ g)) :=
        (lintegral_map (hφ.mul hF) (measurable_rmulQ g)).symm
    _ = ∫⁻ x, φ x * F x ∂μG := by rw [h.2.2.2.2.2.1 g hg]

end GlobalTheory.QuotRightInv
