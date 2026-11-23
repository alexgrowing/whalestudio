import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holoOn_eval {σ : Type} (A : FinHolAtlas e X) {W : Set X} {b : X → σ → ℂ}
    (hb : ∀ q, A.HoloOn W fun y => b y q) (p : MvPolynomial σ ℤ) :
    A.HoloOn W fun y => eval (b y) (map (Int.castRingHom ℂ) p) := by
  intro j
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [Function.comp_def] using
      (analyticOnNhd_const (v := ((a : ℤ) : ℂ)) (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' W))
  | add p q hp hq =>
    convert hp.add hq using 1
    funext u
    simp [Function.comp_def]
  | mul_X p q hp =>
    simpa [Function.comp_def] using hp.mul (hb q j)

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f) {y : X}
    (hy : y ∈ W) : ContinuousAt f y := by
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : (A.chart j) y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact hy⟩
  have h2 : ContinuousAt (f ∘ (A.chart j).symm) ((A.chart j) y) := (hf j _ h1).continuousAt
  have h3 : ContinuousAt (fun u => (f ∘ (A.chart j).symm) ((A.chart j) u)) y :=
    ContinuousAt.comp (f := A.chart j) h2 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with u hu
  simp only [Function.comp_apply, (A.chart j).left_inv hu]

theorem isOpen_inter_ne (A : FinHolAtlas e X) {W : Set X} {f : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) : IsOpen (W ∩ {y | f y ≠ 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hy, h0⟩
  filter_upwards [hW.mem_nhds hy, (continuousAt_of_holoOn A hf hy).eventually_ne h0] with u h1 h2
  exact ⟨h1, h2⟩

theorem holoOn_div_congr (A : FinHolAtlas e X) {W : Set X} {f g v : X → ℂ} (hW : IsOpen W)
    (hf : A.HoloOn W f) (hg : A.HoloOn W g) (h0 : ∀ y ∈ W, g y ≠ 0) (hv : ∀ y ∈ W, v y = f y / g y) :
    A.HoloOn W v := by
  intro j
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  have h1 : AnalyticOnNhd ℂ (fun u => (f ∘ (A.chart j).symm) u / (g ∘ (A.chart j).symm) u)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) := fun u hu =>
    (hf j u hu).div (hg j u hu) (h0 _ hu.2)
  exact h1.congr hO fun u hu => (hv _ hu.2).symm

theorem holoOn_valAt (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (x : (Σ k, ι k) → Ω) (s : Ω) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (W : Set X)
    (b : X → (Σ k, ι k) → ℂ) (y₀ : X) (hW : IsOpen W) (hy₀ : y₀ ∈ W) (hb : ∀ q, A.HoloOn W fun y => b y q)
    (hpt : ∀ y ∈ W, b y ∈ mcPts (mCoordIdeal x)) (hs : RegAt x (mCoordIdeal (b y₀)) s) :
    ∃ W' : Set X, IsOpen W' ∧ y₀ ∈ W' ∧ W' ⊆ W ∧ A.HoloOn W' fun y => valAt x s (b y) := by
  obtain ⟨d, g, h, hg, hh, hQ, heq⟩ := hs
  have hz : eval (b y₀) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    refine hQ (mem_mCoordIdeal_of_aeval_eq_zero (b y₀) hh ?_)
    rw [← h0]
    rw [aeval_def, eval_map, Subsingleton.elim (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]
  have hx : aeval x h ≠ 0 := fun h0 =>
    hz (eval_eq_zero_of_mem_mcPts (hpt y₀ hy₀) (mem_mCoordIdeal_of_aeval_eq_zero x hh h0))
  have Hg := holoOn_eval A hb g
  have Hh := holoOn_eval A hb h
  refine ⟨W ∩ {y | eval (b y) (map (Int.castRingHom ℂ) h) ≠ 0}, isOpen_inter_ne A hW Hh, ⟨hy₀, hz⟩,
    Set.inter_subset_left, ?_⟩
  refine holoOn_div_congr A (isOpen_inter_ne A hW Hh) (fun j => (Hg j).mono ?_) (fun j => (Hh j).mono ?_)
    (fun y hy => hy.2) fun y hy => ?_
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left)
  · exact valAt_eq (hpt y hy.1) ⟨d, g, h, hg, hh, hx, heq, hy.2, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo
