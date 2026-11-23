import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConeAnalyticSubset
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hermLine_eq_of_a_h {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  obtain ⟨a, h, _, _⟩ := A
  obtain ⟨a', h', _, _⟩ := B
  subst ha
  subst hh
  rfl

theorem hpow.equiv (A B : HermLine ι) (j : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.hpow A j = HermLine.zcomb A B (j : ℤ) 0 := by
  refine hermLine_eq_of_a_h ?_ ?_
  · show (j : ℤ) • A.a = (j : ℤ) • A.a + (0 : ℤ) • B.a
    simp
  · funext z
    show A.h z ^ j = A.h z ^ (j : ℤ) * B.h z ^ (0 : ℤ)
    simp

theorem hpow_a_apply (A : HermLine ι) (τ : ℕ) (k : K) :
    (IndefiniteRowSideFullHecke.HilbertSamuel.hpow A τ).a k = τ * A.a k := by
  simp [IndefiniteRowSideFullHecke.HilbertSamuel.hpow]

theorem SupLE.equiv (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (c : ℝ) (s : Ω) :
    IsBoundedH P y A τ c s ↔
      IndefiniteRowSideFullHecke.HilbertSamuel.SupLE P y (IndefiniteRowSideFullHecke.HilbertSamuel.hpow A τ).a (IndefiniteRowSideFullHecke.HilbertSamuel.hpow A τ).h c s := by
  simp only [IsBoundedH, IndefiniteRowSideFullHecke.HilbertSamuel.SupLE, hpow_a_apply]
  rfl

theorem eval_eq_zero_of_aeval_eq_zero {y : (Σ k, ι k) → Ω} {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (h0 : aeval y h = 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) h) = 0 := by
  have hmem : h ∈ mCoordIdeal y := by
    show mConeMap y h = 0
    rw [ProjLine.mConeMap_eq_of_isMultiHomog y hh, h0, map_zero, zero_mul]
  exact hz.2 h hmem

theorem PtDominated.of_ptBoundOn {y : (Σ k, ι k) → Ω} {M L' : HermLine ι} {n : ℕ}
    {U : Set ((Σ k, ι k) → ℂ)} {c : ℝ} {f f' : Ω} (hB : PtBoundOn y M L' n U c f f') :
    ∀ z ∈ U, IndefiniteRowSideFullHecke.HilbertSamuel.PtDominated y (IndefiniteRowSideFullHecke.HilbertSamuel.hpow M n).a
      (IndefiniteRowSideFullHecke.HilbertSamuel.hpow L' n).a (IndefiniteRowSideFullHecke.HilbertSamuel.hpow M n).h (IndefiniteRowSideFullHecke.HilbertSamuel.hpow L' n).h
      c f f' z := by
  intro z hz g h g' h' ⟨dg, dh, hg, hh, hd, _, he⟩ ⟨dg', dh', hg', hh', hd', _, he'⟩ h0 h0'
  exact hB dg dh dg' dh' g h g' h' hg hh (fun k ↦ by rw [hd k, hpow_a_apply]) he hg' hh'
    (fun k ↦ by rw [hd' k, hpow_a_apply]) he' z hz h0 h0'

theorem PtDominated.equiv {y : (Σ k, ι k) → Ω} {M L' : HermLine ι} {n : ℕ}
    {U : Set ((Σ k, ι k) → ℂ)} (hU : U ⊆ mcPts (mCoordIdeal y)) (c : ℝ) (f f' : Ω) :
    PtBoundOn y M L' n U c f f' ↔
      ∀ z ∈ U, IndefiniteRowSideFullHecke.HilbertSamuel.PtDominated y (IndefiniteRowSideFullHecke.HilbertSamuel.hpow M n).a
        (IndefiniteRowSideFullHecke.HilbertSamuel.hpow L' n).a (IndefiniteRowSideFullHecke.HilbertSamuel.hpow M n).h (IndefiniteRowSideFullHecke.HilbertSamuel.hpow L' n).h
        c f f' z := by
  refine ⟨PtDominated.of_ptBoundOn, fun hT ↦ ?_⟩
  intro dg dh dg' dh' g h g' h' hg hh hd he hg' hh' hd' he' z hz h0 h0'
  have hy : aeval y h ≠ 0 := fun hy ↦ h0 (eval_eq_zero_of_aeval_eq_zero hh hy (hU hz))
  have hy' : aeval y h' ≠ 0 := fun hy ↦ h0' (eval_eq_zero_of_aeval_eq_zero hh' hy (hU hz))
  exact hT z hz g h g' h' ⟨dg, dh, hg, hh, fun k ↦ by rw [hd k, hpow_a_apply], hy, he⟩
    ⟨dg', dh', hg', hh', fun k ↦ by rw [hd' k, hpow_a_apply], hy', he'⟩ h0 h0'

theorem hHat0.equiv (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.hHat0 y A n = smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n :=
  rfl

theorem volHat.equiv (y : (Σ k, ι k) → Ω) (A : HermLine ι) (D : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.volHat y A D = arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D :=
  rfl

end Block

section OneBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem blockNonzero_eq_ne_zero :
    {z : Ix κ → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = {z | z ≠ 0} := by
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro h rfl
    obtain ⟨i, hi⟩ := h ()
    exact hi rfl
  · intro hz k
    obtain ⟨⟨⟨⟩, i⟩, hp⟩ := Function.ne_iff.mp hz
    cases k
    exact ⟨i, hp⟩

theorem IsHSDatum.equiv (D : ℕ) (x : Ix κ → Ω) (m : ConeMetric ℂ (Ix κ)) :
    IsGoodDatum D x m ↔ ∃ P₀, IndefiniteRowSideFullHecke.HilbertSamuel.IsHSDatum D x m P₀ := by
  constructor
  · rintro ⟨h1, ha, hi, _, hc, P₀, hle, hsp⟩
    exact ⟨P₀, ⟨h1, ha, hi, hle, hsp, hc⟩⟩
  · rintro ⟨P₀, ⟨h1, ha, hi, hle, hsp, hc⟩⟩
    refine ⟨h1, ha, hi, ?_, hc, P₀, hle, hsp⟩
    have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z : Ix κ → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hsp.1
    rw [blockNonzero_eq_ne_zero] at hs
    exact hs

end OneBlock

section Volume

@[reducible] def chartedSpaceOfAtlas {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) :
    ChartedSpace (Fin e → ℂ) X where
  atlas := Set.range A.chart
  chartAt x := A.chart (Classical.choose (A.cover x))
  mem_chart_source x := Classical.choose_spec (A.cover x)
  chart_mem_atlas _ := ⟨_, rfl⟩

theorem IsSmoothVolume.equiv {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] (A : FinHolAtlas e X)
    (dV : Measure X) :
    IsSmoothVolume A dV ↔ @IndefiniteRowSideFullHecke.HilbertSamuel.IsSmoothVolume e X _ (chartedSpaceOfAtlas A) _ dV := by
  unfold IsSmoothVolume IndefiniteRowSideFullHecke.HilbertSamuel.IsSmoothVolume
  refine and_congr_right fun _ ↦ ⟨fun h c hc ↦ ?_, fun h j ↦ ?_⟩
  · obtain ⟨j, rfl⟩ := hc
    obtain ⟨ν, h1, h2, h3⟩ := h j
    exact ⟨ν, h1, h2, fun S hS hsub ↦ by
      rw [h3 S hS hsub, (A.chart j).image_eq_target_inter_inv_preimage hsub]⟩
  · obtain ⟨ν, h1, h2, h3⟩ := h (A.chart j) ⟨j, rfl⟩
    exact ⟨ν, h1, h2, fun S hS hsub ↦ by
      rw [h3 S hS hsub, (A.chart j).image_eq_target_inter_inv_preimage hsub]⟩

end Volume

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
