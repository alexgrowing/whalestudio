import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverChart
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreSide
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsOrbitCompNonvanish
import GroundTheory.HeightsAndTheta.Heights.Intersections.NormSegreSameOrbit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GenericPointsInAffineChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [∀ k, Fintype (ι k)] in
open Classical in

theorem exists_normalise {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} (hP' : IsMultiHomogIdeal P') {j : ∀ k : FibreBlock κ, ι' k.1}
    {z : (Σ k, ι k) → ℂ} {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z' : (Σ k', ι' k') → ℂ} (hz' : z' ∈ mcPts P')
    (hzz : SameOrbit (fun p => z' (v p)) z) (hj : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) :
    ∃ d : K' → ℂ, (∀ k, d k ≠ 0) ∧ (fun q => d q.1 * z' q) ∈ mcPts P' ∧
      (∀ p, d (v p).1 * z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, d k.1 * z' ⟨k.1, j k⟩ = 1 := by
  obtain ⟨s, hs, hzs⟩ := hzz
  let d : K' → ℂ := fun k' =>
    if h : k' ∈ Set.range κ then c h.choose / s h.choose else (z' ⟨k', j ⟨k', h⟩⟩)⁻¹
  have hdk : ∀ k, d (κ k) = c k / s k := by
    intro k
    have h : κ k ∈ Set.range κ := ⟨k, rfl⟩
    have hk : h.choose = k := hv.1 h.choose_spec
    simp only [d, dif_pos h, hk]
  have hd : ∀ k, d k ≠ 0 := by
    intro k'
    by_cases h : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := h
      rw [hdk]
      exact div_ne_zero (hc k) (hs k)
    · simp only [d, dif_neg h]
      exact inv_ne_zero (hj ⟨k', h⟩)
  refine ⟨d, hd, mcPts_smul hP' d hd hz', fun p => ?_, fun k => ?_⟩
  · have h1 : z' (v p) = s p.1 * z p := congrFun hzs p
    rw [hv.2.2.1 p, hdk, h1]
    field_simp [hs p.1]
  · have h : k.1 ∉ Set.range κ := k.2
    simp only [d, dif_neg h]
    exact inv_mul_cancel₀ (hj k)

omit [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem eq_of_normalised {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {j : ∀ k : FibreBlock κ, ι' k.1} {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    {z₁ z₂ : (Σ k', ι' k') → ℂ} (h₁v : ∀ p, z₁ (v p) = w p) (h₁j : ∀ k : FibreBlock κ, z₁ ⟨k.1, j k⟩ = 1)
    (h₂v : ∀ p, z₂ (v p) = w p) (h₂j : ∀ k : FibreBlock κ, z₂ ⟨k.1, j k⟩ = 1) (h : SameOrbit z₁ z₂) :
    z₁ = z₂ := by
  obtain ⟨t, -, ht⟩ := h
  have ht1 : ∀ k', t k' = 1 := by
    intro k'
    by_cases hk : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := hk
      obtain ⟨i, hi⟩ := hw k
      have e := congrFun ht (v ⟨k, i⟩)
      simp only [h₁v, h₂v, hv.2.2.1] at e
      have e' : (t (κ k) - 1) * w ⟨k, i⟩ = 0 := by rw [sub_mul, ← e]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right hi)
    · have e := congrFun ht ⟨k', j ⟨k', hk⟩⟩
      have e1 : z₁ ⟨k', j ⟨k', hk⟩⟩ = 1 := h₁j ⟨k', hk⟩
      have e2 : z₂ ⟨k', j ⟨k', hk⟩⟩ = 1 := h₂j ⟨k', hk⟩
      simp only [e1, e2, mul_one] at e
      exact e.symm
  rw [ht]
  funext q
  simp [ht1]

end GenericPointsInAffineChart

open GenericPointsInAffineChart PullbackDegreeCount in

theorem GenericPointsInAffineChart.proof (hFin : ArithmeticIntersectionChartFinite.Statement) (hNorm : ChartNormCount.Statement)
    (hOrb : OrbitCompNonvanish.Statement) : GenericPointsInAffineChart.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hP hj
  obtain ⟨E, hE, hEw⟩ := hNorm K ι K' ι' κ v P' n G j hv hP' hP hj (hFin K ι K' ι' κ v P' n G j hv hP' hP hj)
  have hPh : IsMultiHomogIdeal (imageZ v P') := hP.2.1.2.1
  have hP'h : IsMultiHomogIdeal P' := hP'.2.1.2.1
  obtain ⟨D, a, hD, hDP, hDz⟩ := hOrb K ι (imageZ v P') E hPh hE
  refine ⟨D, a, hD, hDP, fun z hz hDz0 => ?_⟩
  obtain ⟨c, hc, hEc⟩ := hDz z hDz0
  have hw : (fun p => c p.1 * z p) ∈ mcPts (imageZ v P') := mcPts_smul hPh c hc hz
  obtain ⟨hfin, hcard, hnz⟩ := hEw _ hw hEc
  set N := {z' | z' ∈ mcPts P' ∧ (∀ p, z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ = 1} with hN
  let orb : ((Σ k', ι' k') → ℂ) → Set ((Σ k', ι' k') → ℂ) := fun z' => {z'' | SameOrbit z'' z'}
  have himg : ptsOverChart P' κ v j z = orb '' N := by
    ext O
    constructor
    · rintro ⟨z', hz', rfl, hzz, hjz⟩
      obtain ⟨d, hd, hm, hdv, hdj⟩ := exists_normalise hv hP'h hc hz' hzz hjz
      have hs : SameOrbit (fun q => d q.1 * z' q) z' := ⟨d, hd, rfl⟩
      refine ⟨_, ⟨hm, hdv, hdj⟩, ?_⟩
      ext y
      exact ⟨fun h => sameOrbit_comp h hs, fun h => sameOrbit_comp h (sameOrbit_flip hs)⟩
    · rintro ⟨z', ⟨hz', hzv, hzj⟩, rfl⟩
      refine ⟨z', hz', rfl, ⟨c, hc, funext hzv⟩, fun k => ?_⟩
      rw [hzj k]
      exact one_ne_zero
  have hinj : Set.InjOn orb N := by
    intro z₁ h₁ z₂ h₂ h12
    have hmem : z₁ ∈ orb z₁ := sameOrbit_self z₁
    rw [h12] at hmem
    exact eq_of_normalised hv hw.1 h₁.2.1 h₁.2.2 h₂.2.1 h₂.2.2 hmem
  refine ⟨himg ▸ hfin.image orb, ?_, fun z' hz' hzz hjz q hq => ?_⟩
  · rw [himg, hinj.ncard_image, hcard]
  · obtain ⟨d, hd, hm, hdv, hdj⟩ := exists_normalise hv hP'h hc hz' hzz hjz
    have h := hnz _ hm hdv hdj q hq
    exact right_ne_zero_of_mul h

end GroundTheory.Heights₂.Heights.Inter
