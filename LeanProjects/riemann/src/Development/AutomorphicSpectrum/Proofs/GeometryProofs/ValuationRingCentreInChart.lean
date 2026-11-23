import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DomBy
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalizationStatement

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

theorem isUnit_valuationSubring_iff {Ω' : Type} [Field Ω'] (W : ValuationSubring Ω') (w : W) :
    IsUnit w ↔ (w : Ω') ≠ 0 ∧ (w : Ω')⁻¹ ∈ W := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_right_inv
    have hv' : (w : Ω') * (v : Ω') = 1 := congrArg Subtype.val hv
    refine ⟨left_ne_zero_of_mul_eq_one hv', ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hv']
    exact v.2
  · rintro ⟨h0, h1⟩
    refine IsUnit.of_mul_eq_one (⟨(w : Ω')⁻¹, h1⟩ : W) (Subtype.ext ?_)
    exact mul_inv_cancel₀ h0

theorem exists_domBy_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω Ω' : Type) [Field Ω] [Field Ω'] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (i : Ω →+* Ω') (W : ValuationSubring Ω') (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k j, i (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ W) → ∃ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q ∧ DomBy W.toSubring i ξ q := by
  intro K _ J _ Ω Ω' _ _ y X ξ hall htie i W c hy hW
  classical
  let x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩
  let M : PModel ℤ x :=
    { X := X
      ξ := ξ
      s := specZIsTerminal.from _
      hover := specZIsTerminal.hom_ext _ _
      all := hall
      tie := htie }
  have hxc : x c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have hch : ∀ a ∈ chRing ℤ x c, i a ∈ W := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a h =>
      obtain ⟨j, rfl⟩ := h
      have e : x j / x c = ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) := by
        simp only [x, Finset.prod_div_distrib]
      show i (x j / x c) ∈ W
      rw [e, map_prod]
      exact prod_mem fun k _ => hW k (j k)
    | algebraMap r =>
      rw [eq_intCast, map_intCast]
      exact intCast_mem W r
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  let φ : chRing ℤ x c →+* W :=
    (i.comp (chRing ℤ x c).toSubring.subtype).codRestrict W.toSubring fun a => hch a a.2
  let P : Ideal (chRing ℤ x c) := (IsLocalRing.maximalIdeal W).comap φ
  have hPp : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨q, ⟨hq, hP⟩, -⟩ := GlobalTheory.T.chart_prime_existsUnique_point ℤ Ω _ x M c hxc P hPp
  have hu : ∀ u (hu : u ∈ chRing ℤ x c), i u ≠ 0 → (i u)⁻¹ ∈ W → unitAt M.ξ q u := by
    intro u hu h0 h1
    by_contra hn
    have hm : (⟨u, hu⟩ : chRing ℤ x c) ∈ P := (hP ⟨u, hu⟩).2 hn
    exact (IsLocalRing.mem_maximalIdeal _).1 hm
      ((isUnit_valuationSubring_iff W (φ ⟨u, hu⟩)).2 ⟨h0, h1⟩)
  have hv : ∀ v (hv : v ∈ chRing ℤ x c), unitAt M.ξ q v → (i v)⁻¹ ∈ W := by
    intro v hv h
    have hm : (⟨v, hv⟩ : chRing ℤ x c) ∉ P := fun hm => (hP ⟨v, hv⟩).1 hm h
    have : IsUnit (φ ⟨v, hv⟩) := by
      by_contra hn
      exact hm ((IsLocalRing.mem_maximalIdeal _).2 hn)
    exact ((isUnit_valuationSubring_iff W (φ ⟨v, hv⟩)).1 this).2
  have hdesc := (GlobalTheory.T.regAt_chart_localization ℤ Ω _ x M c q hq).2
  refine ⟨q, hq, fun a ha => ?_, fun a ha ha0 hinv => ?_⟩
  · obtain ⟨u, huc, v, hvc, hvu, rfl⟩ := (hdesc a).1 ha
    rw [map_div₀, div_eq_mul_inv]
    exact mul_mem (hch u huc) (hv v hvc hvu)
  · obtain ⟨u, huc, v, hvc, hvu, rfl⟩ := (hdesc a).1 ha
    have hv0 : v ≠ 0 := hvu.1
    have hu0 : u ≠ 0 := fun h => ha0 (by rw [h, zero_div])
    have hiu : i u ≠ 0 := (map_ne_zero i).2 hu0
    have hiv : i v ≠ 0 := (map_ne_zero i).2 hv0
    have e : (i u)⁻¹ = (i (u / v))⁻¹ * (i v)⁻¹ := by
      rw [map_div₀]
      field_simp
    have hU : unitAt M.ξ q u := hu u huc hiu (e ▸ mul_mem hinv (hv v hvc hvu))
    have e2 : (u / v)⁻¹ = v * u⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    rw [e2]
    exact mul_mem hvu.2.1 hU.2.2

end GlobalTheory.CompanionTheory.Ar.OrVert
