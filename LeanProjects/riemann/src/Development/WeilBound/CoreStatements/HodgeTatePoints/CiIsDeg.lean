import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HodgeTatePoints.OfMem

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

theorem chart_block {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {B : Type} [Fintype B]
    {J : B → Type} {y : (Σ k, J k) → Ω} {c : (k : B) → J k} {p : Cpt ξ} (hc : InChart ξ (segre y) c p) (k : B) :
    y ⟨k, c k⟩ ≠ 0 ∧ ∀ j, y ⟨k, j⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  refine ⟨h0 k, fun j => ?_⟩
  have h1 := hc.2 (Function.update c k j)
  rw [Conj.segre, Conj.segre, ← Finset.prod_div_distrib, Finset.prod_eq_single k (fun l _ hl => by
    rw [Function.update_of_ne hl, div_self (h0 l)]) (by simp), Function.update_self] at h1
  exact h1

theorem isdeg_coord : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) := by
  intro X Ω _ ξ K _ C z Y B _ J _ y w Λ S a e₀ h₀ h tie hw hz hS hΛ
  classical
  have hξ := tie.gen
  have hval : ∀ k c, w ⟨k, c⟩ ≠ 0 → y ⟨k, c⟩ ≠ 0 ∧ ∀ j, ValAt ξ z (y ⟨k, j⟩ / y ⟨k, c⟩) (w ⟨k, j⟩ / w ⟨k, c⟩) := by
    intro k c hc
    obtain ⟨h1, h2⟩ := hw.2 k c (IsUnit.mk0 _ hc)
    refine ⟨h1, fun j => ?_⟩
    obtain ⟨r, hr, e⟩ := h2 j
    rwa [e, mul_div_cancel_right₀ _ hc]
  choose c₀ hc₀ using hw.1
  replace hc₀ := fun k => (hc₀ k).ne_zero
  have ch₀ : InChart ξ (segre y) c₀ ⟨centre z, h₀⟩ := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (hval k _ (hc₀ k)).1, fun c' => ?_⟩
    rw [Conj.segre, Conj.segre, ← Finset.prod_div_distrib]
    exact prod_mem fun k _ => Val.mem ((hval k _ (hc₀ k)).2 _) h₀
  choose c hc using fun i => tie.cover ⟨centre (Y.x i), h i⟩
  have hint : ∀ i k j, ∃ ρ : K, C.v i ρ ≤ 1 ∧ ValAt ξ z (y ⟨k, j⟩ / y ⟨k, c i k⟩) ρ := by
    intro i k j
    obtain ⟨ρ, hρ⟩ := Val.of_mem ((chart_block (hc i) k).2 j)
    have := LieTangent.valAt_base hξ (C.v i).valuationSubring.subtype hρ
    rw [Y.gen i] at this
    exact ⟨_, ρ.2, this⟩
  have hne : ∀ i k, w ⟨k, c i k⟩ ≠ 0 := by
    intro i k h0
    obtain ⟨ρ, -, hρ⟩ := hint i k (c₀ k)
    have h1 := Val.mul hρ ((hval k _ (hc₀ k)).2 (c i k))
    rw [div_mul_div_cancel₀ (chart_block (hc i) k).1, div_self (hval k _ (hc₀ k)).1, h0, zero_div, mul_zero] at h1
    exact zero_ne_one (LieTangent.valAt_unique hξ h1 (Val.one h₀))
  have hsup : ∀ i k, (Finset.univ.sup fun j : J k => C.v i (w ⟨k, j⟩)) = C.v i (w ⟨k, c i k⟩) := by
    intro i k
    refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j : J k => C.v i (w ⟨k, j⟩))
      (Finset.mem_univ _))
    obtain ⟨ρ, h1, hρ⟩ := hint i k j
    rw [LieTangent.valAt_unique hξ hρ ((hval k _ (hne i k)).2 j), map_div₀] at h1
    exact (div_le_one₀ ((C.v i).pos_iff.2 (hne i k))).1 h1
  have hgen : ∀ p ∈ S, ∀ c, InChart ξ (segre y) c p → Λ.IsGenAt p ((∏ k, y ⟨k, c k⟩ ^ a k) * e₀) := fun p hp c hc =>
    ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (chart_block hc k).1) hΛ.1, hΛ.2 p hp c hc⟩
  have hF : (⋃ q : {q : Σ k, J k // w q ≠ 0}, {i | C.v i (w q.1) ≠ 1}).Finite :=
    Set.finite_iUnion fun q => C.fin _ q.2
  have hgood : ∀ i ∉ hF.toFinset, ∀ q, w q ≠ 0 → C.v i (w q) = 1 := by
    intro i hi q hq
    by_contra hcon
    exact hi (hF.mem_toFinset.2 (Set.mem_iUnion.2 ⟨⟨q, hq⟩, hcon⟩))
  have hfs : ∀ f : C.I → ℤ, (∀ i ∉ hF.toFinset, f i = 0) → ∑ᶠ i, f i = ∑ i ∈ hF.toFinset, f i := fun f hf =>
    finsum_eq_sum_of_support_subset f fun i hi => by_contra fun hc => hi (hf i hc)
  have hr : ∀ i ∉ hF.toFinset, C.v i (∏ k, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k) = 1 := by
    intro i hi
    simp only [map_prod, map_zpow₀, map_div₀, hgood i hi _ (hne i _), hgood i hi _ (hc₀ _), div_one, one_zpow,
      Finset.prod_const_one]
  refine ⟨h₀, h, _, _, fun i => ∏ k, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k, hgen _ hz _ ch₀,
    fun i => hgen _ (hS i) _ (hc i), fun i => ⟨Finset.prod_ne_zero_iff.2 fun k _ =>
      zpow_ne_zero _ (div_ne_zero (hne i k) (hc₀ k)), ?_⟩, hF.subset fun i hi => ?_, ?_⟩
  · rw [mul_div_mul_right _ _ hΛ.1, ← Finset.prod_div_distrib]
    refine Val.prod h₀ _ fun k => ?_
    rw [← div_zpow]
    refine Val.zpow ((hval k _ (hc₀ k)).2 _) ?_ _
    rw [inv_div, inv_div]
    exact (hval k _ (hne i k)).2 _
  · by_contra hcon
    exact hi (hr i fun h' => hcon (hF.mem_toFinset.1 h'))
  · have hlog : ∀ i, WithZero.log (C.v i (∏ k, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k)) =
        ∑ k, a k * (WithZero.log (C.v i (w ⟨k, c i k⟩)) - WithZero.log (C.v i (w ⟨k, c₀ k⟩))) := by
      intro i
      have key : ∀ T : Finset B, WithZero.log (C.v i (∏ k ∈ T, (w ⟨k, c i k⟩ / w ⟨k, c₀ k⟩) ^ a k)) =
          ∑ k ∈ T, a k * (WithZero.log (C.v i (w ⟨k, c i k⟩)) - WithZero.log (C.v i (w ⟨k, c₀ k⟩))) := by
        intro T
        induction T using Finset.induction_on with
        | empty => simp
        | insert k T hk ih =>
          rw [Finset.prod_insert hk, Finset.sum_insert hk, map_mul, WithZero.log_mul, ih, map_zpow₀,
            WithZero.log_zpow, map_div₀, WithZero.log_div, smul_eq_mul]
          · exact (Valuation.ne_zero_iff _).2 (hne i k)
          · exact (Valuation.ne_zero_iff _).2 (hc₀ k)
          · exact (Valuation.ne_zero_iff _).2 (zpow_ne_zero _ (div_ne_zero (hne i k) (hc₀ k)))
          · exact (Valuation.ne_zero_iff _).2 (Finset.prod_ne_zero_iff.2 fun k _ =>
              zpow_ne_zero _ (div_ne_zero (hne i k) (hc₀ k)))
      exact key _
    have hp : ∀ k, ∑ i ∈ hF.toFinset, (C.w i : ℤ) * WithZero.log (C.v i (w ⟨k, c₀ k⟩)) = 0 := fun k => by
      rw [← hfs _ fun i hi => by rw [hgood i hi _ (hc₀ k)]; simp]
      exact C.prod _ (hc₀ k)
    rw [hfs _ fun i hi => by rw [hr i hi]; simp]
    simp only [coordDeg, hsup, hlog, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hfs _ fun i hi => by rw [hgood i hi _ (hne i k)]; simp]
    simp only [mul_left_comm _ (a k), mul_sub, ← Finset.mul_sum, Finset.sum_sub_distrib, hp, mul_zero, sub_zero]

end PositivityTheory.HtPt.Ci
