import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum

variable {L : Type} [Field L] [NumberField L]

theorem finsum_log_add_sum_log {x : L} (hx : x ≠ 0) :
    ∑ᶠ v : FinitePlace L, Real.log (v x) + ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = 0 := by
  have hmul : (Function.mulSupport fun v : FinitePlace L => v x).Finite :=
    FinitePlace.hasFiniteMulSupport hx
  have h1 : ∑ᶠ v : FinitePlace L, Real.log (v x) = Real.log (∏ᶠ v : FinitePlace L, v x) := by
    rw [finsum_eq_sum_of_support_subset (s := hmul.toFinset),
      finprod_eq_prod_of_mulSupport_subset (s := hmul.toFinset) _ (by simp),
      Real.log_prod (fun v _ => (FinitePlace.pos_iff.2 hx).ne')]
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hv
    simp [h1]
  have h2 : ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    classical
    rw [← Real.log_prod fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx), ← norm_prod]
    have h3 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
    have h4 : ∏ σ : L →+* ℂ, σ x = ∏ σ : L →ₐ[ℚ] ℂ, σ x :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ fun σ => (DFunLike.congr rfl rfl)
    rw [h4, ← h3, eq_ratCast, Complex.norm_ratCast]
  rw [h1, h2, FinitePlace.prod_eq_inv_abs_norm hx]
  push_cast
  rw [Real.log_inv, neg_add_cancel]

theorem support_log_finite {x : L} (hx : x ≠ 0) :
    (Function.support fun v : FinitePlace L => Real.log (v x)).Finite := by
  refine (show (Function.mulSupport fun v : FinitePlace L => v x).Finite from
    FinitePlace.hasFiniteMulSupport hx).subset fun v hv h => hv ?_
  simp [show v x = 1 from h]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def badPlaces (w : (Σ k, J k) → L) : Set (FinitePlace L) :=
  ⋃ p : Σ k, J k, {v | w p ≠ 0 ∧ v (w p) ≠ 1}

theorem badPlaces_finite (w : (Σ k, J k) → L) : (badPlaces w).Finite := by
  refine Set.finite_iUnion fun p => ?_
  by_cases hp : w p = 0
  · exact Set.finite_empty.subset fun v hv => hv.1 hp
  · refine (show (Function.mulSupport fun v : FinitePlace L => v (w p)).Finite from
      FinitePlace.hasFiniteMulSupport hp).subset fun v hv => hv.2

theorem eq_one_of_notMem {w : (Σ k, J k) → L} {v : FinitePlace L} (hv : v ∉ badPlaces w)
    {p : Σ k, J k} (hp : w p ≠ 0) : v (w p) = 1 := by
  by_contra h
  exact hv (Set.mem_iUnion.2 ⟨p, hp, h⟩)

theorem le_iSup_place (w : (Σ k, J k) → L) (v : FinitePlace L) (k : K) (c : J k) :
    v (w ⟨k, c⟩) ≤ ⨆ i, v (w ⟨k, i⟩) :=
  le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove c

theorem iSup_place_pos {w : (Σ k, J k) → L} (v : FinitePlace L) {k : K} (h : ∃ c, w ⟨k, c⟩ ≠ 0) :
    0 < ⨆ i, v (w ⟨k, i⟩) := by
  obtain ⟨c, hc⟩ := h
  exact (FinitePlace.pos_iff.2 hc).trans_le (le_iSup_place w v k c)

theorem iSup_place_eq_one {w : (Σ k, J k) → L} {v : FinitePlace L} (hv : v ∉ badPlaces w) {k : K}
    (h : ∃ c, w ⟨k, c⟩ ≠ 0) : ⨆ i, v (w ⟨k, i⟩) = 1 := by
  obtain ⟨c, hc⟩ := h
  haveI : Nonempty (J k) := ⟨c⟩
  refine le_antisymm (ciSup_le fun i => ?_) ?_
  · by_cases hi : w ⟨k, i⟩ = 0
    · rw [hi, map_zero]; exact zero_le_one
    · exact (eq_one_of_notMem hv hi).le
  · rw [← eq_one_of_notMem hv hc]
    exact le_iSup_place w v k c

theorem log_locRatio (a : K → ℤ) {w : (Σ k, J k) → L} (c₀ : (k : K) → J k)
    (h : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) (h₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0) (v : FinitePlace L) :
    Real.log (locRatio a w c₀ v) =
      (∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) -
        ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩)) := by
  unfold locRatio
  rw [Real.log_prod fun k _ => zpow_ne_zero _
    (div_ne_zero (iSup_place_pos v (h k)).ne' (FinitePlace.pos_iff.2 (h₀ k)).ne'),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.log_zpow, Real.log_div (iSup_place_pos v (h k)).ne' (FinitePlace.pos_iff.2 (h₀ k)).ne',
    mul_sub]

theorem ratio_sum (L : Type) [Field L] [NumberField L] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (a : K → ℤ) (w : (Σ k, J k) → L) (c₀ : (k : K) → J k) (u : L) :
    (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → u ≠ 0 →
    (∀ v, 0 < locRatio a w c₀ v) ∧ (Function.mulSupport (locRatio a w c₀)).Finite ∧
    ∑ᶠ v : FinitePlace L, (Real.log (locRatio a w c₀ v) - Real.log (v u)) =
      (∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
        ∑ σ : L →+* ℂ, (Real.log ‖σ u‖ + ∑ k, (a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖) := by
  intro h h₀ hu
  refine ⟨fun v => ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun k _ => zpow_pos
      (div_pos (iSup_place_pos v (h k)) (FinitePlace.pos_iff.2 (h₀ k))) _
  · refine (badPlaces_finite w).subset fun v hv => ?_
    by_contra hb
    apply hv
    unfold locRatio
    refine Finset.prod_eq_one fun k _ => ?_
    rw [iSup_place_eq_one hb (h k), eq_one_of_notMem hb (h₀ k)]
    simp
  · have hS : (Function.support fun v : FinitePlace L =>
        ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))).Finite := by
      refine (badPlaces_finite w).subset fun v hv => ?_
      by_contra hb
      apply hv
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [iSup_place_eq_one hb (h k), Real.log_one, mul_zero]
    have hT1 : ∀ k, (Function.support fun v : FinitePlace L =>
        (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩))).Finite := fun k =>
      (support_log_finite (h₀ k)).subset fun v hv hz => hv (by simp [show Real.log (v (w ⟨k, c₀ k⟩)) = 0 from hz])
    have hT : (Function.support fun v : FinitePlace L =>
        ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩))).Finite := by
      refine (Set.finite_iUnion hT1).subset fun v hv => ?_
      by_contra hb
      apply hv
      refine Finset.sum_eq_zero fun k _ => ?_
      by_contra hk
      exact hb (Set.mem_iUnion.2 ⟨k, hk⟩)
    have hTsum : ∑ᶠ v : FinitePlace L, ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩)) =
        -∑ k, (a k : ℝ) * ∑ σ : L →+* ℂ, Real.log ‖σ (w ⟨k, c₀ k⟩)‖ := by
      rw [finsum_sum_comm _ _ fun k _ => hT1 k, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_finsum,
        eq_neg_of_add_eq_zero_left (finsum_log_add_sum_log (h₀ k)), mul_neg]
    have hu' := eq_neg_of_add_eq_zero_left (finsum_log_add_sum_log hu)
    simp_rw [log_locRatio a c₀ h h₀]
    have hST := (hS.union hT).subset (Function.support_sub
      (fun v : FinitePlace L => ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)))
      (fun v : FinitePlace L => ∑ k, (a k : ℝ) * Real.log (v (w ⟨k, c₀ k⟩))))
    have hcomm : ∑ σ : L →+* ℂ, ∑ k, (a k : ℝ) * Real.log ‖σ (w ⟨k, c₀ k⟩)‖ =
        ∑ k, (a k : ℝ) * ∑ σ : L →+* ℂ, Real.log ‖σ (w ⟨k, c₀ k⟩)‖ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    rw [finsum_sub_distrib hST (support_log_finite hu), finsum_sub_distrib hS hT, hTsum, hu',
      Finset.sum_add_distrib, hcomm]
    ring

end GlobalTheory.CompanionTheory.Ar.RootHt.RatioSum
