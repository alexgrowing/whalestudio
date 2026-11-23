import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NormValuation

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma exists_rat_norm_eq_rpow {p : ℕ} [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ t : ℚ, ‖x‖ = (p : ℝ) ^ (t : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hint hx
  refine ⟨(-((minpoly ℚ_[p] x).coeff 0).valuation : ℚ) / (minpoly ℚ_[p] x).natDegree, ?_⟩
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.NormValuation.main : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ ϖ : V, Irreducible ϖ → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ (PadicAlgCl p) v ∧ _root_.GlobalTheory.ZH.NormVal (algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)) v ∧ ∀ x : PadicAlgCl p, (0 ≤ v x ↔ ‖x‖ ≤ 1) ∧ (v x = 0 ↔ ‖x‖ = 1) := by
  intro p _ V _ _ _ _ hV ϖ hϖ
  set π : PadicAlgCl p :=
    algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ) with hπ
  have hinjV := IsFractionRing.injective V (FractionRing V)
  have hπne : π ≠ 0 := by
    rw [hπ, map_ne_zero]
    exact fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hπle : ‖π‖ ≤ 1 := (hV _).2 ⟨ϖ, rfl⟩
  have hπlt : ‖π‖ < 1 := by
    refine lt_of_le_of_ne hπle fun h1 => hϖ.not_isUnit ?_
    have hle : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv, ← hπ, h1, inv_one]
    obtain ⟨a, ha⟩ := (hV _).1 hle
    refine isUnit_iff_exists_inv.2 ⟨a, hinjV ?_⟩
    rw [map_mul, ha, map_one]
    exact mul_inv_cancel₀ fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hb0 : 0 < ‖π‖ := norm_pos_iff.2 hπne
  have hle : ∀ s t : ℝ, ‖π‖ ^ s ≤ ‖π‖ ^ t ↔ t ≤ s := fun s t =>
    Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hπlt
  have hinj : ∀ s t : ℝ, ‖π‖ ^ s = ‖π‖ ^ t → s = t := fun s t h =>
    le_antisymm ((hle t s).1 h.ge) ((hle s t).1 h.le)
  obtain ⟨s, hs⟩ := exists_rat_norm_eq_rpow hπne
  have hs0 : (s : ℝ) ≠ 0 := by
    intro h0
    rw [h0, Real.rpow_zero] at hs
    exact hπlt.ne hs
  obtain ⟨r, hexp⟩ : ∃ r : PadicAlgCl p → ℚ, ∀ x, x ≠ 0 → ‖x‖ = ‖π‖ ^ (r x : ℝ) := by
    refine ⟨fun x => if h : x = 0 then 0 else (exists_rat_norm_eq_rpow h).choose / s, ?_⟩
    intro x hx
    simp only [dif_neg hx]
    rw [hs, ← Real.rpow_mul (Nat.cast_nonneg _)]
    push_cast
    rw [mul_div_cancel₀ _ hs0]
    exact (exists_rat_norm_eq_rpow hx).choose_spec
  have hr_one : r 1 = 0 := by
    have h := hexp 1 one_ne_zero
    rw [norm_one, ← Real.rpow_zero ‖π‖] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_mul : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → r (x * y) = r x + r y := by
    intro x y hx hy
    have h := hexp (x * y) (mul_ne_zero hx hy)
    rw [norm_mul, hexp x hx, hexp y hy, ← Real.rpow_add hb0] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_add : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (r x) (r y) ≤ r (x + y) := by
    intro x y hx hy hxy
    have h := (PadicAlgCl.isNonarchimedean p) x y
    rw [hexp x hx, hexp y hy, hexp _ hxy] at h
    rcases le_total (r x) (r y) with hxy' | hxy'
    · rw [min_eq_left hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r x : ℝ) :=
        max_eq_left ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
    · rw [min_eq_right hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r y : ℝ) :=
        max_eq_right ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
  set w : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ) with hw
  have hw0 : w 0 = ⊤ := by simp [hw]
  have hw1 : w 1 = 0 := by simp [hw, hr_one]
  have hwadd : ∀ x y, min (w x) (w y) ≤ w (x + y) := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    by_cases hxy : x + y = 0
    · simp [hw, hxy]
    simp only [hw, if_neg hx, if_neg hy, if_neg hxy]
    rw [← WithTop.coe_min, WithTop.coe_le_coe]
    exact hr_add x y hx hy hxy
  have hwmul : ∀ x y, w (x * y) = w x + w y := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    simp only [hw, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [hr_mul x y hx hy, WithTop.coe_add]
  let v : AddValuation (PadicAlgCl p) (WithTop ℚ) := AddValuation.of w hw0 hw1 hwadd hwmul
  have hv : ∀ x, v x = w x := fun x => rfl
  have hunit : ∀ u : Vˣ,
      ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ = 1 := by
    intro u
    have h1 := (hV (algebraMap V (FractionRing V) u)).2 ⟨u, rfl⟩
    have h2 := (hV (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ *
        ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖
          = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) u)), norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)))]
  refine ⟨v, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver
    intro c n hc
    unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.HasVal at hc
    obtain ⟨u, rfl⟩ := hc
    have hne : algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u) ≠ 0 := by
      rw [map_mul, map_zpow₀]
      refine mul_ne_zero (zpow_ne_zero _ hπne) ?_
      intro h
      have := hunit u
      rw [h, norm_zero] at this
      exact zero_ne_one this
    rw [hv]
    simp only [hw, if_neg hne]
    have h2 : ‖algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u)‖ =
          ‖π‖ ^ (n : ℝ) := by
      rw [map_mul, map_zpow₀, norm_mul, norm_zpow, hunit u, _root_.mul_one, ← hπ,
        Real.rpow_intCast]
    have := hinj _ _ ((hexp _ hne).symm.trans h2)
    rw [WithTop.coe_eq_coe]
    exact_mod_cast this
  · unfold _root_.GlobalTheory.ZH.NormVal
    refine ⟨hb0, hπlt, fun x q => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [hv, hw0, norm_zero]
      constructor
      · intro h; exact absurd h WithTop.top_ne_coe
      · intro h; exact absurd h.symm (Real.rpow_pos_of_pos hb0 _).ne'
    rw [hv]
    simp only [hw, if_neg hx, WithTop.coe_eq_coe]
    rw [hexp x hx]
    constructor
    · rintro rfl; rfl
    · intro h; exact_mod_cast hinj _ _ h
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp [hv, hw0]
    rw [hv]
    simp only [hw, if_neg hx]
    rw [hexp x hx]
    have h1 := hle (r x : ℝ) 0
    rw [Real.rpow_zero] at h1
    refine ⟨?_, ?_⟩
    · rw [h1, WithTop.coe_nonneg]
      exact_mod_cast Iff.rfl
    · rw [WithTop.coe_eq_zero]
      constructor
      · rintro h; rw [h]; simp
      · intro h
        have := hinj (r x : ℝ) 0 (by rw [Real.rpow_zero]; exact h)
        exact_mod_cast this

end GlobalTheory.NormValuation
end
