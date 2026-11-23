import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.FiniteDVRValuation

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} in

theorem _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) {c : V}
    (hc : c ≠ 0) :
    ∃ n : ℕ, v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) =
        ((n : ℚ) : WithTop ℚ) ∧ (n = 0 → IsUnit c) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨n, ?_, fun hn => by subst hn; simp⟩
  rw [hv _ n ⟨u, by rw [zpow_natCast, map_mul, map_pow, mul_comm]⟩]
  norm_cast

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} in
theorem _root_.GlobalTheory.FiniteDVRValuation.val_nonneg (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) (c : V) :
    0 ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · subst hc
    simp
  · obtain ⟨n, hn, -⟩ := _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hc
    rw [hn]
    exact_mod_cast n.cast_nonneg

end

def nonnegSubring {F K : Type} [Field F] [Field K] (v : AddValuation F (WithTop ℚ)) (e : K →+* F) :
    ValuationSubring K where
  carrier := {x | 0 ≤ v (e x)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg, AddValuation.map_neg] at *
    exact ha
  mem_or_inv_mem' := by
    intro x
    simp only [Set.mem_setOf_eq]
    by_cases hx : x = 0
    · left; simp [hx]
    by_contra hcon
    push_neg at hcon
    have h1 : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx, map_one, AddValuation.map_one]
    have h2 : v (e x) + v (e x⁻¹) < 0 := by
      calc v (e x) + v (e x⁻¹) ≤ 0 + v (e x⁻¹) := by gcongr; exact hcon.1.le
        _ = v (e x⁻¹) := zero_add _
        _ < 0 := hcon.2
    exact h2.ne h1

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.FiniteDVRValuation.main :
    ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W']
      [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i →
      i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F]
      [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v →
      (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧
      (∃ i' : FractionRing W →+* FractionRing W',
        (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧
        ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 →
          ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧
      ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K,
        ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  intro W W' _ _ _ _ _ _ i hi hfin ϖ hϖ F _ _ v hv
  refine ⟨fun r => _root_.GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r, ?_,
    fun K _ e => ⟨_root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e, fun x => ⟨Iff.rfl, fun h => ?_⟩⟩⟩
  · have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp i) :=
      (IsFractionRing.injective W' (FractionRing W')).comp hi
    have hunit : ∀ x : W,
        v (algebraMap (FractionRing W') F (algebraMap W' _ (i x))) = 0 → IsUnit x := by
      intro x hx
      by_contra hxu
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' i hfin.to_isIntegral
        (IsLocalRing.maximalIdeal W')
      have hcomap : (IsLocalRing.maximalIdeal W').comap i = IsLocalRing.maximalIdeal W :=
        IsLocalRing.eq_maximalIdeal hmax
      have hmem : x ∈ (IsLocalRing.maximalIdeal W').comap i := by
        rw [hcomap]
        exact (IsLocalRing.mem_maximalIdeal x).2 hxu
      have hix : ¬IsUnit (i x) := (IsLocalRing.mem_maximalIdeal _).1 (Ideal.mem_comap.1 hmem)
      have hle := (_root_.ReciprocityTheory.ChartRestriction.G.DVR.TWO.v_of_V v hϖ hv (i x)).2 hix ((map_ne_zero_iff i hi).2 hx0)
      have hle' : (1 : WithTop ℚ) ≤ 0 := by
        rw [← hx]
        exact hle
      exact absurd hle' (by norm_num)
    refine ⟨IsFractionRing.lift hinj, fun r => IsFractionRing.lift_algebraMap hinj r,
      fun a ha => ?_⟩
    by_cases ha0 : a = 0
    · subst ha0
      simp at ha
    rcases ValuationRing.isInteger_or_isInteger W a with ⟨x, hx⟩ | ⟨x, hx⟩
    · subst hx
      rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply] at ha
      exact ⟨(hunit x ha).unit, rfl⟩
    · have hinv : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
        have hsum : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a)) +
            v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
          rw [← AddValuation.map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one,
            AddValuation.map_one]
        rwa [ha, zero_add] at hsum
      rw [← hx, IsFractionRing.lift_algebraMap, RingHom.comp_apply] at hinv
      refine ⟨(hunit x hinv).unit⁻¹, ?_⟩
      rw [← inv_inv a, ← hx, map_units_inv, IsUnit.unit_spec]
  · have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h
    have h1 : x ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e := (ValuationSubring.valuation_le_one_iff _ _).1 h.le
    have h2 : x⁻¹ ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e :=
      (ValuationSubring.valuation_le_one_iff _ _).1 (by rw [map_inv₀, h, inv_one])
    change 0 ≤ v (e x) at h1
    change 0 ≤ v (e x⁻¹) at h2
    have hsum : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, AddValuation.map_one]
    exact le_antisymm (le_add_of_nonneg_right h2 |>.trans_eq hsum) h1

end GlobalTheory.FiniteDVRValuation
