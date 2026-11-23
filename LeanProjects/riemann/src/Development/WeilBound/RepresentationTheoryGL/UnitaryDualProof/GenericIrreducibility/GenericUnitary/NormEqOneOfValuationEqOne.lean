import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.Exp.Rpow

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

theorem exists_unit_uniformizer : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact (show uniformizer k ≠ 0 by simp) hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

def ordHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord k x)
  map_one' := by simp [ord_eq_zero (k := k) (x := 1) (by simp)]
  map_mul' x y := by simp [ord_mul]

def nabsHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    kˣ →* ℝ where
  toFun := nabs k
  map_one' := nabs_eq_one k (by simp)
  map_mul' := nabs_mul' k

def normHom (χ : kˣ →* ℂˣ) : kˣ →* ℝ where
  toFun z := ‖(χ z : ℂ)‖
  map_one' := by simp
  map_mul' x y := by simp

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem mem_units_integer {u : kˣ} (hu : valuation k (u : k) = 1) :
    u ∈ (𝒪[k]).toSubmonoid.units := by
  refine ⟨?_, ?_⟩
  · show (u : k) ∈ 𝒪[k]
    exact (Valuation.mem_integer_iff _ _).2 hu.le
  · show ((u⁻¹ : kˣ) : k) ∈ 𝒪[k]
    rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem norm_eq_one_of_valuation_eq_one (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) {u : kˣ}
    (hu : valuation k (u : k) = 1) : ‖(χ u : ℂ)‖ = 1 := by
  have : T1Space k := IsTopologicalAddGroup.t1Space k (by
    convert (valuation k).isClosed_closedBall (R := k) 0 using 1
    ext x
    simp)
  set S : Submonoid k := (𝒪[k]).toSubmonoid
  have hS : IsCompact (S : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hG : IsCompact (S.units : Set kˣ) := Submonoid.units_isCompact hS
  have : CompactSpace S.units := isCompact_iff_compactSpace.mp hG
  set H : Subgroup S.units := χ.ker.comap S.units.subtype
  have hH : IsOpen (H : Set S.units) := hχ.preimage continuous_subtype_val
  have : Finite (S.units ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have hn : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmem : (⟨u, mem_units_integer hu⟩ : S.units) ^ H.index ∈ H := Subgroup.pow_index_mem H _
  have h1 : χ (u ^ H.index) = 1 := hmem
  have h2 : ‖(χ u : ℂ)‖ ^ H.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

theorem norm_eq_nabs_rpow (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    ∃ s : ℝ, ∀ z : kˣ, ‖(χ z : ℂ)‖ = nabs k z ^ s := by
  obtain ⟨ϖ, hϖ⟩ := exists_unit_uniformizer k
  set a := ‖(χ ϖ : ℂ)‖
  set b := nabs k ϖ
  have ha : 0 < a := norm_pos_iff.2 (χ ϖ).ne_zero
  have hb : 0 < b := nabs_pos' k ϖ
  have hb1 : b ≠ 1 := fun e => (uniformizer_lt_one (R := k)).ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have hlb : Real.log b ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hb hb1
  refine ⟨Real.log a / Real.log b, fun z => ?_⟩
  have hbt : b ^ (Real.log a / Real.log b) = a := by
    rw [Real.rpow_def_of_pos hb, mul_div_cancel₀ _ hlb, Real.exp_log ha]
  set m : ℤ := ord k z
  set u : kˣ := z * ϖ ^ (-m)
  have hord1 : ord k ϖ = 1 := ord_eq_one hϖ
  have hordu : ord k u = 0 := by
    have e1 : ordHom k u = ordHom k z * ordHom k ϖ ^ (-m) := by rw [map_mul, map_zpow]
    have e2 := congrArg Multiplicative.toAdd e1
    simp only [ordHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_mul, toAdd_zpow, toAdd_ofAdd, hord1] at e2
    rw [e2]
    simp [m]
  have hu : valuation k (u : k) = 1 := ord_eq_zero_iff.1 hordu
  have hz : z = u * ϖ ^ m := by
    simp only [u, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hnorm : ‖(χ z : ℂ)‖ = a ^ m := by
    have := congrArg (normHom χ) hz
    rw [map_mul, map_zpow] at this
    simpa [normHom, norm_eq_one_of_valuation_eq_one χ hχ hu, a] using this
  have hnabs : nabs k z = b ^ m := by
    have := congrArg (nabsHom k) hz
    rw [map_mul, map_zpow] at this
    simpa [nabsHom, nabs_eq_one k hu, b] using this
  rw [hnorm, hnabs, ← Real.rpow_intCast b m, ← Real.rpow_mul hb.le, mul_comm, Real.rpow_mul hb.le, hbt,
    Real.rpow_intCast]

end PositivityTheory.RgUd.Exp.Rpow
