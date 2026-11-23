import Mathlib
import GroundTheory.PAdicHodge.BCrisTensorK
import GroundTheory.PAdicHodge.BCrisNewtonFrac
import GroundTheory.PAdicHodge.CyclotomicTower
set_option maxSynthPendingDepth 1

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

local notation "K₀" => maxUnramified p K

theorem gal_smul_algebraMap_maxUnramified (σ : Gal(PadicAlgCl p/K)) (k : K₀) :
    σ • algebraMap K₀ (BCrisPlus ℂ_[p] p) k = algebraMap K₀ (BCrisPlus ℂ_[p] p) k := by
  apply iotaPlus_injective (K := ℂ_[p]) (p := p)
  rw [iotaPlus_gal_smul, iotaPlus_algebraMap_maxUnramified, gal_smul_algClToBdR]
  congr 1
  exact σ.commutes ⟨(k : PadicAlgCl p), (mem_maxUnramified.1 k.2).1⟩

theorem algebraMap_maxUnramified_padic (q : ℚ_[p]) :
    algebraMap K₀ (BCrisPlus ℂ_[p] p) (algebraMap ℚ_[p] K₀ q) =
      algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q := by
  apply iotaPlus_injective (K := ℂ_[p]) (p := p)
  rw [iotaPlus_algebraMap_maxUnramified, iotaPlus_algebraMap_padic, IntermediateField.coe_algebraMap_apply,
    AlgHom.commutes]

theorem algebraMap_maxUnramified_injective :
    Function.Injective (algebraMap K₀ (BCrisPlus ℂ_[p] p)) := by
  intro a b h
  have h' := congrArg (iotaPlus ℂ_[p] p) h
  rw [iotaPlus_algebraMap_maxUnramified, iotaPlus_algebraMap_maxUnramified] at h'
  exact Subtype.ext ((algClToBdR p).injective h')

section Frob

variable [FiniteDimensional ℚ_[p] K]

instance finiteDimensional_padic_maxUnramified : FiniteDimensional ℚ_[p] K₀ :=
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : maxUnramified p K ≤ K)).toLinearMap
    (IntermediateField.inclusion (inf_le_left : maxUnramified p K ≤ K)).injective

theorem exists_phiPlus_algebraMap_maxUnramified (k : K₀) :
    ∃ k' : K₀, phiPlus ℂ_[p] p (algebraMap K₀ (BCrisPlus ℂ_[p] p) k) =
      algebraMap K₀ (BCrisPlus ℂ_[p] p) k' := by
  obtain ⟨k₁, hk₁, h⟩ := bCrisPlus_fixed (K := K) (phiPlus ℂ_[p] p (algebraMap K₀ _ k)) fun σ => by
    rw [← phiPlus_gal_smul, gal_smul_algebraMap_maxUnramified]
  refine ⟨⟨k₁, hk₁⟩, iotaPlus_injective (K := ℂ_[p]) (p := p) ?_⟩
  rw [h, iotaPlus_algebraMap_maxUnramified]

def maxUnramifiedFrobeniusFun (k : K₀) : K₀ := (exists_phiPlus_algebraMap_maxUnramified K k).choose

theorem phiPlus_algebraMap_maxUnramifiedFrobeniusFun (k : K₀) :
    phiPlus ℂ_[p] p (algebraMap K₀ (BCrisPlus ℂ_[p] p) k) =
      algebraMap K₀ (BCrisPlus ℂ_[p] p) (maxUnramifiedFrobeniusFun K k) :=
  (exists_phiPlus_algebraMap_maxUnramified K k).choose_spec

def maxUnramifiedFrobeniusHom : K₀ →ₐ[ℚ_[p]] K₀ where
  toFun := maxUnramifiedFrobeniusFun K
  map_one' := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun]; simp only [map_one])
  map_mul' a b := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun, map_mul, map_mul, map_mul, phiPlus_algebraMap_maxUnramifiedFrobeniusFun,
      phiPlus_algebraMap_maxUnramifiedFrobeniusFun])
  map_zero' := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun]; simp only [map_zero])
  map_add' a b := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun, map_add, map_add, map_add, phiPlus_algebraMap_maxUnramifiedFrobeniusFun,
      phiPlus_algebraMap_maxUnramifiedFrobeniusFun])
  commutes' q := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun, algebraMap_maxUnramified_padic, phiPlus_algebraMap_padic])

def maxUnramifiedFrobenius : K₀ ≃ₐ[ℚ_[p]] K₀ :=
  AlgEquiv.ofBijective (maxUnramifiedFrobeniusHom K) (maxUnramifiedFrobeniusHom K).bijective

theorem phiPlus_algebraMap_maxUnramified (k : K₀) :
    phiPlus ℂ_[p] p (algebraMap K₀ (BCrisPlus ℂ_[p] p) k) =
      algebraMap K₀ (BCrisPlus ℂ_[p] p) (maxUnramifiedFrobenius K k) :=
  phiPlus_algebraMap_maxUnramifiedFrobeniusFun K k

theorem phiB_algebraMap_maxUnramified {ε : PreTilt (normInteger ℂ_[p]) p}
    (hε : PreTilt.untilt ε = 1) (k : K₀) :
    phiB hε (algebraMap K₀ (BCris hε) k) = algebraMap K₀ (BCris hε) (maxUnramifiedFrobenius K k) :=
  calc phiB hε (algebraMap K₀ (BCris hε) k)
      = phiB hε (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap K₀ (BCrisPlus ℂ_[p] p) k)) :=
        congrArg _ (IsScalarTower.algebraMap_apply K₀ (BCrisPlus ℂ_[p] p) (BCris hε) k)
    _ = algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)
          (phiPlus ℂ_[p] p (algebraMap K₀ (BCrisPlus ℂ_[p] p) k)) :=
        phiB_algebraMap hε _
    _ = algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap K₀ (BCrisPlus ℂ_[p] p) (maxUnramifiedFrobenius K k)) :=
        congrArg _ (phiPlus_algebraMap_maxUnramified K k)
    _ = algebraMap K₀ (BCris hε) (maxUnramifiedFrobenius K k) :=
        (IsScalarTower.algebraMap_apply K₀ (BCrisPlus ℂ_[p] p) (BCris hε) (maxUnramifiedFrobenius K k)).symm

end Frob

section Valuation

variable {K}

theorem exists_norm_eq_zpow_maxUnramified {x : K₀} (hx : x ≠ 0) :
    ∃ D : ℤ, ‖(x : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ D :=
  (isACrisFraction_of_mem (mem_maxUnramified.1 x.2).2).exists_norm_eq_zpow
    (by simpa using hx)

theorem norm_p_algCl_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)

theorem zpow_norm_p_injective : Function.Injective fun D : ℤ => ‖(p : PadicAlgCl p)‖ ^ D :=
  zpow_right_injective₀ norm_p_algCl_pos (norm_p_algCl_lt_one (p := p)).ne

open Classical in

def maxUnramifiedValFun (x : K₀) : WithTop ℤ :=
  if hx : x = 0 then ⊤ else ((exists_norm_eq_zpow_maxUnramified hx).choose : ℤ)

theorem maxUnramifiedValFun_zero : maxUnramifiedValFun (0 : K₀) = ⊤ := by
  classical
  rw [maxUnramifiedValFun, dif_pos rfl]

theorem maxUnramifiedValFun_eq {x : K₀} (hx : x ≠ 0) {D : ℤ} (h : ‖(x : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ D) :
    maxUnramifiedValFun x = D := by
  classical
  rw [maxUnramifiedValFun, dif_neg hx]
  congr 1
  exact zpow_norm_p_injective ((exists_norm_eq_zpow_maxUnramified hx).choose_spec.symm.trans h)

theorem maxUnramifiedValFun_add_le (x y : K₀) : min (maxUnramifiedValFun x) (maxUnramifiedValFun y) ≤ maxUnramifiedValFun (x + y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add, maxUnramifiedValFun_zero]; exact min_le_right _ _
  by_cases hy : y = 0
  · rw [hy, add_zero, maxUnramifiedValFun_zero]; exact min_le_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, maxUnramifiedValFun_zero]; exact le_top
  obtain ⟨D, hD⟩ := exists_norm_eq_zpow_maxUnramified hx
  obtain ⟨E, hE⟩ := exists_norm_eq_zpow_maxUnramified hy
  obtain ⟨F, hF⟩ := exists_norm_eq_zpow_maxUnramified hxy
  rw [maxUnramifiedValFun_eq hx hD, maxUnramifiedValFun_eq hy hE, maxUnramifiedValFun_eq hxy hF, ← WithTop.coe_min, WithTop.coe_le_coe]
  have h := IsUltrametricDist.norm_add_le_max (x : PadicAlgCl p) (y : PadicAlgCl p)
  rw [← IntermediateField.coe_add, hF, hD, hE] at h
  have hp0 := norm_p_algCl_pos (p := p)
  have hp1 := norm_p_algCl_lt_one (p := p)
  rcases le_total D E with hDE | hDE
  · rw [min_eq_left hDE]
    rw [max_eq_left ((zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).2 hDE)] at h
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).1 h
  · rw [min_eq_right hDE]
    rw [max_eq_right ((zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).2 hDE)] at h
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).1 h

theorem maxUnramifiedValFun_mul (x y : K₀) : maxUnramifiedValFun (x * y) = maxUnramifiedValFun x + maxUnramifiedValFun y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, maxUnramifiedValFun_zero, WithTop.top_add]
  by_cases hy : y = 0
  · rw [hy, mul_zero, maxUnramifiedValFun_zero, WithTop.add_top]
  obtain ⟨D, hD⟩ := exists_norm_eq_zpow_maxUnramified hx
  obtain ⟨E, hE⟩ := exists_norm_eq_zpow_maxUnramified hy
  rw [maxUnramifiedValFun_eq hx hD, maxUnramifiedValFun_eq hy hE, maxUnramifiedValFun_eq (mul_ne_zero hx hy) (D := D + E), ← WithTop.coe_add]
  rw [IntermediateField.coe_mul, norm_mul, hD, hE, zpow_add₀ norm_p_algCl_pos.ne']

theorem maxUnramifiedValFun_one : maxUnramifiedValFun (1 : K₀) = 0 :=
  maxUnramifiedValFun_eq (one_ne_zero : (1 : K₀) ≠ 0) (D := 0) (by simp)

variable (K) in

def maxUnramifiedValuation : AddValuation K₀ (WithTop ℤ) :=
  AddValuation.of maxUnramifiedValFun maxUnramifiedValFun_zero maxUnramifiedValFun_one maxUnramifiedValFun_add_le maxUnramifiedValFun_mul

theorem maxUnramifiedValuation_apply (x : K₀) : maxUnramifiedValuation K x = maxUnramifiedValFun x := rfl

theorem maxUnramifiedValuation_eq_coe_iff {x : K₀} (hx : x ≠ 0) {D : ℤ} :
    maxUnramifiedValuation K x = D ↔ ‖(x : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ D := by
  refine ⟨fun h => ?_, maxUnramifiedValFun_eq hx⟩
  obtain ⟨E, hE⟩ := exists_norm_eq_zpow_maxUnramified hx
  rw [maxUnramifiedValuation_apply, maxUnramifiedValFun_eq hx hE, WithTop.coe_eq_coe] at h
  rw [hE, h]

theorem maxUnramifiedValuation_ne_top {x : K₀} (hx : x ≠ 0) : maxUnramifiedValuation K x ≠ ⊤ := by
  obtain ⟨E, hE⟩ := exists_norm_eq_zpow_maxUnramified hx
  rw [maxUnramifiedValuation_apply, maxUnramifiedValFun_eq hx hE]
  exact WithTop.coe_ne_top

theorem maxUnramifiedValuation_natCast_p : maxUnramifiedValuation K (p : K₀) = 1 := by
  have hp0 : (p : K₀) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  rw [show (1 : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) from rfl, maxUnramifiedValuation_eq_coe_iff hp0, zpow_one]
  simp

end Valuation

section FrobValuation

variable [FiniteDimensional ℚ_[p] K]

theorem norm_maxUnramifiedFrobenius (x : K₀) : ‖((maxUnramifiedFrobenius K x : K₀) : PadicAlgCl p)‖ = ‖(x : PadicAlgCl p)‖ := by
  have hm : minpoly ℚ_[p] ((maxUnramifiedFrobenius K x : K₀) : PadicAlgCl p) = minpoly ℚ_[p] (x : PadicAlgCl p) := by
    rw [← IntermediateField.minpoly_eq, ← IntermediateField.minpoly_eq, minpoly.algEquiv_eq]
  have h1 := norm_pow_natDegree_minpoly ((maxUnramifiedFrobenius K x : K₀) : PadicAlgCl p)
  have h2 := norm_pow_natDegree_minpoly (x : PadicAlgCl p)
  rw [hm] at h1
  have hd : (minpoly ℚ_[p] (x : PadicAlgCl p)).natDegree ≠ 0 :=
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (x : PadicAlgCl p))).ne'
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd).1 (h1.trans h2.symm)

theorem maxUnramifiedValuation_frobenius (x : K₀) : maxUnramifiedValuation K (maxUnramifiedFrobenius K x) = maxUnramifiedValuation K x := by
  by_cases hx : x = 0
  · rw [hx, map_zero]
  obtain ⟨D, hD⟩ := exists_norm_eq_zpow_maxUnramified hx
  have hσx : maxUnramifiedFrobenius K x ≠ 0 := (map_ne_zero_iff _ (maxUnramifiedFrobenius K).injective).2 hx
  rw [(maxUnramifiedValuation_eq_coe_iff hx).2 hD, maxUnramifiedValuation_eq_coe_iff hσx, norm_maxUnramifiedFrobenius, hD]

end FrobValuation

end ACris

end GroundTheory.PAdicHodge
