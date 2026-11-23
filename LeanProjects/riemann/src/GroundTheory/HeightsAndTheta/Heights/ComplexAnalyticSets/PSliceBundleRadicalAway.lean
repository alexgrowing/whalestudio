import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBundleRadicalAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SliceBundleRadicalAway

variable {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) (k : Fin n)

abbrev Base := Localization.Away (Ideal.Quotient.mk J (X k - C (q k)))

def toBase : MvPolynomial (Fin n) ℂ →+* Base J q k :=
  (algebraMap _ (Base J q k)).comp (Ideal.Quotient.mk J)

def rowForm (i : Fin d) : MvPolynomial (Fin d × Fin n) (Base J q k) :=
  ∑ j, X (i, j) * C (toBase J q k (X j - C (q j)))

def coeffMap : MvPolynomial (Fin d × Fin n) ℂ →+* MvPolynomial (Fin d × Fin n) (Base J q k) :=
  eval₂Hom (C.comp ((toBase J q k).comp C)) fun ij =>
    X ij - if ij.2 = k then
      C (IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k)))) * rowForm J d q k ij.1
    else 0

def solveMap :
    MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) →+* MvPolynomial (Fin d × Fin n) (Base J q k) :=
  eval₂Hom (coeffMap J d q k) fun j => C (toBase J q k (X j))

abbrev Quo := MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) ⧸ universalSliceIdeal J d q

instance instCommRingQuo : CommRing (Quo J d q) := Ideal.Quotient.commRing _

def uQuo : Quo J d q :=
  algebraMap (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) (Quo J d q) (X k - C (C (q k)))

abbrev Tot := Localization.Away (uQuo J d q k)

def toTot : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) →+* Tot J d q k :=
  algebraMap _ _

theorem toTot_apply (x : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) :
    toTot J d q k x = algebraMap (Quo J d q) (Tot J d q k)
      (algebraMap (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) (Quo J d q) x) :=
  IsScalarTower.algebraMap_apply _ _ _ x

theorem toTot_eq_zero {x : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)}
    (hx : x ∈ universalSliceIdeal J d q) : toTot J d q k x = 0 := by
  rw [toTot_apply, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

def quotToTot : (MvPolynomial (Fin n) ℂ ⧸ J) →+* Tot J d q k :=
  Ideal.Quotient.lift J ((toTot J d q k).comp (MvPolynomial.map C)) fun a ha =>
    toTot_eq_zero J d q k (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

theorem quotToTot_isUnit : IsUnit (quotToTot J d q k (Ideal.Quotient.mk J (X k - C (q k)))) := by
  have e : MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ) (X k - C (q k)) =
      X k - C (C (q k)) := by simp
  rw [quotToTot, Ideal.Quotient.lift_mk, RingHom.comp_apply, e, toTot_apply]
  exact IsLocalization.Away.algebraMap_isUnit (S := Tot J d q k) (uQuo J d q k)

def baseToTot : Base J q k →+* Tot J d q k :=
  IsLocalization.Away.lift (R := MvPolynomial (Fin n) ℂ ⧸ J) (S := Base J q k) (P := Tot J d q k)
    (Ideal.Quotient.mk J (X k - C (q k))) (g := quotToTot J d q k) (quotToTot_isUnit J d q k)

theorem baseToTot_toBase (a : MvPolynomial (Fin n) ℂ) :
    baseToTot J d q k (toBase J q k a) = toTot J d q k (MvPolynomial.map C a) := by
  simp [baseToTot, toBase, quotToTot]

def backMap : MvPolynomial (Fin d × Fin n) (Base J q k) →+* Tot J d q k :=
  eval₂Hom (baseToTot J d q k) fun ij => toTot J d q k (C (X ij))

theorem backMap_rowForm (i : Fin d) : backMap J d q k (rowForm J d q k i) = 0 := by
  simp only [rowForm, map_sum, map_mul, backMap, eval₂Hom_X', eval₂Hom_C, baseToTot_toBase]
  rw [← toTot_eq_zero J d q k (x := ∑ j, C (X (i, j)) * (X j - C (C (q j))))
    (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))]
  simp [map_sum, map_mul, map_sub]

theorem backMap_comp_solveMap : (backMap J d q k).comp (solveMap J d q k) = toTot J d q k := by
  have hc : (backMap J d q k).comp (coeffMap J d q k) = (toTot J d q k).comp C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coeffMap, backMap, baseToTot_toBase]
    · intro ij
      simp only [RingHom.comp_apply, coeffMap, eval₂Hom_X', map_sub]
      split_ifs
      · rw [map_mul, backMap_rowForm, mul_zero, sub_zero]
        simp [backMap]
      · simp [backMap]
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa [solveMap] using RingHom.congr_fun hc a
  · intro j
    simp [solveMap, backMap, baseToTot_toBase]

theorem coeffMap_comp_mapC :
    (solveMap J d q k).comp (MvPolynomial.map C) = C.comp (toBase J q k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [solveMap, coeffMap]
  · intro j
    simp [solveMap]

theorem solveMap_gen (i : Fin d) :
    solveMap J d q k (∑ j, C (X (i, j)) * (X j - C (C (q j)))) = 0 := by
  have h : ∀ j, solveMap J d q k (C (X (i, j)) * (X j - C (C (q j)))) =
      (X (i, j) - if j = k then
        C (IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k)))) * rowForm J d q k i
      else 0) * C (toBase J q k (X j - C (q j))) := by
    intro j
    have := RingHom.congr_fun (coeffMap_comp_mapC J d q k) (X j - C (q j))
    have e : MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ) (X j - C (q j)) =
        X j - C (C (q j)) := by simp
    rw [RingHom.comp_apply, RingHom.comp_apply, e] at this
    rw [map_mul, this]
    congr 1
    rw [solveMap, eval₂Hom_C, coeffMap, eval₂Hom_X']
  rw [map_sum, Finset.sum_congr rfl fun j _ => h j]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [← rowForm, mul_assoc, mul_comm (rowForm J d q k i), ← mul_assoc, ← map_mul]
  have hu : IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k))) *
      toBase J q k (X k - C (q k)) = (1 : Base J q k) := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf (S := Base J q k) (Ideal.Quotient.mk J (X k - C (q k)))
  rw [hu, map_one, one_mul, sub_self]

theorem le_ker_solveMap : universalSliceIdeal J d q ≤ RingHom.ker (solveMap J d q k) := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, coeffMap_comp_mapC]
    simp [toBase, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact solveMap_gen J d q k i

end SliceBundleRadicalAway

theorem SliceBundleRadicalAway.proof : SliceBundleRadicalAway.Statement := by
  intro n d J q hJ k f hf
  have : IsReduced (MvPolynomial (Fin n) ℂ ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).1 hJ
  obtain ⟨m, hm⟩ := hf
  have h0 : SliceBundleRadicalAway.solveMap J d q k f = 0 := by
    apply IsNilpotent.eq_zero
    exact ⟨m, by rw [← map_pow]; exact SliceBundleRadicalAway.le_ker_solveMap J d q k hm⟩
  have h1 : SliceBundleRadicalAway.toTot J d q k f = 0 := by
    rw [← SliceBundleRadicalAway.backMap_comp_solveMap J d q k, RingHom.comp_apply, h0, map_zero]
  rw [SliceBundleRadicalAway.toTot_apply] at h1
  obtain ⟨⟨_, e, rfl⟩, he⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (SliceBundleRadicalAway.uQuo J d q k)) (SliceBundleRadicalAway.Tot J d q k) _).1 h1
  refine ⟨e, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, map_mul, map_pow]
  exact he

end

end GroundTheory.Heights₂.Heights
