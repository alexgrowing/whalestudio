import Mathlib
import GroundTheory.PAdicHodge.FieldOfNormsDef
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
  {L : IntermediateField K Ω} [IsGalois K L]
  [hsapf : Fact (IsStrictlyAPF K Ω L)] [hinf : Fact (¬ FiniteDimensional K L)]

namespace FieldOfNorms

variable (K Ω L) in

def apfData : APFData L := Classical.choice (IsStrictlyAPF.nonempty_apfData hsapf.out)

variable (K Ω L) in

def tower : NormTower K Ω (ringChar 𝓀[K]) := (apfData K Ω L).tower hinf.out

theorem isTowerFor : (tower K Ω L).IsTowerFor L := (apfData K Ω L).isTowerFor hinf.out

variable (K Ω L) in

def equivFam : FieldOfNorms K Ω L ≃ (tower K Ω L).Fam := isTowerFor.equiv _ _

instance instField : Field (FieldOfNorms K Ω L) := (equivFam K Ω L).field

theorem equivFam_mul (x y : FieldOfNorms K Ω L) :
    equivFam K Ω L (x * y) = equivFam K Ω L x * equivFam K Ω L y :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_add (x y : FieldOfNorms K Ω L) :
    equivFam K Ω L (x + y) = equivFam K Ω L x + equivFam K Ω L y :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_sub (x y : FieldOfNorms K Ω L) :
    equivFam K Ω L (x - y) = equivFam K Ω L x - equivFam K Ω L y :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_zero : equivFam K Ω L (0 : FieldOfNorms K Ω L) = 0 :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_one : equivFam K Ω L (1 : FieldOfNorms K Ω L) = 1 :=
  (equivFam K Ω L).apply_symm_apply _

theorem equivFam_natCast (n : ℕ) : equivFam K Ω L (n : FieldOfNorms K Ω L) = n :=
  (equivFam K Ω L).apply_symm_apply _

variable (K Ω L) in

def ringEquivFam : FieldOfNorms K Ω L ≃+* (tower K Ω L).Fam where
  __ := equivFam K Ω L
  map_mul' := equivFam_mul
  map_add' := equivFam_add

theorem equivFam_val (x : FieldOfNorms K Ω L) (n : ℕ) :
    (equivFam K Ω L x).1 n = x.1 (isTowerFor.finSub n) := rfl

theorem mul_val (x y : FieldOfNorms K Ω L) (E : FinSub K Ω L) : (x * y).1 E = x.1 E * y.1 E := by
  obtain ⟨n, hn⟩ := (isTowerFor (L := L)).exists_le E
  have hx : ∀ z : FieldOfNorms K Ω L, z.1 E = relNorm hn ((equivFam K Ω L z).1 n) := fun z ↦ by
    rw [equivFam_val]; exact (z.2.2 E _ hn).symm
  rw [hx, hx x, hx y, equivFam_mul, NormTower.Fam.mul_val]
  exact relNorm_mul hn ((equivFam K Ω L x).2 n).1 ((equivFam K Ω L y).2 n).1

instance charP : CharP (FieldOfNorms K Ω L) (ringChar 𝓀[K]) :=
  (CharP.charP_iff_prime_eq_zero (APFData.fact_prime (K := K)).out).mpr (by
    apply (equivFam K Ω L).injective
    rw [equivFam_natCast, equivFam_zero]
    exact NormTower.Fam.natCast_p)

def abv : AbsoluteValue (FieldOfNorms K Ω L) ℝ where
  toFun x := ‖equivFam K Ω L x‖
  map_mul' x y := by simp only [equivFam_mul, norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by
    rw [norm_eq_zero, ← equivFam_zero, (equivFam K Ω L).injective.eq_iff]
  add_le' x y := by simp only [equivFam_add]; exact norm_add_le _ _

instance instNormedField : NormedField (FieldOfNorms K Ω L) := (abv (K := K) (Ω := Ω) (L := L)).toNormedField

theorem norm_def (x : FieldOfNorms K Ω L) : ‖x‖ = ‖equivFam K Ω L x‖ := rfl

variable (K Ω L) in

def isometryEquivFam : FieldOfNorms K Ω L ≃ᵢ (tower K Ω L).Fam where
  __ := equivFam K Ω L
  isometry_toFun := Isometry.of_dist_eq fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm, norm_def, equivFam_sub]
    rfl

instance instIsUltrametricDist : IsUltrametricDist (FieldOfNorms K Ω L) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simp only [norm_def, equivFam_add]
    exact IsUltrametricDist.norm_add_le_max _ _

instance instNontriviallyNormedField : NontriviallyNormedField (FieldOfNorms K Ω L) where
  non_trivial := by
    obtain ⟨z, hz⟩ := NontriviallyNormedField.non_trivial (α := (tower K Ω L).Fam)
    exact ⟨(equivFam K Ω L).symm z, by rw [norm_def, Equiv.apply_symm_apply]; exact hz⟩

instance instLocallyCompactSpace : LocallyCompactSpace (FieldOfNorms K Ω L) :=
  ((isometryEquivFam K Ω L).toHomeomorph.locallyCompactSpace_iff).mpr inferInstance

instance instValuativeRel : ValuativeRel (FieldOfNorms K Ω L) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := FieldOfNorms K Ω L))

theorem vle_iff_norm_le (x y : FieldOfNorms K Ω L) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  exact NNReal.coe_le_coe

instance instCompatible : (NormedField.valuation (K := FieldOfNorms K Ω L)).Compatible :=
  Valuation.Compatible.ofValuation _

instance instIsValuativeTopology : IsValuativeTopology (FieldOfNorms K Ω L) := by
  let : Valued (FieldOfNorms K Ω L) NNReal := NormedField.toValued
  have : (Valued.v : Valuation (FieldOfNorms K Ω L) NNReal).Compatible := instCompatible
  exact GroundTheory.LocalField.isValuativeTopology_of_valued

instance instIsNontrivial : IsNontrivial (FieldOfNorms K Ω L) := by
  obtain ⟨z, hz⟩ := NontriviallyNormedField.non_trivial (α := FieldOfNorms K Ω L)
  refine ⟨⟨valuation _ z, ?_, ?_⟩⟩
  · rw [ne_eq, Valuation.zero_iff, ← norm_eq_zero]
    linarith
  · intro h
    have h2 : z ≤ᵥ (1 : FieldOfNorms K Ω L) := by
      rw [Valuation.vle_iff_le (valuation _), h, map_one]
    rw [vle_iff_norm_le, norm_one] at h2
    linarith

instance instIsNonarchimedeanLocalField : IsNonarchimedeanLocalField (FieldOfNorms K Ω L) where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial := inferInstance

end FieldOfNorms

section Limit

variable {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  {Ω' : Type*} [Field Ω'] [ValuativeRel Ω'] [TopologicalSpace Ω'] [IsValuativeTopology Ω']
  [Algebra K' Ω'] [ValuativeExtension K' Ω'] [Algebra.IsAlgebraic K' Ω']

variable {p : ℕ} {t : NormTower K' Ω' p}

end Limit

namespace FieldOfNorms

end FieldOfNorms

end GroundTheory.PAdicHodge
