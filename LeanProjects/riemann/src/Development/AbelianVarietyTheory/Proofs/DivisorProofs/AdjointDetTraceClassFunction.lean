import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdMatConjTranspose

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap Matrix
open Formalism.REAL (KG toMK)

namespace GlobalTheory.PsCo.PcEF.PhysicalMatrixDeterminant

variable {n : ℕ} {ε : Fin n → Bool}

def physM (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix {x : Fin n × Fin n // IsPhys ε x} {x : Fin n × Fin n // IsPhys ε x} ℂ :=
  fun x y => k x.1.1 y.1.1 * star (k x.1.2 y.1.2)

theorem physM_eq_adMat (k : Matrix (Fin n) (Fin n) ℂ) (x y : {x : Fin n × Fin n // IsPhys ε x}) :
    physM ε k x y = adMat ε k x.1 y.1 := by
  simp [physM, adMat, x.2, y.2]

theorem physM_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) :
    physM ε (a * b) = physM ε a * physM ε b := by
  ext x y
  rw [physM_eq_adMat, adMat_mul ha hb, Matrix.mul_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype (IsPhys ε)]
  have h0 : ∑ z : {z : Fin n × Fin n // ¬ IsPhys ε z}, adMat ε a x.1 z * adMat ε b z y.1 = 0 :=
    Finset.sum_eq_zero fun z _ => by simp [adMat, x.2, z.2]
  rw [h0, add_zero]
  simp only [physM_eq_adMat]

theorem physM_one : physM ε (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext x y
  rw [physM_eq_adMat, adMat_one]
  by_cases h : x = y
  · subst h; simp
  · have h' : x.1 ≠ y.1 := fun e => h (Subtype.ext e)
    simp [h, h']

theorem physDet_eq (k : Matrix (Fin n) (Fin n) ℂ) : physDet ε k = (1 - physM ε k).det := by
  unfold physDet
  congr 1

theorem physDet_conj (k k' : KG ε) : physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) := by
  have ha : toMK k'⁻¹ ∈ Kset ε := (k'⁻¹).2
  have hb : toMK k ∈ Kset ε := k.2
  have hc : toMK k' ∈ Kset ε := k'.2
  have hab : toMK k'⁻¹ * toMK k ∈ Kset ε := (k'⁻¹ * k).2
  have hac : physM ε (toMK k'⁻¹) * physM ε (toMK k') = 1 := by
    rw [← physM_mul ha hc, show toMK k'⁻¹ * toMK k' = toMK (k'⁻¹ * k') from rfl, inv_mul_cancel]
    exact physM_one
  rw [physDet_eq, physDet_eq, show toMK (k'⁻¹ * k * k') = toMK k'⁻¹ * toMK k * toMK k' from rfl,
    physM_mul hab hc, physM_mul ha hb]
  have e : 1 - physM ε (toMK k'⁻¹) * physM ε (toMK k) * physM ε (toMK k') =
      physM ε (toMK k'⁻¹) * (1 - physM ε (toMK k)) * physM ε (toMK k') := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hac]
  rw [e, det_mul, det_mul, mul_comm (det (physM ε (toMK k'⁻¹))), mul_assoc, ← det_mul, hac, det_one, mul_one]

theorem trK_conj {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (k k' : KG ε) :
    trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k) := by
  have hmul : ∀ a b : KG ε, (T (toMK (a * b)) : W →ₗ[ℂ] W) = (T (toMK a) : W →ₗ[ℂ] W) * (T (toMK b)) := by
    intro a b
    rw [show toMK (a * b) = toMK a * toMK b from rfl, hT.1.2 _ a.2 _ b.2]
    rfl
  have h1 : (T (toMK (1 : KG ε)) : W →ₗ[ℂ] W) = 1 := by
    rw [show toMK (1 : KG ε) = 1 from rfl, hT.1.1]
    rfl
  unfold trK
  rw [hmul, hmul, LinearMap.trace_mul_comm, ← mul_assoc, ← hmul k' k'⁻¹, mul_inv_cancel, h1, one_mul]

end GlobalTheory.PsCo.PcEF.PhysicalMatrixDeterminant

namespace GlobalTheory.PsCo.PcEF

theorem adjointDetTrace_classFunction : ClassFn := by
  intro n ε k k'
  refine ⟨PhysicalMatrixDeterminant.physDet_conj k k', ?_⟩
  intro W _ _ _ T hT
  exact PhysicalMatrixDeterminant.trK_conj T hT k k'

end GlobalTheory.PsCo.PcEF

end
end
