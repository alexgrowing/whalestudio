import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem psiGen_norm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat k r) :
    ‖Formalism.MainNotions.S.psiGen k r z c g‖ = 1 := by
  unfold Formalism.MainNotions.S.psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem ellA_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {m m' : Mat k r}
    (hm : m ∈ Nset k r) (hm' : m' ∈ Nset k r) (a : Fin r) :
    Formalism.MainNotions.S.ellA k r z (m * m') a = Formalism.MainNotions.S.ellA k r z m a + Formalism.MainNotions.S.ellA k r z m' a := by
  have hc := ((nset_iff m).1 hm).2
  have hc' := ((nset_iff m').1 hm').2
  have hi : (Formalism.QuantumDeterminants.eI k r a).val < r := a.isLt
  unfold Formalism.MainNotions.S.ellA
  split_ifs with h
  · exact mul_apply_add hc hc' _ _ hi
      (show (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩).val ≤ r + k by show a.val + 1 ≤ r + k; omega)
      (show (Formalism.QuantumDeterminants.eI k r a).val < (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩).val by
        show a.val < a.val + 1; omega)
      (Or.inl (show (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩).val ≤ (Formalism.QuantumDeterminants.eI k r a).val + 1 by
        show a.val + 1 ≤ a.val + 1; omega))
  · simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : r ≤ q.val ∧ q.val ≤ r + k
    · rw [mul_apply_add hc hc' _ _ hi hq.2
        (show (Formalism.QuantumDeterminants.eI k r a).val < q.val by show a.val < q.val; omega)
        (Or.inr (show r ≤ (Formalism.QuantumDeterminants.eI k r a).val + 1 by show r ≤ a.val + 1; omega)), add_mul]
    · have hz0 : z q = 0 := hz q (by omega)
      rw [hz0, mul_zero, mul_zero, mul_zero, add_zero]

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem ellA_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) (a : Fin r) :
    Formalism.MainNotions.S.ellA k r z (h * m * h⁻¹) a = Formalism.MainNotions.S.ellA k r z m a := by
  have hb := uw_block hh
  have hb' := uw_block (uw_inv hh)
  have hz' : h⁻¹ *ᵥ z = z := (uw_inv hh).2.2
  have hrow : ∀ p, h (Formalism.QuantumDeterminants.eI k r a) p = if Formalism.QuantumDeterminants.eI k r a = p then 1 else 0 :=
    fun p => hb.2 _ p (Or.inl (show (Formalism.QuantumDeterminants.eI k r a).val < r from a.isLt))
  unfold Formalism.MainNotions.S.ellA
  split_ifs with h1
  · have hcol : ∀ q, h⁻¹ q (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h1⟩) =
        if q = Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h1⟩ then 1 else 0 :=
      fun q => hb'.1 q _ (Or.inl (show (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h1⟩).val < r from h1))
    rw [mul_apply_of_col _ _ _ hcol, mul_apply_of_row _ _ _ hrow]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_apply_of_row _ _ hrow, hz']

theorem psiGen_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) {m m' : Mat k r}
    (hm : m ∈ Nset k r) (hm' : m' ∈ Nset k r) :
    Formalism.MainNotions.S.psiGen k r z c (m * m') = Formalism.MainNotions.S.psiGen k r z c m * Formalism.MainNotions.S.psiGen k r z c m' := by
  unfold Formalism.MainNotions.S.psiGen
  rw [← Complex.exp_add]
  have e : ∑ a, c a * Formalism.MainNotions.S.ellA k r z (m * m') a =
      (∑ a, c a * Formalism.MainNotions.S.ellA k r z m a) + ∑ a, c a * Formalism.MainNotions.S.ellA k r z m' a := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ellA_mul hz hm hm' a, mul_add]
  rw [e, Complex.add_re, Complex.ofReal_add, mul_add]

theorem psiGen_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) :
    Formalism.MainNotions.S.psiGen k r z c (h * m * h⁻¹) = Formalism.MainNotions.S.psiGen k r z c m := by
  unfold Formalism.MainNotions.S.psiGen
  have e : ∑ a, c a * Formalism.MainNotions.S.ellA k r z (h * m * h⁻¹) a = ∑ a, c a * Formalism.MainNotions.S.ellA k r z m a :=
    Finset.sum_congr rfl fun a _ => by rw [ellA_conj hz hh hm a]
  rw [e]

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
