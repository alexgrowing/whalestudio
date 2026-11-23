import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction

noncomputable section

namespace GlobalTheory.RowLev.GroupAlgPos

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

variable {Q : Type} [Group Q]

theorem coeff_mul_eq_sum [Fintype Q] (a b : MonoidAlgebra ℂ Q) (q : Q) :
    (a * b).coeff q = ∑ x, a.coeff x * b.coeff (x⁻¹ * q) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]

def adj [Finite Q] (a : MonoidAlgebra ℂ Q) : MonoidAlgebra ℂ Q :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun q => star (a.coeff q⁻¹))

theorem adj_coeff [Finite Q] (a : MonoidAlgebra ℂ Q) (q : Q) : (adj a).coeff q = star (a.coeff q⁻¹) := rfl

theorem adj_mul [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a * b) = adj b * adj a := by
  haveI := Fintype.ofFinite Q
  ext q
  rw [adj_coeff, coeff_mul_eq_sum, coeff_mul_eq_sum, star_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun x => ?_
  simp [adj_coeff, mul_comm, mul_assoc]

theorem adj_adj [Finite Q] (a : MonoidAlgebra ℂ Q) : adj (adj a) = a := by
  ext q; simp [adj_coeff]

theorem adj_sub [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a - b) = adj a - adj b := by
  ext q; simp [adj_coeff]

theorem isSA_iff [Finite Q] (a : MonoidAlgebra ℂ Q) : IsSA a ↔ adj a = a := by
  constructor
  · intro h
    ext q
    rw [adj_coeff, h q, star_star]
  · intro h q
    have := adj_coeff a q⁻¹
    rw [h, inv_inv] at this
    exact this

theorem coeff_mul_adj_one [Fintype Q] (a : MonoidAlgebra ℂ Q) :
    (a * adj a).coeff 1 = ∑ x, a.coeff x * star (a.coeff x) := by
  rw [coeff_mul_eq_sum]
  simp only [adj_coeff, mul_one, inv_inv]

theorem eq_zero_of_coeff_mul_adj [Finite Q] (a : MonoidAlgebra ℂ Q) (h : (a * adj a).coeff 1 = 0) : a = 0 := by
  haveI := Fintype.ofFinite Q
  rw [coeff_mul_adj_one] at h
  ext q
  have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_star_self_nonneg (a.coeff x)).1 h q (Finset.mem_univ _)
  simpa using this

theorem isSA_central [Finite Q] (z : MonoidAlgebra ℂ Q) (hz : z * z = z) (hc : ∀ a, z * a = a * z) : IsSA z := by
  have hs : adj z * adj z = adj z := by rw [← adj_mul, hz]
  have h0 : z - z * adj z = 0 := by
    apply eq_zero_of_coeff_mul_adj
    rw [adj_sub, adj_mul, adj_adj]
    have e1 : z * adj z * adj z = z * adj z := by rw [mul_assoc, hs]
    have e2 : z * (z * adj z) = z * adj z := by rw [← mul_assoc, hz]
    have e3 : z * adj z * (z * adj z) = z * adj z := by
      rw [mul_assoc, ← mul_assoc (adj z), ← hc (adj z), mul_assoc z (adj z), hs, e2]
    rw [sub_mul, mul_sub, mul_sub, e1, e2, e3]; simp
  have h1 : z = z * adj z := sub_eq_zero.1 h0
  rw [isSA_iff]
  conv_lhs => rw [h1, adj_mul, adj_adj]
  exact h1.symm

theorem coeff_inv_mul [Fintype Q] (a : MonoidAlgebra ℂ Q) (h : a * a = a) (hs : IsSA a) (x y : Q) :
    a.coeff (x⁻¹ * y) = ∑ q, star (a.coeff (q⁻¹ * x)) * a.coeff (q⁻¹ * y) := by
  conv_lhs => rw [← h, coeff_mul_eq_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun q => ?_
  simp [hs q, mul_assoc]

theorem posType [Finite Q] (a : MonoidAlgebra ℂ Q) (h : a * a = a) (hs : IsSA a) (m : ℕ) (x : Fin m → Q)
    (c : Fin m → ℂ) : 0 ≤ ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j) := by
  haveI := Fintype.ofFinite Q
  have e : ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j) =
      ∑ q : Q, star (∑ j, c j * a.coeff (q⁻¹ * x j)) * ∑ j, c j * a.coeff (q⁻¹ * x j) := by
    simp only [coeff_inv_mul a h hs (x _), star_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
    rw [star_mul']
    ring
  rw [e]
  exact Finset.sum_nonneg fun q _ => star_mul_self_nonneg _

theorem selfAdjoint_idempotent_posType : ∀ (Q : Type) [Group Q] [Finite Q],
    (∀ a : MonoidAlgebra ℂ Q, a * a = a → IsSA a →
      (∀ (m : ℕ) (x : Fin m → Q) (c : Fin m → ℂ), 0 ≤ ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j)) ∧
        0 ≤ a.coeff 1 ∧ (a.coeff 1 = 0 → a = 0)) ∧
    (∀ z : MonoidAlgebra ℂ Q, z * z = z → (∀ a, z * a = a * z) → IsSA z) ∧
    ∀ a b : MonoidAlgebra ℂ Q, IsSA a → IsSA b → a * b = b * a → IsSA (a * b) := by
  intro Q _ _
  haveI := Fintype.ofFinite Q
  refine ⟨fun a h hs => ?_, isSA_central, fun a b ha hb hab => ?_⟩
  · have e : a * adj a = a := by rw [(isSA_iff a).1 hs, h]
    refine ⟨posType a h hs, ?_, fun h0 => eq_zero_of_coeff_mul_adj a (by rw [e, h0])⟩
    rw [← e, coeff_mul_adj_one]
    exact Finset.sum_nonneg fun q _ => mul_star_self_nonneg _
  · rw [isSA_iff] at ha hb ⊢
    rw [adj_mul, ha, hb, hab]

end GlobalTheory.RowLev.GroupAlgPos
