import Mathlib

noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsGA

variable {G : Type} [Group G] [Fintype G]

theorem coeff_mul_fin (a b : MonoidAlgebra ℂ G) (g : G) :
    (a * b).coeff g = ∑ h : G, a.coeff h * b.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]

theorem central_of_class (a : MonoidAlgebra ℂ G) (h : ∀ g P : G, a.coeff (P⁻¹ * g * P) = a.coeff g)
    (y : MonoidAlgebra ℂ G) : a * y = y * a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [coeff_mul_fin, coeff_mul_fin]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight g)) _ _ fun k => ?_
  have e1 : (k⁻¹ * g)⁻¹ * g = g⁻¹ * k * g := by group
  show a.coeff k * y.coeff (k⁻¹ * g) = y.coeff (k⁻¹ * g) * a.coeff ((k⁻¹ * g)⁻¹ * g)
  rw [e1, h k g]
  exact mul_comm _ _

def conjA (a : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g => star (a.coeff g⁻¹))

theorem conjA_coeff (a : MonoidAlgebra ℂ G) (g : G) : (conjA a).coeff g = star (a.coeff g⁻¹) := by
  simp [conjA, MonoidAlgebra.coeff_ofCoeff]

theorem conjA_conjA (a : MonoidAlgebra ℂ G) : conjA (conjA a) = a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [conjA_coeff, conjA_coeff, inv_inv, star_star]

theorem conjA_mul (a b : MonoidAlgebra ℂ G) : conjA (a * b) = conjA b * conjA a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [conjA_coeff, coeff_mul_fin, coeff_mul_fin, star_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  have e1 : ((g * h)⁻¹ * g)⁻¹ = h := by group
  have e2 : (g * h)⁻¹ = h⁻¹ * g⁻¹ := mul_inv_rev g h
  show star (a.coeff h * b.coeff (h⁻¹ * g⁻¹)) =
    (conjA b).coeff (g * h) * (conjA a).coeff ((g * h)⁻¹ * g)
  rw [conjA_coeff, conjA_coeff, e1, e2, star_mul']
  exact mul_comm _ _

theorem conjA_sub (a b : MonoidAlgebra ℂ G) : conjA (a - b) = conjA a - conjA b := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  simp [conjA_coeff, MonoidAlgebra.coeff_sub, star_sub]

private theorem eq_zero_of_conjA_mul_self_eq_zero (x : MonoidAlgebra ℂ G) (hx : conjA x * x = 0) :
    x = 0 := by
  have h1 := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff 1) hx
  simp only [coeff_mul_fin, conjA_coeff, mul_one, MonoidAlgebra.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply] at h1
  have h2 : ∑ h : G, ((Complex.normSq (x.coeff h⁻¹) : ℝ) : ℂ) = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h2
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun h _ => Complex.normSq_nonneg (x.coeff h⁻¹))).mp h2
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  have h4 := h3 g⁻¹ (Finset.mem_univ _)
  rw [inv_inv, Complex.normSq_eq_zero] at h4
  simpa using h4

private theorem eq_mul_of_commuting_idempotents_conjA_swap (e f : MonoidAlgebra ℂ G) (hef : conjA e = f)
    (hfe : conjA f = e) (he : e * e = e) (hf : f * f = f) (hc : f * e = e * f) :
    e = e * f := by
  have hx : conjA (e - e * f) * (e - e * f) = 0 := by
    rw [conjA_sub, conjA_mul, hef, hfe]
    have h1 : f * (e * f) = e * f := by rw [← mul_assoc, hc, mul_assoc, hf]
    have h2 : e * f * e = e * f := by rw [mul_assoc, hc, ← mul_assoc, he]
    have h3 : e * f * (e * f) = e * f := by rw [← mul_assoc, h2, mul_assoc, hf]
    rw [sub_mul, mul_sub, mul_sub, h1, h3, h2, hc]
    simp
  exact sub_eq_zero.mp (eq_zero_of_conjA_mul_self_eq_zero _ hx)

theorem selfadj_of_central_idem (e : MonoidAlgebra ℂ G) (hid : e * e = e) (hc : ∀ y, e * y = y * e) :
    conjA e = e := by
  have hff : conjA e * conjA e = conjA e := by rw [← conjA_mul, hid]
  have h1 := eq_mul_of_commuting_idempotents_conjA_swap e (conjA e) rfl (conjA_conjA e) hid hff
    (hc (conjA e)).symm
  have h2 := eq_mul_of_commuting_idempotents_conjA_swap (conjA e) e (conjA_conjA e) rfl hff hid
    (hc (conjA e))
  calc conjA e = conjA e * e := h2
    _ = e * conjA e := (hc _).symm
    _ = e := h1.symm

end Formalism.L2.SG.Pf.AllRowsGA
