import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass

open Matrix MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.TopClass

open PositivityTheory.RgTw

variable {n : ℕ}

def secExpr {R : Type*} [Ring R] (A B C E Z : R) : R :=
  -((Z * A + A * Z) * B + A * (Z * B + B * Z)) - ((Z * E + E * Z) * C + E * (Z * C + C * Z))

def secDer (d : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun Z := secExpr d dᴴ d⁻¹ dᴴ⁻¹ Z
  map_add' X Y := by simp only [secExpr, add_mul, mul_add]; abel
  map_smul' c X := by
    simp only [secExpr, RingHom.id_apply, smul_sub, smul_neg, smul_add, Matrix.smul_mul, Matrix.mul_smul, add_mul,
      mul_add]

theorem trace_single_mul_single (a b c e : Fin n) :
    trace (Matrix.single a b (1 : ℂ) * Matrix.single c e 1) = if a = e ∧ b = c then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  by_cases h1 : a = e <;> by_cases h2 : b = c <;> simp [h1, h2, ite_and, Finset.sum_ite_eq', eq_comm]

theorem sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem trace_hb_mul_hb (p q : Fin n × Fin n) : trace (hb p * hb q) = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, e⟩ := q
  have hs := sqrt_two_inv_sq
  simp only [hb]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 <;>
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      trace_add, trace_sub, trace_smul, trace_single_mul_single, smul_eq_mul, Prod.mk.injEq] at * <;> (simp only [Fin.ext_iff, Fin.lt_iff_val_lt_val] at * ; split_ifs at * <;> (try omega)) <;>
  (generalize ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = s at hs ⊢
   have hs2 : s ^ 2 = 1 / 2 := by rw [sq]; exact hs
   first | ring1 | (ring_nf; simp only [Complex.I_sq, hs2]; ring_nf))

theorem hb_linInd : LinearIndependent ℂ (hb (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h := congrArg (fun X => trace (X * hb q)) hg
  simpa [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, trace_smul, trace_hb_mul_hb] using h

def hbB (n : ℕ) : Module.Basis (Fin n × Fin n) ℂ (Mat n) :=
  basisOfLinearIndependentOfCardEqFinrank' hb hb_linInd (by simp [Module.finrank_matrix])

theorem hbB_apply (p : Fin n × Fin n) : hbB n p = hb p := by
  simp [hbB]

theorem hbB_repr (X : Mat n) (q : Fin n × Fin n) : (hbB n).repr X q = trace (X * hb q) := by
  conv_rhs => rw [← (hbB n).sum_repr X]
  simp [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, trace_smul, hbB_apply, trace_hb_mul_hb]

theorem det_of_trace (L : Mat n →ₗ[ℂ] Mat n) :
    (Matrix.of fun p q : Fin n × Fin n => trace (L (hb p) * hb q)).det = LinearMap.det L := by
  rw [← LinearMap.det_toMatrix (hbB n) L, ← Matrix.det_transpose (LinearMap.toMatrix (hbB n) (hbB n) L)]
  congr 1
  ext p q
  simp [LinearMap.toMatrix_apply, hbB_repr, hbB_apply]

def cjHom (U : Mat n) (hU : IsUnit U.det) : Mat n →+* Mat n where
  toFun X := U⁻¹ * X * U
  map_one' := by simp [Matrix.nonsing_inv_mul U hU]
  map_mul' X Y := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U U⁻¹, Matrix.mul_nonsing_inv U hU, Matrix.one_mul]
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]

theorem cjHom_apply (U : Mat n) (hU : IsUnit U.det) (X : Mat n) : cjHom U hU X = U⁻¹ * X * U := rfl

def cjEquiv (U : Mat n) (hU : IsUnit U.det) : Mat n ≃ₗ[ℂ] Mat n where
  toFun X := U⁻¹ * X * U
  invFun X := U * X * U⁻¹
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]
  left_inv X := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv U hU, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv U hU, Matrix.one_mul]
  right_inv X := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul U hU, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul U hU, Matrix.one_mul]

theorem isUnit_det_G (k : G n) : IsUnit (k.val).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp k.isUnit

theorem tw_val {k : G n} (hk : k ∈ KU n) (d : G n) : (tw k d).val = cjHom k.val (isUnit_det_G k) d.val := by
  have h : th k = k := hk
  rw [tw, h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, cjHom_apply]

end GlobalTheory.CompanionTheory.TopClass
