import Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas
import Formalism.LocalToGlobal.IndefiniteReal.PHeisThA
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StdCharExists

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

theorem hO_add_left (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_add_left (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO
  rw [hO_add_left, mul_add, map_add]

theorem symplO_add_right (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add]

theorem symplO_zero_left (y : WO S T) : symplO S T 0 y = 0 := by
  have h := symplO_add_left S T 0 0 y
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_zero_right (x : WO S T) : symplO S T x 0 = 0 := by
  have h := symplO_add_right S T x 0 0
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_neg_left (x y : WO S T) : symplO S T (-x) y = -symplO S T x y := by
  have h := symplO_add_left S T x (-x) y
  have h0 : x + -x = 0 := by simp
  rw [h0, symplO_zero_left] at h
  linear_combination -1 * h

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  have h0 : y + -y = 0 := by simp
  rw [h0, symplO_zero_right] at h
  linear_combination -1 * h

abbrev MO : Type := Matrix (Fin T.rank) (Fin S.rank) (AE D)

def hOM (x y : MO S T) : Matrix (Fin S.rank) (Fin S.rank) (AE D) :=
  HMul.hMul (HMul.hMul (HMul.hMul (Brg.GI S) (y.map (cA D))ᵀ) (Brg.GG T)) x

theorem hO_eq_trace (x y : MO S T) : hO S T x y = (hOM S T x y).trace := by
  unfold hO hOM
  simp only [Brg.GI, Brg.GG, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext d; rw [Finset.sum_comm]

theorem cA_trace {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) : cA D M.trace = ((M.map (cA D))ᵀ).trace := by
  rw [Matrix.trace_transpose]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem hO_swap (x y : MO S T) : hO S T y x = cA D (hO S T x y) := by
  have e0 : (y.map (cA D)).map (cA D) = y := by ext i j; simp [cA_cA]
  have e2 : ((hOM S T x y).map (cA D))ᵀ =
      HMul.hMul (HMul.hMul (HMul.hMul (x.map (cA D))ᵀ (Brg.GG T)) y) (Brg.GI S) := by
    unfold hOM
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Brg.GI_herm, Brg.GG_herm, Matrix.transpose_map, e0, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [hO_eq_trace, hO_eq_trace, cA_trace, e2, Matrix.trace_mul_comm]
  unfold hOM
  simp only [Matrix.mul_assoc]

theorem symplO_swap (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [hO_swap S T x y]
  have e : incA D D.host.xi0 * cA D (hO S T x y) = cA D (cA D (incA D D.host.xi0) * hO S T x y) := by
    rw [map_mul, cA_cA]
  rw [e, Brg.trace_cA, Brg.cA_inc, Brg.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem symplOH_add_left (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  unfold symplOH
  rw [symplO_add_left, mul_add]

theorem symplOH_add_right (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  unfold symplOH
  rw [symplO_add_right, mul_add]

theorem symplOH_swap (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_swap, mul_neg]

theorem symplOH_two (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add]
  norm_num

theorem ratW_add (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S (a + b) = ratW T S a + ratW T S b := by
  exact Matrix.map_add _ (map_add (incA D)) a b

theorem ratW_neg (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ratW T S (-a) = -ratW T S a := by
  exact Matrix.map_neg _ (map_neg (incA D)) a

theorem ratW_zero : ratW T S (0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E) = 0 := by
  exact Matrix.map_zero _ (map_zero (incA D))

theorem mem_ratL_iff (x : WO S T) : x ∈ ratL T S ↔ ∃ a, ratW T S a = x := by
  unfold ratL
  simp only [AddMonoidHom.mem_range]
  exact Iff.rfl

theorem incA_eq_tmul (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem trace_incA (e : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D e) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  rw [incA_eq_tmul]
  exact Formalism.IndefR.PHeisTh.trace_tmul _

theorem hO_rat (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ e : D.host.E, hO S T (ratW T S a) (ratW T S b) = incA D e := by
  refine ⟨∑ i, ∑ j, ∑ k, ∑ l, (HSpace.gram S)⁻¹ i j * D.sp.cm.sig (b k j) * HSpace.gram T k l * a l i, ?_⟩
  unfold hO ratW
  simp only [Matrix.map_apply, Formalism.IndefR.PHeisTh.cA_incA, map_sum, map_mul]

theorem symplO_rat (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ q : D.host.F, symplO S T (ratW T S a) (ratW T S b) = algebraMap D.host.F (AF D.host.F) q := by
  obtain ⟨e, he⟩ := hO_rat S T a b
  refine ⟨Algebra.trace D.host.F D.host.E (D.host.xi0 * e), ?_⟩
  unfold symplO
  rw [he, ← map_mul, trace_incA]

end Formalism.IndefR.Fin

end
