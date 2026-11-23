import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TMemLaurentFiltration

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

theorem flt_twistMat_mem (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k e t : ℤ) (h0 : t ≤ 0) (hk : t ≤ e * k)
    (b c : Fin n) : twistMat R n j k b c ∈ (flt_L (GLCoord R n) e).F t := by
  unfold twistMat
  rw [Matrix.mul_apply]
  refine sum_mem fun a _ => ?_
  rw [Matrix.mul_diagonal]
  have hg : gL R n b a ∈ (flt_L (GLCoord R n) e).F 0 := by
    simp only [gL, Matrix.map_apply]
    exact flt_L_C e _
  have hgi : gLinv R n a c ∈ (flt_L (GLCoord R n) e).F 0 := by
    simp only [gLinv, Matrix.map_apply]
    exact flt_L_C e _
  have hd : (if a = j then LaurentPolynomial.T k else 1) ∈ (flt_L (GLCoord R n) e).F t := by
    split_ifs
    · exact (flt_L (GLCoord R n) e).anti hk (T_mem_laurentFiltration e k)
    · exact (flt_L (GLCoord R n) e).anti h0 (flt_L (GLCoord R n) e).one_mem
  have hm := (flt_L (GLCoord R n) e).mul_mem ((flt_L (GLCoord R n) e).mul_mem hg hd) hgi
  rwa [zero_add, add_zero] at hm

open Classical in

def flt_cost {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) : (ι × Fin n →₀ ℕ) →+ ℤ :=
  Finsupp.liftAddHom fun v => if v.1 ∈ S ∧ LL.vec v.1 = b then Nat.castAddMonoidHom ℤ else 0

open Classical in
theorem flt_cost_single {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) (v : ι × Fin n) (k : ℕ) :
    flt_cost LL S b (Finsupp.single v k) = if v.1 ∈ S ∧ LL.vec v.1 = b then (k : ℤ) else 0 := by
  unfold flt_cost
  rw [Finsupp.liftAddHom_apply_single]
  split_ifs
  · rfl
  · rfl

def flt_compat (e : ℤ) (bm : Bool) : Prop := (e = 1 ∧ bm = false) ∨ (e = -1 ∧ bm = true)

theorem flt_twistX_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (v : ι × Fin n) :
    twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F ((-flt_cost LL S bm) (Finsupp.single v 1)) := by
  classical
  have hX : ∀ w : ι × Fin n,
      (X w : MvPolynomial (ι × Fin n) (GLLaurent R n)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F 0 := by
    intro w
    rw [laurentCoeffFiltration, flt_lift_mem]
    intro m
    rw [AddMonoidHom.zero_apply, sub_zero, MvPolynomial.coeff_X]
    split_ifs
    · exact (flt_L (GLCoord R n) e).one_mem
    · exact zero_mem _
  have hterm : ∀ (a : GLLaurent R n) (w : ι × Fin n) (t : ℤ), a ∈ (flt_L (GLCoord R n) e).F t →
      MvPolynomial.C a * X w ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t := by
    intro a w t ha
    have hm := (laurentCoeffFiltration R n (ι × Fin n) e).mul_mem (flt_C_mem ha) (hX w)
    rwa [add_zero] at hm
  unfold twistSub
  rw [MvPolynomial.eval₂Hom_X', AddMonoidHom.neg_apply, flt_cost_single]
  by_cases hS : v.1 ∈ S
  · rw [if_pos hS]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases hb : LL.vec v.1 <;> simp only [hS, true_and] <;>
      norm_num <;>
      exact sum_mem fun b _ => hterm _ _ _ (flt_twistMat_mem R n j _ _ _ (by norm_num) (by norm_num) _ _)
  · rw [if_neg hS, if_neg (fun h' => hS h'.1), neg_zero]
    exact hX v

theorem flt_twist_monomial_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (al : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al (1 : R)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F (-flt_cost LL S bm al) :=
  flt_hom_monomial (laurentCoeffFiltration R n (ι × Fin n) e) (twistSub LL S j) (-flt_cost LL S bm)
    (fun w => flt_twistX_mem LL S j h w) al

theorem flt_gL_mul_gLinv (R : Type*) [CommRing R] (n : ℕ) : gL R n * gLinv R n = 1 := by
  ext i k
  have hu : algebraMap _ (GLCoord R n) (genMat R n).det *
      IsLocalization.Away.invSelf (genMat R n).det = 1 :=
    IsLocalization.Away.mul_invSelf _
  have e : ∑ j, algebraMap _ (GLCoord R n) (genMat R n i j) *
      (IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) ((genMat R n).adjugate j k)) =
      IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) ((genMat R n * (genMat R n).adjugate) i k) := by
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  rw [Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at e
  simp only [Matrix.mul_apply, gL, gLinv, Matrix.map_apply, ← map_mul, ← map_sum, e,
    Matrix.one_apply]
  split_ifs
  · rw [mul_one, mul_comm, hu, map_one]
  · rw [mul_zero, map_zero, mul_zero, map_zero]

theorem flt_gLinv_mul_gL (R : Type*) [CommRing R] (n : ℕ) : gLinv R n * gL R n = 1 :=
  mul_eq_one_comm.1 (flt_gL_mul_gLinv R n)

theorem flt_twistMat_mul (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) :
    twistMat R n j k * twistMat R n j (-k) = 1 := by
  have hd : Matrix.diagonal (fun a => if a = j then (LaurentPolynomial.T k : GLLaurent R n) else 1) *
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-k) else 1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs
    · rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
    · rw [one_mul]
  unfold twistMat
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gLinv R n) (gL R n), flt_gLinv_mul_gL, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hd, Matrix.one_mul, flt_gL_mul_gLinv]

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
