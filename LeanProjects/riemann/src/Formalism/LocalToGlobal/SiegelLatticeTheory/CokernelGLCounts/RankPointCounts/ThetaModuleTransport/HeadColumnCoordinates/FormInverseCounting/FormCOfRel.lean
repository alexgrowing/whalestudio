import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SumGramInr

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem formC_of_rel (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E)
    (hG : IsUnit (gramC cj Z T T').det) (Y W : Ix r → O) (c : Ix r → E)
    (hY : ∀ j, (Y j : E) = ∑ i, c i * gramC cj Z T T' i j) :
    formC O cj Z T T' Y W = ∑ j, c j * cj (W j) := by
  have hc : Matrix.vecMul (fun j => (Y j : E)) (gramC cj Z T T')⁻¹ = c := by
    have hYv : (fun j => (Y j : E)) = Matrix.vecMul c (gramC cj Z T T') := by
      funext j
      rw [hY j]
      rfl
    rw [hYv, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one]
  unfold formC
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, ← congrFun hc j]
  rfl

def cvec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (Y : Ix r → O) : Ix r → E :=
  Sum.elim
    (fun a => (∑ j, cj (Z⁻¹ j a) * (Y (Sum.inr j) : E)) +
      T' * lamC Z (fun j => (Y (Sum.inl j) : E)) * cj (Z⁻¹ (Fin.last r) a))
    (fun b => (Z⁻¹.mulVec (fun j => (Y (Sum.inl j) : E))) b +
      T * lamStarC cj Z (fun j => (Y (Sum.inr j) : E)) * Z⁻¹ b (Fin.last r))

theorem cvec_gram (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hu : IsUnit Z.det) (hκ : Z⁻¹ (Fin.last r) (Fin.last r) = 0) (T T' : E) (Y : Ix r → O) :
    ∀ j, (Y j : E) = ∑ i, cvec O cj Z T T' Y i * gramC cj Z T T' i j := by
  have hZ : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z hu
  have hZ' : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z hu
  have cl : cvec O cj Z T T' Y (Sum.inl (Fin.last r)) =
      lamStarC cj Z (fun j => (Y (Sum.inr j) : E)) := by
    simp only [cvec, Sum.elim_inl, hκ, map_zero, mul_zero, add_zero, lamStarC]
  have cr : cvec O cj Z T T' Y (Sum.inr (Fin.last r)) = lamC Z (fun j => (Y (Sum.inl j) : E)) := by
    simp only [cvec, Sum.elim_inr, hκ, mul_zero, add_zero, lamC]
  intro j
  rcases j with j | j
  · rw [sum_gram_inl, cl]
    have a1 : ∑ b, Z j b * Z⁻¹.mulVec (fun k => (Y (Sum.inl k) : E)) b = (Y (Sum.inl j) : E) := by
      have := congrFun (show Z.mulVec (Z⁻¹.mulVec (fun k => (Y (Sum.inl k) : E))) =
        (fun k => (Y (Sum.inl k) : E)) by rw [Matrix.mulVec_mulVec, hZ, Matrix.one_mulVec]) j
      simpa only [Matrix.mulVec, dotProduct] using this
    have a2 : ∑ b, Z j b * Z⁻¹ b (Fin.last r) = if j = Fin.last r then 1 else 0 := by
      have := congrFun (congrFun hZ j) (Fin.last r)
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    have e1 : ∑ b, Z j b * cvec O cj Z T T' Y (Sum.inr b) =
        (Y (Sum.inl j) : E) + T * lamStarC cj Z (fun k => (Y (Sum.inr k) : E)) *
          (if j = Fin.last r then 1 else 0) := by
      simp only [cvec, Sum.elim_inr]
      rw [← a1, ← a2, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [e1]
    split_ifs <;> ring
  · rw [sum_gram_inr, cr]
    have a1 : ∀ k, ∑ a, cj (Z a j) * cj (Z⁻¹ k a) = if k = j then 1 else 0 := by
      intro k
      have := congrFun (congrFun hZ' k) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [← map_one cj, ← map_zero cj, ← apply_ite cj, ← this, map_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [map_mul, mul_comm])
    have e1 : ∑ a, cj (Z a j) * cvec O cj Z T T' Y (Sum.inl a) =
        (Y (Sum.inr j) : E) + T' * lamC Z (fun k => (Y (Sum.inl k) : E)) *
          (if Fin.last r = j then 1 else 0) := by
      simp only [cvec, Sum.elim_inl]
      rw [← a1 (Fin.last r)]
      have a3 : ∑ a, cj (Z a j) * ∑ k, cj (Z⁻¹ k a) * (Y (Sum.inr k) : E) = (Y (Sum.inr j) : E) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        have : ∀ k, ∑ a, cj (Z a j) * (cj (Z⁻¹ k a) * (Y (Sum.inr k) : E)) =
            (if k = j then 1 else 0) * (Y (Sum.inr k) : E) := by
          intro k
          rw [← a1 k, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun a _ => by ring)
        simp_rw [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← a3, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [e1]
    by_cases hj : j = Fin.last r
    · subst hj; simp only [if_true]; ring
    · rw [if_neg hj, if_neg (Ne.symm hj)]; ring

theorem formC_eq (hcj : ∀ x, cj (cj x) = x) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hu : IsUnit (Z.map O.subtype).det) (hκ : (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (T T' : E) (hG : IsUnit (gramC cj (Z.map O.subtype) T T').det) (Y W : Ix r → O) :
    formC O cj (Z.map O.subtype) T T' Y W =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) +
      cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) +
      T' * lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) *
        cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) +
      T * lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) *
        cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
  rw [formC_of_rel O cj _ T T' hG Y W _ (cvec_gram O cj hcj _ hu hκ T T' Y), Fintype.sum_sum_type]
  simp only [cvec, Sum.elim_inl, Sum.elim_inr, add_mul, Finset.sum_add_distrib]
  have s1 : ∑ a, (∑ k, cj ((Z.map O.subtype)⁻¹ k a) * (Y (Sum.inr k) : E)) * cj (W (Sum.inl a) : E) =
      cj (bRaw O cj Z (fun j => W (Sum.inl j)) (fun j => Y (Sum.inr j))) := by
    simp only [bRaw, map_sum, map_mul, hcj, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ => by ring))
  have s3 : ∑ b, (Z.map O.subtype)⁻¹.mulVec (fun j => (Y (Sum.inl j) : E)) b * cj (W (Sum.inr b) : E) =
      bRaw O cj Z (fun j => Y (Sum.inl j)) (fun j => W (Sum.inr j)) := by
    simp only [bRaw]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
  have s2 : ∑ a, T' * lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) *
        cj ((Z.map O.subtype)⁻¹ (Fin.last r) a) * cj (W (Sum.inl a) : E) =
      T' * lamC (Z.map O.subtype) (fun j => (Y (Sum.inl j) : E)) *
        cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) := by
    have e : cj (lamC (Z.map O.subtype) (fun j => (W (Sum.inl j) : E))) =
        ∑ a, cj ((Z.map O.subtype)⁻¹ (Fin.last r) a) * cj (W (Sum.inl a) : E) := by
      simp only [lamC, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have s4 : ∑ b, T * lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) *
        (Z.map O.subtype)⁻¹ b (Fin.last r) * cj (W (Sum.inr b) : E) =
      T * lamStarC cj (Z.map O.subtype) (fun j => (Y (Sum.inr j) : E)) *
        cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) := by
    have e : cj (lamStarC cj (Z.map O.subtype) (fun j => (W (Sum.inr j) : E))) =
        ∑ b, (Z.map O.subtype)⁻¹ b (Fin.last r) * cj (W (Sum.inr b) : E) := by
      simp only [lamStarC, map_sum, map_mul, hcj]
    rw [e, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  linear_combination s1 + s2 + s3 + s4

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
