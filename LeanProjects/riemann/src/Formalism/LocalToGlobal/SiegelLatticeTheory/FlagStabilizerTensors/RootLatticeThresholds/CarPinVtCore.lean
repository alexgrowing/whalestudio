import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PackageTie
import Formalism.HermitianCurvature.StatementB

noncomputable section

open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

section Trace

variable {H' H : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H']
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem hsSum_indep {ι κ : Type*} [Fintype ι] [Fintype κ] (b : OrthonormalBasis ι ℂ H') (c : OrthonormalBasis κ ℂ H')
    (A A' : H' →L[ℂ] H) : ∑ i, ⟪A (b i), A' (b i)⟫_ℂ = ∑ k, ⟪A (c k), A' (c k)⟫_ℂ := by

  set e := stdOrthonormalBasis ℂ H
  have h1 : ∀ x : H', ⟪A x, A' x⟫_ℂ = ∑ j, ⟪ContinuousLinearMap.adjoint A' (e j), x⟫_ℂ *
      ⟪x, ContinuousLinearMap.adjoint A (e j)⟫_ℂ := by
    intro x
    rw [← e.sum_inner_mul_inner (A x) (A' x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, mul_comm]
  simp_rw [h1]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  simp_rw [OrthonormalBasis.sum_inner_mul_inner]

end Trace

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V' : ι → Type*} [∀ i, NormedAddCommGroup (V' i)]
  [∀ i, InnerProductSpace ℂ (V' i)] [∀ i, FiniteDimensional ℂ (V' i)]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H']

def tB (t' : (∀ i, V' i) → H') (k : ∀ i, Fin (Module.finrank ℂ (V' i))) : H' :=
  t' (fun i => stdOrthonormalBasis ℂ (V' i) (k i))

theorem tB_orthonormal (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) :
    Orthonormal ℂ (tB t') := by
  rw [orthonormal_iff_ite]
  intro k l
  simp only [tB, ht]
  have hs : ∀ i, ⟪stdOrthonormalBasis ℂ (V' i) (k i), stdOrthonormalBasis ℂ (V' i) (l i)⟫_ℂ =
      if k i = l i then 1 else 0 := fun i =>
    orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ (V' i)).orthonormal (k i) (l i)
  simp_rw [hs]
  rw [Finset.prod_boole]
  by_cases h : k = l
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro hall
    exact h (funext fun i => hall i (Finset.mem_univ i))

theorem inner_tB_self_sum (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (x : ∀ i, V' i) : ⟪t' x, t' x⟫_ℂ = ∑ k, ⟪t' x, tB t' k⟫_ℂ * ⟪tB t' k, t' x⟫_ℂ := by
  simp only [tB, ht]
  calc ∏ i, ⟪x i, x i⟫_ℂ = ∏ i, ∑ j, ⟪x i, stdOrthonormalBasis ℂ (V' i) j⟫_ℂ *
        ⟪stdOrthonormalBasis ℂ (V' i) j, x i⟫_ℂ := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [OrthonormalBasis.sum_inner_mul_inner]
    _ = _ := by
        rw [Finset.prod_univ_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.prod_mul_distrib]

theorem mem_span_tB (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (x : ∀ i, V' i) : t' x ∈ Submodule.span ℂ (Set.range (tB t')) := by

  have hon := tB_orthonormal t' ht
  set v := t' x with hv
  set u := ∑ k, ⟪tB t' k, v⟫_ℂ • tB t' k with hu
  have huu : ⟪u, u⟫_ℂ = ∑ k, ⟪v, tB t' k⟫_ℂ * ⟪tB t' k, v⟫_ℂ := by
    rw [hu, hon.inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_conj_symm]
  have hvu : ⟪v, u⟫_ℂ = ⟪u, u⟫_ℂ := by
    rw [huu]
    conv_lhs => rw [hu]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_right, mul_comm]
  have huv : ⟪u, v⟫_ℂ = ⟪u, u⟫_ℂ := by
    rw [← inner_conj_symm, hvu, inner_conj_symm]
  have hvv : ⟪v, v⟫_ℂ = ⟪u, u⟫_ℂ := by
    rw [huu, hv]
    exact inner_tB_self_sum t' ht x
  have hz : ⟪v - u, v - u⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hvu, huv, hvv]
    ring
  have hvu' : v = u := sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  rw [hvu', hu]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

def tONB (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hsp : Submodule.span ℂ (Set.range t') = ⊤) : OrthonormalBasis (∀ i, Fin (Module.finrank ℂ (V' i))) ℂ H' :=
  OrthonormalBasis.mk (tB_orthonormal t' ht) (by
    rw [← hsp]
    exact Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact mem_span_tB t' ht x))

theorem tONB_apply (t' : (∀ i, V' i) → H') (ht : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hsp : Submodule.span ℂ (Set.range t') = ⊤) (k : ∀ i, Fin (Module.finrank ℂ (V' i))) :
    tONB t' ht hsp k = tB t' k := by
  unfold tONB
  rw [OrthonormalBasis.coe_mk]

variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem hsSum_tensor (t' : (∀ i, V' i) → H') (ht' : ∀ x y, ⟪t' x, t' y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hsp : Submodule.span ℂ (Set.range t') = ⊤) (t : (∀ i, V i) → H)
    (ht : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) (A A' : H' →L[ℂ] H) (B B' : ∀ i, V' i →L[ℂ] V i)
    (hA : ∀ x, A (t' x) = t (fun i => B i (x i))) (hA' : ∀ x, A' (t' x) = t (fun i => B' i (x i))) :
    ∑ j, ⟪A (stdOrthonormalBasis ℂ H' j), A' (stdOrthonormalBasis ℂ H' j)⟫_ℂ =
      ∏ i, ∑ j, ⟪B i (stdOrthonormalBasis ℂ (V' i) j), B' i (stdOrthonormalBasis ℂ (V' i) j)⟫_ℂ := by
  rw [hsSum_indep (stdOrthonormalBasis ℂ H') (tONB t' ht' hsp) A A', Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tONB_apply, tB, hA, hA', ht]

end Tensor

end Formalism.L2.SG.Pf.Carrier.CarPinVt
