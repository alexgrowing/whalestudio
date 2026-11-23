import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapPoly

open NumberField

theorem UpperTheory.ConvolutionTheory.BW.zSpec :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.ZSpec E := by
  intro E _ _ _ n τ
  have key : ∀ ℓ : UpperTheory.V.Cm.UC E n →ₗ[ℂ] ℂ, ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ p.coeff n = ℓ 1 ∧
      (∀ u, p.eval u = ℓ (UpperTheory.V.Cm.capC τ u)) ∧ ∀ i, ℓ (zC E n τ i) = p.coeff (n - i) := fun ℓ => by
    obtain ⟨p, h1, h2, -, h4⟩ := exists_capPoly (UpperTheory.V.Cm.genC (a := n) τ) ℓ
    refine ⟨p, h1, h2, h4, fun i => ?_⟩
    have hinj : Set.InjOn (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Finset.univ : Finset (Fin (n + 1))) :=
      fun a _ b _ h => Fin.ext (Nat.cast_injective h)
    have hd : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le h1)
    conv_rhs => rw [Lagrange.eq_interpolate hinj hd]
    rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, zC, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, h4, map_smul, smul_eq_mul, mul_comm]
    rfl
  refine ⟨?_, fun u => ?_⟩
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, -, h2, -, h4⟩ := key ℓ
    rw [map_sub, h4, Nat.sub_zero, h2, sub_self]
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, h1, -, h3, h4⟩ := key ℓ
    rw [map_sub, sub_eq_zero, ← h3, map_sum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h1),
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, h4, smul_eq_mul, mul_comm]
    simp
