import Mathlib
import Formalism.DirichletDensity.Statement

open NumberField Polynomial Matrix

noncomputable section

namespace Formalism.HF.P

lemma quad_not_sq_rat (a : ℤ) (ha : Squarefree a) (h1 : a ≠ 1) : ∀ b : ℚ, b ^ 2 ≠ (a : ℚ) := by
  intro b hb
  have hsq : IsSquare (a : ℚ) := ⟨b, by rw [← hb]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_intCast_iff.1 hsq
  have hu : IsUnit n := ha n ⟨1, by rw [hn, mul_one]⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (subst h; simp at hn; exact h1 hn)

theorem quadDiscr_ne_one (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a)
    (h4 : a % 4 = 1) (h1 : a ≠ 1) : discr K = a := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have hint : IsIntegral ℚ x := .of_finite ℚ x
  have hrank : Module.finrank ℚ K = 2 := by
    have := IntermediateField.adjoin.finrank hint
    rw [hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top'] at this
    exact this
  have htrq : ∀ q : ℚ, Algebra.trace ℚ K (algebraMap ℚ K q) = 2 * q := by
    intro q
    rw [Algebra.trace_algebraMap, hrank]; simp
  have htrlin : ∀ (q : ℚ) (z : K), Algebra.trace ℚ K (algebraMap ℚ K q * z) =
      q * Algebra.trace ℚ K z := by
    intro q z
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have htrx : Algebra.trace ℚ K x = 0 := by
    have hnc : (X ^ 2 - C (a : ℚ)).nextCoeff = 0 := by
      rw [nextCoeff, natDegree_X_pow_sub_C, coeff_sub, coeff_X_pow, coeff_C]; norm_num
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, hnc]; simp
  set ω : K := (1 + x) / 2 with hω
  have hω1 : ω = algebraMap ℚ K (1 / 2) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; ring
  have hω2 : ω * ω = algebraMap ℚ K ((1 + a) / 4) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; linear_combination (1 / 4 : K) * hx
  have htr1 : Algebra.trace ℚ K 1 = 2 := by
    rw [show (1 : K) = algebraMap ℚ K 1 by simp, htrq]; norm_num
  have htrω : Algebra.trace ℚ K ω = 1 := by
    rw [hω1, map_add, htrq, htrlin, htrx]; norm_num
  have htrωω : Algebra.trace ℚ K (ω * ω) = (1 + a) / 2 := by
    rw [hω2, map_add, htrq, htrlin, htrx]; ring
  have hdisc : Algebra.discr ℚ ![(1 : K), ω] = a := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, mul_one]
    rw [htr1, htrω, htrωω]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℤ, a = 4 * c + 1 := ⟨a / 4, by omega⟩
  have hcK : (a : K) = 4 * c + 1 := by rw [hc]; push_cast; ring
  have hωint : IsIntegral ℤ ω := by
    refine ⟨X ^ 2 - X - C c, ?_, ?_⟩
    · monicity!
    · rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast, hω]
      linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hcK
  let B := RingOfIntegers.basis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← hrank, Module.finrank_eq_card_basis (integralBasis K)]
  let e := Fintype.equivFinOfCardEq hcard
  let B' : Module.Basis (Fin 2) ℤ (𝓞 K) := B.reindex e
  let Cb : Module.Basis (Fin 2) ℚ K := (integralBasis K).reindex e
  have hC : ∀ i, Cb i = ((B' i : 𝓞 K) : K) := by
    intro i; simp [Cb, B', B, integralBasis_apply]
  let ω' : 𝓞 K := ⟨ω, hωint⟩
  let v : Fin 2 → 𝓞 K := ![1, ω']
  let P : Matrix (Fin 2) (Fin 2) ℤ := B'.toMatrix v
  have hv : ![(1 : K), ω] = Cb ᵥ* (P.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ K) := by
    have h0 := B'.toMatrix_map_vecMul v
    funext j
    have hj := congrArg (fun w : Fin 2 → 𝓞 K => ((w j : 𝓞 K) : K)) h0
    have hvj : ((v j : 𝓞 K) : K) = ![(1 : K), ω] j := by
      fin_cases j <;> rfl
    rw [← hvj, ← hj]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hC, P]
  have key : (a : ℚ) = ((P.det : ℤ) : ℚ) ^ 2 * (discr K : ℚ) := by
    rw [← hdisc, hv, Algebra.discr_of_matrix_vecMul, coe_discr, Module.Basis.coe_reindex,
      Algebra.discr_reindex]
    congr 2
    exact (RingHom.map_det (Int.castRingHom ℚ) P).symm
  have key' : a = P.det ^ 2 * discr K := by exact_mod_cast key
  have hu : IsUnit P.det := hsf P.det ⟨discr K, by rw [key']; ring⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (rw [key', h]; ring)

end Formalism.HF.P

theorem Formalism.HF.quadDiscr : Formalism.HF.QuadDiscr := by
  intro K _ _ a x hx hadj hsf h4
  by_cases h1 : a = 1
  · subst h1
    have hx1 : x * x = 1 := by rw [← sq, hx]; simp
    have hbot : x ∈ (⊥ : IntermediateField ℚ K) := by
      rcases mul_self_eq_one_iff.1 hx1 with h | h
      · rw [h]; exact IntermediateField.one_mem _
      · rw [h]; exact IntermediateField.neg_mem _ (IntermediateField.one_mem _)
    have htop : (⊥ : IntermediateField ℚ K) = ⊤ := by
      rw [← hadj, eq_comm]; exact IntermediateField.adjoin_simple_eq_bot_iff.2 hbot
    let e : ℚ ≃ₐ[ℚ] K := (IntermediateField.botEquiv ℚ K).symm.trans
      ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
    rw [← NumberField.discr_eq_discr_of_algEquiv ℚ e, NumberField.discr_rat]
  · exact Formalism.HF.P.quadDiscr_ne_one K a x hx hadj hsf h4 h1
