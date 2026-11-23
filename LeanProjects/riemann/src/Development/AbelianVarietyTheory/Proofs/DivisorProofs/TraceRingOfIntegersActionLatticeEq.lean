import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleDvdOfDvdCharpolyOfAevalMatrix
open NumberField Polynomial IntermediateField

namespace GlobalTheory.LatticeTrace

theorem trace_lattice_eq : ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] [Algebra (𝓞 F) O] (La : Type) [AddCommGroup La] [Module O La] [Module.Free ℤ La] [Module.Finite ℤ La] (k : ℕ), Module.finrank ℤ La = k * Module.finrank ℚ F → ∀ c : 𝓞 F, ((LinearMap.trace ℤ La (DistribMulAction.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap : ℤ) : ℂ) = (k : ℂ) * ∑ τ : F →+* ℂ, τ (c : F) := by
  intro F _ _ O _ _ La _ _ _ _ k hk c
  classical
  set n := Module.finrank ℤ La with hn

  let φ : 𝓞 F →+* Module.End ℤ La :=
    ((addMonoidEndRingEquivInt La).toRingHom.comp (Module.toAddMonoidEnd O La)).comp (algebraMap (𝓞 F) O)
  have hφ : φ c = (DistribMulAction.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap := rfl
  let b := Module.finBasis ℤ La
  set M := LinearMap.toMatrix b b (φ c) with hM
  set M' := M.map (algebraMap ℤ ℚ) with hM'
  have hx : IsIntegral ℚ (c : F) := Algebra.IsIntegral.isIntegral _
  set f := minpoly ℚ (c : F) with hf
  have hfmon : f.Monic := minpoly.monic hx
  have hfirr : Irreducible f := minpoly.irreducible hx
  have hfZ : f = (minpoly ℤ c).map (algebraMap ℤ ℚ) := by
    rw [hf, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe c),
      RingOfIntegers.minpoly_coe]
  have hT : aeval (φ c) (minpoly ℤ c) = 0 := by
    rw [show φ c = (RingHom.toIntAlgHom φ) c from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hMz : aeval M (minpoly ℤ c) = 0 := by
    have hMe : M = LinearMap.toMatrixAlgEquiv b (φ c) := rfl
    rw [hMe, aeval_algHom_apply, hT, map_zero]
  have hM'f : aeval M' f = 0 := by
    rw [hfZ, aeval_map_algebraMap, hM', show M.map (algebraMap ℤ ℚ) = (Algebra.ofId ℤ ℚ).mapMatrix M from rfl,
      aeval_algHom_apply, hMz, map_zero]

  set r := Module.finrank ℚ⟮(c : F)⟯ F with hr
  have hdeg : Module.finrank ℚ F = f.natDegree * r := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮(c : F)⟯ F, IntermediateField.adjoin.finrank hx]
  have hsize : n = f.natDegree * (k * r) := by
    rw [hk, hdeg]; ring
  have hcp : M'.charpoly = f ^ (k * r) :=
    GlobalTheory.charpoly_eq_pow_of_aeval_irreducible_eq_zero ℚ n (k * r) M' f hfmon hfirr hM'f hsize

  have htr : (M'.trace : ℚ) = (k * r : ℚ) * -(f.nextCoeff) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have hk0 : k * r = 0 := by
        have := hsize; rw [h0] at this
        rcases Nat.mul_eq_zero.1 this.symm with h | h
        · exact absurd h (Irreducible.natDegree_pos hfirr).ne'
        · exact h
      have : M'.trace = 0 := by
        haveI : IsEmpty (Fin (Module.finrank ℤ La)) := by rw [← hn, h0]; infer_instance
        simp [Matrix.trace]
      rw [this]
      have : (k * r : ℚ) = 0 := by exact_mod_cast hk0
      rw [this, zero_mul]
    · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, hcp, Fintype.card_fin]
      have hnd : (f ^ (k * r)).natDegree = n := by rw [hfmon.natDegree_pow, hsize]; ring
      have hne : (f ^ (k * r)).nextCoeff = (f ^ (k * r)).coeff (n - 1) := by
        rw [nextCoeff, hnd, if_neg hpos.ne']
      rw [← hne, hfmon.nextCoeff_pow, nsmul_eq_mul]
      push_cast; ring

  have hTr : (∑ τ : F →+* ℂ, τ (c : F)) = algebraMap ℚ ℂ (Algebra.trace ℚ F c) := by
    rw [trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have hTr2 : Algebra.trace ℚ F c = (r : ℚ) * -(f.nextCoeff) := trace_eq_finrank_mul_minpoly_nextCoeff ℚ _
  have hL : ((LinearMap.trace ℤ La (φ c) : ℤ) : ℚ) = M'.trace := by
    rw [LinearMap.trace_eq_matrix_trace ℤ b, hM', ← hM]
    exact AddMonoidHom.map_trace (algebraMap ℤ ℚ) M
  rw [← hφ, hTr, hTr2]
  have : ((LinearMap.trace ℤ La (φ c) : ℤ) : ℂ) = algebraMap ℚ ℂ (((LinearMap.trace ℤ La (φ c) : ℤ) : ℚ)) := by simp
  rw [this, hL, htr]
  simp only [map_mul, map_neg, map_natCast]
  ring

end GlobalTheory.LatticeTrace
