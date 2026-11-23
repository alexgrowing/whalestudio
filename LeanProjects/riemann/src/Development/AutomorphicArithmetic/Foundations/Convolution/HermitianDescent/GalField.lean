import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll

noncomputable section

namespace UpperTheory.ConvolutionTheory.D

open Classical in
private theorem dual_sum (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (τ : E ≃ₐ[F] E) :
    ∑ i, b i * τ (b.traceDual i) = if τ = 1 then 1 else 0 := by
  have li : LinearIndependent E (fun t : E ≃ₐ[F] E => ((t : E →* E) : E → E)) :=
    (linearIndependent_monoidHom E E).comp (fun t : E ≃ₐ[F] E => (t : E →* E))
      (fun s t h => AlgEquiv.ext fun x => DFunLike.congr_fun h x)
  have key := Fintype.linearIndependent_iff.1 li
    (fun t => (∑ i, b i * t (b.traceDual i)) - if t = 1 then 1 else 0) ?_ τ
  · exact sub_eq_zero.1 key
  funext z
  have hz : z = ∑ i, b i * algebraMap F E (Algebra.trace F E (b.traceDual i * z)) := by
    conv_lhs => rw [← b.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Algebra.trace F E (b.traceDual i * z) = b.repr z i := by
      conv_lhs => rw [← b.sum_repr z]
      simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, Module.Basis.trace_traceDual_mul]
      simp
    rw [this, Algebra.smul_def, mul_comm]
  simp only [trace_eq_sum_automorphisms, Finset.mul_sum, map_mul] at hz
  rw [Finset.sum_comm] at hz
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply, mul_assoc]
  exact sub_eq_zero.2 hz.symm

theorem galField : GalField := by
  classical
  intro F E _ _ _ _ _ σ hσ
  have ho : orderOf σ = Module.finrank F E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  refine ⟨Module.finrank_pos, ho ▸ pow_orderOf_eq_one σ, (algebraMap F E).injective, fun r hr => ?_,
    Module.finrank F E, Module.finBasis F E, (Module.finBasis F E).traceDual, fun j hj => ?_⟩
  · have h : ∀ τ : E ≃ₐ[F] E, τ r = r := fun τ => by
      have : Subgroup.zpowers σ ≤ MulAction.stabilizer (E ≃ₐ[F] E) r :=
        (Subgroup.zpowers_le).2 hr
      exact this (hσ τ)
    exact (IsGalois.mem_range_algebraMap_iff_fixed r).2 h
  · have := dual_sum F E (Module.finBasis F E) (σ ^ j)
    rw [show (if j = 0 then (1 : E) else 0) = if σ ^ j = 1 then 1 else 0 from
      if_congr ⟨fun h => by rw [h, pow_zero], fun h =>
        Nat.eq_zero_of_dvd_of_lt (orderOf_dvd_of_pow_eq_one h) (ho ▸ hj)⟩ rfl rfl]
    convert this

end UpperTheory.ConvolutionTheory.D
