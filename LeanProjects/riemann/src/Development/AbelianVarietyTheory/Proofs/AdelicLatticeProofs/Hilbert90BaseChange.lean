import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isUnit_of_forall_maximal {K A : Type} [Field K] [Infinite K] [CommRing A]
    [Algebra K A] [IsArtinianRing A] (Θ : A →ₗ[K] A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ c, Θ c ∉ 𝔪) : ∃ c, IsUnit (Θ c) := by
  classical
  have hfin := IsArtinianRing.setOf_isMaximal_finite A
  let s : Finset (Subspace K A) :=
    hfin.toFinset.image fun 𝔪 => (𝔪.restrictScalars K).comap Θ
  have hs : ⊤ ∉ s := by
    intro ht
    obtain ⟨𝔪, hm, he⟩ := Finset.mem_image.1 ht
    obtain ⟨c, hc⟩ := h 𝔪 (by simpa using hm)
    have : c ∈ (𝔪.restrictScalars K).comap Θ := by rw [he]; trivial
    exact hc this
  have hne := Subspace.biUnion_ne_univ_of_top_notMem hs
  obtain ⟨c, hc⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
  refine ⟨c, ?_⟩
  by_contra hu
  obtain ⟨𝔪, hm, hle⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
  apply hc
  simp only [Set.mem_iUnion]
  exact ⟨_, Finset.mem_image.2 ⟨𝔪, by simpa using hm, rfl⟩, hle⟩

theorem hilbert90_baseChange : ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] (τ : E ≃ₐ[F] E) (m : ℕ), orderOf τ = m → ∀ x : K ⊗[F] E, ∏ i ∈ Finset.range m, (Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E))^[i] x = 1 → ∃ z : (K ⊗[F] E)ˣ, x * Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) z = z := by
  intro F E K _ _ _ _ _ _ _ τ m hm x hx
  classical
  set T := Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) with hT
  have hm0 : 0 < m := hm ▸ orderOf_pos τ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : IsArtinianRing (K ⊗[F] E) := IsArtinianRing.of_finite K _
  have hpow : ∀ (i : ℕ) (y : K ⊗[F] E), T^[i] y = (T ^ i) y := fun i y => by
    rw [AlgHom.coe_pow]
  have htm : ∀ (i : ℕ) (k : K) (c : E), (T ^ i) (k ⊗ₜ c) = k ⊗ₜ ((τ ^ i) c) := by
    intro i k c
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, ih, AlgEquiv.mul_apply]; simp [hT]
  have hTm : ∀ y, (T ^ m) y = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k c => rw [htm, ← hm, pow_orderOf_eq_one]; rfl
    | add a b ha hb => rw [map_add, ha, hb]
  simp only [hpow] at hx
  let a : ℕ → K ⊗[F] E := fun i => ∏ j ∈ Finset.range i, (T ^ j) x
  have ha : ∀ i, x * T (a i) = a (i + 1) := by
    intro i
    simp only [a, map_prod, Finset.prod_range_succ', pow_zero, AlgHom.one_apply, pow_succ',
      AlgHom.mul_apply]
    ring
  have ha0 : a 0 = 1 := by simp [a]
  have ham : a m = 1 := hx
  let Θ : K ⊗[F] E →ₗ[K] K ⊗[F] E :=
    ∑ i ∈ Finset.range m, (LinearMap.mulLeft K (a i)).comp (T ^ i).toLinearMap
  have hΘ : ∀ c, Θ c = ∑ i ∈ Finset.range m, a i * (T ^ i) c := by
    intro c
    simp [Θ, LinearMap.sum_apply]
  have hfix : ∀ c, x * T (Θ c) = Θ c := by
    intro c
    have h1 : x * T (Θ c) = ∑ i ∈ Finset.range m, a (i + 1) * (T ^ (i + 1)) c := by
      rw [hΘ, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← mul_assoc, ha, pow_succ', AlgHom.mul_apply]
    have h2 := Finset.sum_range_succ' (fun i => a i * (T ^ i) c) m
    rw [Finset.sum_range_succ, ham, ha0, hTm, pow_zero, AlgHom.one_apply] at h2
    rw [h1, hΘ]
    exact (add_right_cancel h2).symm
  obtain ⟨c, hc⟩ := exists_isUnit_of_forall_maximal Θ (fun 𝔪 h𝔪 => by
    by_contra hcon
    push_neg at hcon
    letI : Field ((K ⊗[F] E) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    let ι : E →+* (K ⊗[F] E) ⧸ 𝔪 :=
      (Ideal.Quotient.mk 𝔪).comp Algebra.TensorProduct.includeRight.toRingHom
    let φ : Fin m → (E →* (K ⊗[F] E) ⧸ 𝔪) := fun i =>
      ι.toMonoidHom.comp ((τ ^ (i : ℕ) : E ≃ₐ[F] E) : E →* E)
    have hφ : Function.Injective φ := by
      intro i j hij
      have : τ ^ (i : ℕ) = τ ^ (j : ℕ) := by
        ext c
        exact ι.injective (DFunLike.congr_fun hij c)
      exact Fin.ext (pow_injOn_Iio_orderOf (by simp [hm]) (by simp [hm]) this)
    have hli := (linearIndependent_monoidHom E ((K ⊗[F] E) ⧸ 𝔪)).comp φ hφ
    have := Fintype.linearIndependent_iff.1 hli (fun i => Ideal.Quotient.mk 𝔪 (a i)) (by
      ext c
      have h := Ideal.Quotient.eq_zero_iff_mem.2 (hcon (1 ⊗ₜ c))
      rw [hΘ, map_sum, Finset.sum_range] at h
      simp only [htm, map_mul] at h
      rw [Finset.sum_apply]
      exact h) ⟨0, hm0⟩
    simp only [ha0, map_one] at this
    exact one_ne_zero this)
  exact ⟨hc.unit, hfix c⟩

end GlobalTheory.CNorm
