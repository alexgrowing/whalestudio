import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationPowSurj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIndEtaleIsDomainIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootOfUnitZeroDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPolynomialMemPrimeLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeTensorPolynomialIsMaximalOfMemImageStatement
open GlobalTheory.EtC

namespace GlobalTheory.QUnits

theorem tensorFractionRing_units_pow_surj : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ u : (TensorProduct T (FractionRing T) A)ˣ, ∃ v : (TensorProduct T (FractionRing T) A)ˣ, v ^ q = u := by
  intro q _ T _ _ _ hAIC hq O _ _ _ _ _ _ hind A _ _ _ _ π hπ u
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let L := Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  let R := TensorProduct T (FractionRing T) A
  let f : O →+* R := (Algebra.TensorProduct.includeRight : A →ₐ[T] R).toRingHom.comp π.toRingHom
  have hπT : ∀ t : T, π (algebraMap T O t) = algebraMap T A t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hfT : ∀ t : T, f (algebraMap T O t) = algebraMap T R t := by
    intro t
    change Algebra.TensorProduct.includeRight (π (algebraMap T O t)) = _
    rw [hπT, AlgHom.commutes]
  have hf : ∀ y : Algebra.algebraMapSubmonoid O (nonZeroDivisors T), IsUnit (f y) := by
    rintro ⟨_, t, ht, rfl⟩
    change IsUnit (f (algebraMap T O t))
    rw [hfT, IsScalarTower.algebraMap_apply T (FractionRing T) R]
    exact (IsLocalization.map_units (FractionRing T) ⟨t, ht⟩).map _
  let φ : L →+* R := IsLocalization.lift hf
  have hφ : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero φ⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add φ a b⟩
    | tmul k a =>
      obtain ⟨o, rfl⟩ := hπ a
      obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T) k
      refine ⟨IsLocalization.mk' L (algebraMap T O x * o)
        (⟨algebraMap T O s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩ :
          Algebra.algebraMapSubmonoid O (nonZeroDivisors T)), ?_⟩
      rw [IsLocalization.lift_mk'_spec]
      change f (algebraMap T O x * o) = f (algebraMap T O (s : T)) * _
      rw [map_mul, hfT, hfT]
      change algebraMap T R x * (Algebra.TensorProduct.includeRight (π o)) = _
      have hR : ∀ t : T, algebraMap T R t = algebraMap T (FractionRing T) t ⊗ₜ[T] (1 : A) := fun t => rfl
      rw [Algebra.TensorProduct.includeRight_apply, hR, hR, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, IsLocalization.mk'_spec']
  have hB : ∀ P : Ideal L, P.IsPrime → P ≠ ⊥ → P.IsMaximal ∧ ∀ x : L, ∃ c d : T, d ≠ 0 ∧
      algebraMap T L d * x - algebraMap T L c ∈ P := by
    intro P hP hne
    obtain ⟨g, hg, hgP⟩ := GlobalTheory.T.exists_ne_zero_polynomial_mem_prime_localization T hAIC O hind P hP hne
    exact GlobalTheory.T.prime_tensor_polynomial_isMaximal_of_mem_image T hAIC O hind P hP g hg hgP
  by_cases hJ : RingHom.ker φ = ⊥
  · have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hJ
    let e : L ≃+* R := RingEquiv.ofBijective φ ⟨hinj, hφ⟩
    obtain ⟨v, hv⟩ := GlobalTheory.LocAcycUnits.units_localization_pow_surj T O q ⟨inferInstance, hAIC⟩ hq hq0
      hind (Units.map e.symm.toMonoidHom u)
    refine ⟨Units.map e.toMonoidHom v, ?_⟩
    rw [← map_pow, hv]; ext; simp
  · let J := RingHom.ker φ
    let e : L ⧸ J ≃+* R := RingHom.quotientKerEquivOfSurjective hφ
    have hne : ∀ I : Ideal (L ⧸ J), I.comap (Ideal.Quotient.mk J) ≠ ⊥ := by
      intro I h
      apply hJ
      rw [eq_bot_iff]
      intro x hx
      rw [← h, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact I.zero_mem
    haveI : Ring.KrullDimLE 0 (L ⧸ J) := by
      refine Ring.KrullDimLE.mk₀ ?_
      intro I hI
      have hP : (I.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
      have hmax := (hB _ hP (hne I)).1
      have := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective hmax
      rw [Ideal.map_comap_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective] at this
      exact this.resolve_left hI.ne_top
    have hqL : IsUnit (q : L ⧸ J) := by
      have := hq.map (algebraMap T (L ⧸ J)); simpa using this
    have hroot : ∀ m : Ideal (L ⧸ J), m.IsMaximal → ∃ x : L ⧸ J,
        x ^ q - ((Units.map e.symm.toMonoidHom u : (L ⧸ J)ˣ) : L ⧸ J) ∈ m := by
      intro m hm
      obtain ⟨w0, hw0⟩ := Ideal.Quotient.mk_surjective
        ((Units.map e.symm.toMonoidHom u : (L ⧸ J)ˣ) : L ⧸ J)
      have hP : (m.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ _
      obtain ⟨c, d, hd, hcd⟩ := (hB _ hP (hne m)).2 w0
      obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
      obtain ⟨r, hr⟩ := hAIC (Polynomial.X ^ (n + 1) - Polynomial.C (c * d ^ n))
        (Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero n))
        (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hq0)
      have hrq : r ^ (n + 1) = c * d ^ n := by simpa [sub_eq_zero] using hr
      have hdu : IsUnit (algebraMap T L d) := by
        rw [IsScalarTower.algebraMap_apply T O L]
        exact IsLocalization.map_units L (⟨algebraMap T O d,
          Algebra.mem_algebraMapSubmonoid_of_mem (⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩ :
            nonZeroDivisors T)⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      set D := algebraMap T L d
      set Dinv : L := ((hdu.unit⁻¹ : Lˣ) : L)
      have hDn : Dinv ^ (n + 1) * D ^ (n + 1) = 1 := by
        rw [← mul_pow, IsUnit.val_inv_mul, one_pow]
      have hR : algebraMap T L r ^ (n + 1) = algebraMap T L c * D ^ n := by
        rw [← map_pow, hrq, map_mul, map_pow]
      refine ⟨Ideal.Quotient.mk J (algebraMap T L r * Dinv), ?_⟩
      rw [← hw0, ← map_pow, ← map_sub, ← Ideal.mem_comap]
      have key : (algebraMap T L r * Dinv) ^ (n + 1) - w0 =
          -(Dinv ^ (n + 1) * D ^ n) * (D * w0 - algebraMap T L c) := by
        linear_combination Dinv ^ (n + 1) * hR + w0 * hDn
      rw [key]
      exact Ideal.mul_mem_left _ _ hcd
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_root_of_unit_zero_dimensional (L ⧸ J) q hq0 hqL (Units.map e.symm.toMonoidHom u) hroot
    exact ⟨Units.map e.toMonoidHom v, by rw [← map_pow, hv]; ext; simp⟩

end GlobalTheory.QUnits
