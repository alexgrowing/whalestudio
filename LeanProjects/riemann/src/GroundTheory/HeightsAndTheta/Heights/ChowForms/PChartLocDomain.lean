import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartLocDomain

variable {F : Type} [Field F] {n : ℕ}

theorem aeval_mul_of_isHomogeneous {A : Type*} [CommRing A] [Algebra F A]
    {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) (c : A) (x : Fin n → A) :
    aeval (fun m => c * x m) g = c ^ d * aeval x g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.mp hs)
  simp only [aeval_monomial, mul_pow]
  rw [Finsupp.prod_mul, Finsupp.prod_pow, Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, ← hd,
    Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [smul_eq_mul, Pi.one_apply, mul_one]
  ring

theorem linForm_isHomogeneous (u : Fin n → F) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem linForm_not_mem_sup {I : Ideal (MvPolynomial (Fin n) F)} (hI : IsProjPrime I) {t u : Fin n → F}
    (ht : linForm t ∉ I) (hu : linForm u ∉ I) : linForm u ∉ I ⊔ Ideal.span {linForm t - 1} := by
  have := hI.isPrime
  set a : MvPolynomial (Fin n) F ⧸ I := Ideal.Quotient.mk I (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ I) A).comp (Ideal.Quotient.mkₐ F I)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    rw [← comp_aeval_apply]; simp
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {d : ℕ}, g.IsHomogeneous d → ψ g = v ^ d * φ g :=
    fun hg => by rw [← hφ]; exact aeval_mul_of_isHomogeneous hg _ _
  have hle : I ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) ?_
    · rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [hhom (homogeneousComponent_isHomogeneous d g)]
      have : φ (homogeneousComponent d g) = 0 := by
        simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hI.isHomog g hg d)]
      rw [this, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
        hhom (linForm_isHomogeneous t), pow_one]
      have : φ (linForm t) = algebraMap _ A a := rfl
      rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  intro hmem
  have h0 : ψ (linForm u) = 0 := hle hmem
  rw [hhom (linForm_isHomogeneous u), pow_one] at h0
  have h1 : algebraMap _ A (Ideal.Quotient.mk I (linForm u)) = 0 :=
    calc algebraMap _ A (Ideal.Quotient.mk I (linForm u))
        = algebraMap _ A a * (v * φ (linForm u)) := by
          rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]; rfl
      _ = 0 := by rw [h0, mul_zero]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ I) A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  exact hu (Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h1.trans (map_zero _).symm)))

end ChartLocDomain

theorem ChartLocDomain.proof (h₁ : IncIdealBelow.Statement) (h₂ : ChartIncDomain.Statement)
    (h₃ : ChartKernel.Statement) : ChartLocDomain.Statement := by
  intro F _ n e I f t p _ hI hf ht
  obtain ⟨hdom, hker⟩ := h₂ F n e I t hI ht
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr (by rw [h₃ F n e I t hI ht, h₁ F n e I f hI hf])
  have hle : Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl ≤ nonZeroDivisors (ChartInc I t e) := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs ?_
    rw [hinj (h0.trans (map_zero _).symm)]
    exact p.zero_mem
  have : IsDomain (ChartLoc I t e p) := IsLocalization.isDomain_localization hle
  refine ⟨inferInstance, localizationAlgebra_injective (M := p.primeCompl) (S := ChartInc I t e)
    (Rₘ := Localization.AtPrime p) (Sₘ := ChartLoc I t e p) (hRS := hinj), fun u hu h0 => ?_⟩
  have hz : chartLin I t e u = 0 := IsLocalization.injective (ChartLoc I t e p) hle (h0.trans (map_zero _).symm)
  have hmem : linForm u ∈ RingHom.ker (chartX I t e) := hz
  rw [hker] at hmem
  exact ChartLocDomain.linForm_not_mem_sup hI ht hu hmem

end

end GroundTheory.Heights₂.Heights
