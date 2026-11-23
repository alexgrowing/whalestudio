import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.Mem.CharAlg

theorem bijective_cmType {L : Type} [Field L] [IsTotallyComplex L] {I : Type} (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
  have hne : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    have h1 : i = j := h.1 (by
      show InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j)
      rw [hij, InfinitePlace.mk_conjugate_eq])
    subst h1
    exact IsTotallyComplex.complexEmbedding_not_isReal (φ i) (ComplexEmbedding.isReal_iff.2 hij.symm)
  constructor
  · rintro (i | i) (j | j) hij
    · have hij' : φ i = φ j := hij
      exact congrArg Sum.inl (h.1 (congrArg InfinitePlace.mk hij'))
    · exact absurd hij (hne i j)
    · exact absurd hij.symm (hne j i)
    · have hij' : ComplexEmbedding.conjugate (φ i) = ComplexEmbedding.conjugate (φ j) := hij
      refine congrArg Sum.inr (h.1 ?_)
      show InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j)
      rw [← InfinitePlace.mk_conjugate_eq (φ i), hij', InfinitePlace.mk_conjugate_eq]
  · intro ψ
    obtain ⟨i, hi⟩ := h.2 (InfinitePlace.mk ψ)
    rcases InfinitePlace.mk_eq_iff.1 hi with hi | hi
    · exact ⟨Sum.inl i, hi⟩
    · exact ⟨Sum.inr i, hi⟩

theorem prod_split {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) (f : (L →+* ℂ) → ℂ) :
    ∏ ψ, f ψ = ∏ i, (f (φ i) * f (ComplexEmbedding.conjugate (φ i))) := by
  rw [← (bijective_cmType φ h).prod_comp f, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  rfl

theorem isAlg_of {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (a b : I → ℤ)
    (hχ : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i k ^ a i * (starRingEnd ℂ (φ i k)) ^ b i)) :
    ∃ n, χ.IsAlg n := by
  let e := Equiv.ofBijective _ (bijective_cmType φ h)
  refine ⟨fun ψ => Sum.elim a b (e.symm ψ), fun k => ?_⟩
  rw [hχ k, prod_split φ h]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : e.symm (φ i) = Sum.inl i := e.symm_apply_eq.2 rfl
  have h2 : e.symm (ComplexEmbedding.conjugate (φ i)) = Sum.inr i := e.symm_apply_eq.2 rfl
  simp only [h1, h2, Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq]

theorem even_pow {z : ℂ} (hz : z ≠ 0) (c : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * c) = z ^ c * (starRingEnd ℂ z) ^ (-c) := by
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
    rw [zpow_ofNat, div_pow, ← Complex.mul_conj', sq, mul_div_mul_left _ _ hz]
  rw [zpow_mul, h, div_zpow, zpow_neg, div_eq_mul_inv]

theorem odd_pow {z : ℂ} (hz : z ≠ 0) (m : ℕ) :
    ((z / ((‖z‖ : ℝ) : ℂ)) ^ (1 : ℤ))⁻¹ *
      (((‖z‖ : ℝ) : ℂ) ^ (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) *
        ((‖z‖ : ℝ) : ℂ) ^ (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)) =
      z ^ (-1 - (m : ℤ)) * (starRingEnd ℂ z) ^ (-(m : ℤ)) := by
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz
  have he : (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) + (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) =
      -((2 * m + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [← Complex.cpow_add _ _ hn, he, Complex.cpow_neg, Complex.cpow_natCast, pow_succ, pow_mul,
    ← Complex.mul_conj', zpow_sub₀ hz, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_one, zpow_one, mul_pow]
  field_simp

theorem isAlg_even_odd : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), (∀ (χ : HChar H.E) (c : R.Psi → ℤ), χ.HasInf (embPsi H) (fun τ => 2 * c τ) → ∃ n, χ.IsAlg n) ∧ ∀ (η : HChar H.E), η.HasInf (embPsi H) (fun _ => 1) → ∀ r : ℕ, Odd r → ∃ n, (η⁻¹ * GlobalTheory.HeckeGal.Model.absPow H.E (-(r : ℝ) / 2)).IsAlg n := by
  intro R H
  obtain ⟨c0, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have := hcm.cplx
  have hz : ∀ (i : R.Psi) (k : (H.E)ˣ), embPsi H i (k : H.E) ≠ 0 := fun i k => by simp
  refine ⟨fun χ c hχ => isAlg_of (embPsi H) hcm.bij χ c (fun i => -c i) fun k => ?_, ?_⟩
  · rw [hχ k]
    exact Finset.prod_congr rfl fun i _ => even_pow (hz i k) (c i)
  · rintro η hη r ⟨m, rfl⟩
    refine isAlg_of (embPsi H) hcm.bij _ (fun _ => -1 - (m : ℤ)) (fun _ => -(m : ℤ)) fun k => ?_
    rw [HChar.inf_mul, HChar.inf_inv, Units.val_mul, Units.val_inv_eq_inv_val, hη k,
      (GlobalTheory.HeckeGal.Model.absPow_isAbsPow H.E _).2.2 k, prod_split (embPsi H) hcm.bij, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    exact odd_pow (hz i k) m

end GlobalTheory.Mem.CharAlg
