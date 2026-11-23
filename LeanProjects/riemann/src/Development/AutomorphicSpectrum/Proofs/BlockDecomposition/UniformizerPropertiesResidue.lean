import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem uniformiser_facts : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    2 ≤ qOf π ∧ l ∣ qOf π ∧ π ∣ (l : ↥(OL K)) ∧
      ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 ∧ ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
  intro l _ K π hπ
  obtain ⟨⟨⟨hD, hV, -⟩, -⟩, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l K
  have hlp : l.Prime := Fact.out
  have hi : Algebra.IsIntegral ℤ_[l] ↥(OL K) := integralClosure.AlgebraIsIntegral
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL K)) := by
    intro a b hab
    have h1 : algebraMap ℤ_[l] ↥K.1 a = algebraMap ℤ_[l] ↥K.1 b := congrArg Subtype.val hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1 b] at h1
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] ↥K.1).injective h1)
  have hf : FaithfulSMul ℤ_[l] ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hl : ¬ IsUnit ((l : ℕ) : ↥(OL K)) := by
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] ↥(OL K))] at hu
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_map_unit _ _ hu)
  have hdvd : π ∣ ((l : ℕ) : ↥(OL K)) := by
    have hm : ((l : ℕ) : ↥(OL K)) ∈ IsLocalRing.maximalIdeal ↥(OL K) := hl
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have hle : Ideal.span {((l : ℕ) : ↥(OL K)) ^ 1} ≤ Ideal.span {π} := by
    rw [pow_one, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hfinQ : Finite (↥(OL K) ⧸ Ideal.span {π}) := by
    have := hfin 1
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have hnt : Nontrivial (↥(OL K) ⧸ Ideal.span {π}) := by
    refine Ideal.Quotient.nontrivial_iff.2 ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hπ.not_isUnit
  have h2 : 2 ≤ qOf π := Finite.one_lt_card
  have hord : addOrderOf (1 : ↥(OL K) ⧸ Ideal.span {π}) = l := by
    have h1 : (1 : ↥(OL K) ⧸ Ideal.span {π}) ≠ 0 := by
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), Ne, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
    refine addOrderOf_eq_prime ?_ h1
    rw [nsmul_one, ← map_natCast (Ideal.Quotient.mk (Ideal.span {π})),
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hq : l ∣ qOf π := by
    have := addOrderOf_dvd_natCard (1 : ↥(OL K) ⧸ Ideal.span {π})
    rwa [hord] at this
  have hl0 : ((l : ℕ) : ↥(OL K)) ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : ↥(OL K) => (x : ↥K.1)) h
    simp only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2
    exact hlp.ne_zero (by exact_mod_cast h2)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hπ
  have he : e ≠ 0 := by
    rintro rfl
    apply hl
    rw [pow_zero] at hu
    exact IsUnit.of_mul_eq_one _ hu
  have hnorm : ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
    intro μ
    rw [PadicComplex.norm_extends]
    have hint : ∀ x : ↥(OL K), ‖μ (x : ↥K.1)‖ ≤ 1 := by
      intro x
      rw [← GlobalTheory.isIntegral_padicInt_iff_norm_le_one]
      exact (x.2 : IsIntegral ℤ_[l] (x : ↥K.1)).map (μ.restrictScalars ℤ_[l])
    have hpow : (π : ↥K.1) ^ e = (l : ↥K.1) * ((u : ↥(OL K)) : ↥K.1) := by
      have := congrArg (fun x : ↥(OL K) => (x : ↥K.1)) hu
      simpa using this.symm
    have h3 : ‖μ (π : ↥K.1)‖ ^ e < 1 := by
      rw [← norm_pow, ← map_pow, hpow, map_mul, norm_mul, map_natCast,
        ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) Padic.norm_p_lt_one (hint _)
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 h3
  exact ⟨h2, hq, hdvd, hnorm K.1.val, hnorm⟩

end GlobalTheory.CompanionTheory.LTPer
