import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem intTrace_modEq (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))
    (hvI : IsCoprime v.asIdeal I) (hpI : Ideal.span {(p : 𝓞 K)} = v.asIdeal * I)
    (hnorm : Ideal.absNorm v.asIdeal = p) (x : 𝓞 K) (b : ℤ) (hxv : x - (b : 𝓞 K) ∈ v.asIdeal) (hxI : x ∈ I) :
    ∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m := by
  classical
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPm : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI := Ideal.Quotient.field P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) P = v.asIdeal * I := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_natCast]; exact hpI
  have hPv : P ≤ v.asIdeal.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_left (I := v.asIdeal) (J := I)
  have hPI : P ≤ I.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_right (I := v.asIdeal) (J := I)
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap hPv
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap hPI
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ I) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ I) := Module.Finite.of_restrictScalars_finite ℤ _ _
  let e : (𝓞 K ⧸ Ideal.map (algebraMap ℤ (𝓞 K)) P) ≃ₐ[ℤ ⧸ P] ((𝓞 K ⧸ v.asIdeal) × (𝓞 K ⧸ I)) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientMulEquivQuotientProd v.asIdeal I hvI),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have he : e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk v.asIdeal x, Ideal.Quotient.mk I x) := rfl
  have hx2 : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have hx1 : Ideal.Quotient.mk v.asIdeal x = algebraMap (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk P b) := by
    rw [Ideal.Quotient.eq.mpr hxv]
    show _ = Ideal.Quotient.mk v.asIdeal (algebraMap ℤ (𝓞 K) b)
    rw [algebraMap_int_eq, eq_intCast]
  have hcardP : Nat.card (ℤ ⧸ P) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hcardv : Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
    rw [← hnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfr : Module.finrank (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ℤ ⧸ P) (V := 𝓞 K ⧸ v.asIdeal)
    rw [hcardP, hcardv] at h
    exact (Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm))
  have key : Ideal.Quotient.mk P (Algebra.intTrace ℤ (𝓞 K) x) = Ideal.Quotient.mk P b := by
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv e, he,
      Algebra.trace_prod_apply, hx2, map_zero, add_zero, hx1, Algebra.trace_algebraMap, hfr, one_smul]
  rw [Ideal.Quotient.eq, hPdef, Ideal.mem_span_singleton] at key
  obtain ⟨m, hm⟩ := key
  exact ⟨m, by linear_combination hm⟩

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem integral_of_mul (w : HeightOneSpectrum (𝓞 K)) (n z s y : 𝓞 K) (hn : n ≠ 0) (hs : s ∉ w.asIdeal)
    (h : z * s = n * y) :
    algebraMap K (Af K) ((z : K) / (n : K)) w ∈ w.adicCompletionIntegers K := by
  have hs0 : (s : K) ≠ 0 := by
    intro h0; apply hs; rw [show s = 0 from by exact_mod_cast h0]; exact zero_mem _
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn
  have hq : (z : K) / (n : K) = (y : K) / (s : K) := by
    rw [div_eq_div_iff hn0 hs0]
    have := congrArg (fun t : 𝓞 K => (t : K)) h
    simp only [map_mul] at this
    push_cast at this
    linear_combination this
  rw [hq, HeightOneSpectrum.mem_adicCompletionIntegers]
  have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ((y : K) / (s : K))
  erw [e]
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, div_one]
  exact HeightOneSpectrum.intValuation_le_one w y

theorem exists_cofactor (p : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) :
    ∃ I : Ideal (𝓞 K), IsCoprime v.asIdeal I ∧ Ideal.span {(p : 𝓞 K)} = v.asIdeal * I := by
  have hpv : (p : 𝓞 K) ∈ v.asIdeal := by
    have := Ideal.absNorm_mem v.asIdeal
    rwa [hnorm] at this
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hpv)
  refine ⟨I, ?_, hI⟩
  have hpr := (Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime
  rw [Ideal.isCoprime_iff_gcd, hpr.irreducible.gcd_eq_one_iff]
  rintro ⟨J, rfl⟩
  apply hsq
  have : Ideal.span {(p : 𝓞 K)} ≤ v.asIdeal ^ 2 := by
    rw [hI, pow_two, ← mul_assoc]; exact Ideal.mul_le_left (I := v.asIdeal * v.asIdeal) (J := J)
  exact this (Ideal.mem_span_singleton_self _)

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem fin_part (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) (α : Af K)
    (hα1 : evalV K v α = 1) (hα0 : ∀ w, w ≠ v → evalV K w α = 0) (a : 𝓞 K) (b : ℤ)
    (hab : a - (b : 𝓞 K) ∈ v.asIdeal) :
    ∃ x : 𝓞 K, (∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (α * algebraMap K (Af K) ((a : K) / (p : K)) -
        algebraMap K (Af K) ((x : K) / (p : K))) w ∈ w.adicCompletionIntegers K := by
  obtain ⟨I, hvI, hpI⟩ := exists_cofactor p v hnorm hsq
  obtain ⟨u, hu, t, ht, hut⟩ := Ideal.isCoprime_iff_exists.mp hvI
  have htv : t ∉ v.asIdeal := fun h =>
    v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hut ▸ add_mem hu h))
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmemp : ∀ z ∈ v.asIdeal * I, ∃ y, z = (p : 𝓞 K) * y := fun z hz => by
    rw [← hpI, Ideal.mem_span_singleton'] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, by rw [← hy, mul_comm]⟩
  have hxv : (b : 𝓞 K) * t - b ∈ v.asIdeal := by
    have e : (b : 𝓞 K) * t - b = -((b : 𝓞 K) * u) := by linear_combination (b : 𝓞 K) * hut
    rw [e]; exact neg_mem (Ideal.mul_mem_left _ _ hu)
  refine ⟨b * t, intTrace_modEq p hp v I hvI hpI hnorm _ b hxv (Ideal.mul_mem_left _ _ ht), fun w => ?_⟩
  have hcomp : (α * algebraMap K (Af K) ((a : K) / (p : K)) - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K))) w =
      α w * algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w := rfl
  rw [hcomp]
  by_cases hw : w = v
  · subst hw
    have h1 : α w = 1 := hα1
    have hsub : algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w =
        algebraMap K (Af K) (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) w := by
      rw [show (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) =
        (a : K) / (p : K) - ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) by push_cast; ring, map_sub]
      rfl
    rw [h1, one_mul, hsub]
    have hmem : (a - (b : 𝓞 K) * t) * t ∈ w.asIdeal * I := by
      refine Ideal.mul_mem_mul ?_ ht
      have e : a - (b : 𝓞 K) * t = (a - b) - ((b : 𝓞 K) * t - b) := by ring
      rw [e]; exact sub_mem hab hxv
    obtain ⟨y, hy⟩ := hmemp _ hmem
    exact integral_of_mul w _ _ t y hp0 htv hy
  · have h0 : α w = 0 := hα0 w hw
    rw [h0, zero_mul, zero_sub]
    refine neg_mem ?_
    obtain ⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by
      by_contra hc
      push_neg at hc
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)
    obtain ⟨y, hy⟩ := hmemp _ (Ideal.mul_mem_mul hsv (Ideal.mul_mem_left _ (b : 𝓞 K) ht))
    have := integral_of_mul w (p : 𝓞 K) ((b : 𝓞 K) * t) s y hp0 hsw (by rw [mul_comm]; exact hy)
    simpa using this

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

theorem stdChar_placeIdem_div : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  intro D ψ hψ p hp v hnorm hsq ε hε a b hab
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  obtain ⟨x, ⟨m, hm⟩, hint⟩ := fin_part p hp v hnorm hsq α hα1 hα0 a b hab
  have hsplit : pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F)) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) +
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * _ = 0 + 0
      rw [zero_mul, add_zero]
    · show α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) =
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)) +
        (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
          algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))
      rw [add_sub_cancel]
  have htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ) :=
    fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm
  have h1 : ψ (pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))) = 1 := by
    refine GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1})
      (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
      (fun r => ?_) _ hint
    show ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (r : D.host.F))) = 1
    rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]
  have hq : Algebra.trace ℚ D.host.F ((x : D.host.F) / (p : D.host.F)) = ((b : ℚ) + p * m) / p := by
    have e : (x : D.host.F) / (p : D.host.F) = ((p : ℚ)⁻¹) • (x : D.host.F) := by
      rw [Algebra.smul_def, map_inv₀, map_natCast, div_eq_inv_mul]
    rw [e, map_smul, htr, hm, smul_eq_mul]
    push_cast
    ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hq, show 2 * ↑Real.pi * Complex.I * ((((b : ℚ) + p * m) / p : ℚ) : ℂ) =
      2 * Real.pi * Complex.I * b / (p : ℂ) + m * (2 * Real.pi * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end GlobalTheory.StdCharDegOne
