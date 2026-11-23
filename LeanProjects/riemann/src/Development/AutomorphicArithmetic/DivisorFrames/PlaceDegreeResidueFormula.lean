import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OrdFracEqValuationInvOfIsLocalization
open IsLocalRing NumberField IsDedekindDomain GlobalTheory.ValCount GlobalTheory.VertCmp
open scoped Classical

private theorem isLoc_of_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (A : ValuationSubring F) [Algebra (𝓞 F) A] [IsScalarTower (𝓞 F) A F]
    (h : ∀ x : 𝓞 F, x ∈ v.asIdeal ↔ algebraMap (𝓞 F) A x ∈ maximalIdeal A) :
    IsLocalization.AtPrime A v.asIdeal := by
  have hc : ∀ a, ((algebraMap (𝓞 F) A a : A) : F) = algebraMap (𝓞 F) F a := fun a =>
    (IsScalarTower.algebraMap_apply (𝓞 F) A F a).symm
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨fun y => IsLocalRing.notMem_maximalIdeal.1 fun hy => y.2 ((h _).2 hy), fun o => ?_, fun {a c} hac => ⟨1, ?_⟩⟩
  · by_cases e0 : (o : F) = 0
    · exact ⟨⟨0, 1⟩, by rw [show o = 0 from Subtype.ext e0]; simp⟩
    have hS := v.asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime F) :=
      Localization.subalgebra.isLocalization_ofField F _ hS
    rcases (v.valuationSubringAtPrime F).mem_or_inv_mem (o : F) with h' | h'
    · obtain ⟨⟨r, s⟩, hh⟩ := IsLocalization.surj v.asIdeal.primeCompl (⟨o, h'⟩ : v.valuationSubringAtPrime F)
      have h2 : (o : F) * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F r := congrArg Subtype.val hh
      exact ⟨⟨r, s⟩, Subtype.ext (by rw [MulMemClass.coe_mul, hc, hc]; exact h2)⟩
    · obtain ⟨⟨r, s⟩, hh⟩ := IsLocalization.surj v.asIdeal.primeCompl (⟨(o : F)⁻¹, h'⟩ : v.valuationSubringAtPrime F)
      have h2 : (o : F)⁻¹ * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F r := congrArg Subtype.val hh
      have h3 : o * algebraMap (𝓞 F) A r = algebraMap (𝓞 F) A s := Subtype.ext (by
        rw [MulMemClass.coe_mul, hc, hc, ← h2, ← mul_assoc, mul_inv_cancel₀ e0, one_mul])
      refine ⟨⟨s, ⟨r, fun hr => s.2 ?_⟩⟩, h3⟩
      refine (h _).2 ?_
      rw [← h3]
      exact Ideal.mul_mem_left _ _ ((h _).1 hr)
  · have h2 : algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F c := by rw [← hc, ← hc, hac]
    rw [IsFractionRing.injective (𝓞 F) F h2]

private theorem ramIdx_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (p : ℕ)
    (hp : p.Prime) (hv : (p : 𝓞 F) ∈ v.asIdeal) :
    ((v.asIdeal.ramificationIdx ℤ : ℕ) : ℤ) = -WithZero.log (v.valuation F (p : F)) := by
  have hP := v.isPrime
  have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal hpr h0
  have hl : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hv
  have hm : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : 𝓞 F)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hm0 : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by simpa using hp.ne_zero
  have hp0 : (p : 𝓞 F) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(p : ℤ)}) _ (hm ▸ hm0), hm,
    ← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap,
    v.intValuation_eq_exp_neg_multiplicity hp0, WithZero.log_exp, neg_neg]

theorem UpperTheory.place_degree_residue_formula :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime], (p : 𝓞 F) ∈ v.asIdeal → ∀ (F' : Type) [Field F'] [NumberField F'] (ε : F →+* F') (O : ValuationSubring F') [IsDiscreteValuationRing O] [CharP (ResidueField O) p] (b : 𝓞 F →+* O), IsUp v ε O b → IsDiscreteValuationRing (O.comap ε) ∧ placeDeg p v * (vdeg ε O : ℝ) = (vord (O.comap ε) (p : F) : ℝ) * (resDeg O p : ℝ) := by
  intro F _ _ v p hp hv F' _ _ ε O _ _ b hup
  have hmem : ∀ a : 𝓞 F, algebraMap (𝓞 F) F a ∈ O.comap ε := fun a => by
    rw [ValuationSubring.mem_comap]
    have := (b a).2
    rwa [hup.1 a] at this
  letI : Algebra (𝓞 F) (O.comap ε) := ((algebraMap (𝓞 F) F).codRestrict (O.comap ε) hmem).toAlgebra
  haveI : IsScalarTower (𝓞 F) (O.comap ε) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmax : ∀ x : 𝓞 F, x ∈ v.asIdeal ↔ algebraMap (𝓞 F) (O.comap ε) x ∈ maximalIdeal (O.comap ε) := fun x => by
    rw [hup.2 x, ← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff,
      mem_nonunits_comap, hup.1 x]
    rfl
  haveI := v.isPrime
  haveI := v.isMaximal
  haveI hloc := isLoc_of_mem v (O.comap ε) hmax
  haveI hdvr : IsDiscreteValuationRing (O.comap ε) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) v.ne_bot _
  refine ⟨hdvr, ?_⟩
  have h1 : vord (O.comap ε) (p : F) = (v.asIdeal.ramificationIdx ℤ : ℕ) := by
    rw [vord_eq, GlobalTheory.ExtField.log_ordFrac_eq_neg_log_valuation v (O.comap ε), ramIdx_eq v p hp.out hv]
  haveI : CharP (ResidueField (O.comap ε)) p :=
    (ResidueField.map (vres ε O)).charP (ResidueField.map (vres ε O)).injective p
  have hcard : Nat.card (ResidueField (O.comap ε)) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal (O.comap ε)).toEquiv).symm
  haveI : Finite (ResidueField (O.comap ε)) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  letI := ZMod.algebra (ResidueField O) p
  letI := ZMod.algebra (ResidueField (O.comap ε)) p
  letI := (ResidueField.map (vres ε O)).toAlgebra
  haveI : IsScalarTower (ZMod p) (ResidueField (O.comap ε)) (ResidueField O) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have h2 : Module.finrank (ZMod p) (ResidueField (O.comap ε)) * vdeg ε O = resDeg O p :=
    Module.finrank_mul_finrank (ZMod p) (ResidueField (O.comap ε)) (ResidueField O)
  have h3 : Ideal.absNorm v.asIdeal = p ^ Module.finrank (ZMod p) (ResidueField (O.comap ε)) := by
    rw [← hcard, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have h4 : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  rw [h1, ← h2, placeDeg, h3]
  unfold Formalism.BasicNotions.eWL
  push_cast
  rw [Real.log_pow]
  field_simp
