import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.CycIne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem unrJ_prime (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal := by
  have := w.isPrime
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  refine ⟨ringChar (𝓞 L ⧸ w.asIdeal), CharP.char_is_prime (𝓞 L ⧸ w.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact (ringChar.spec _ _).2 dvd_rfl

private theorem unrJ_arith (f n p : ℕ) (hp : p.Prime) (hf : Odd f) (h1 : 1 < f) (hn : 2 ≤ n) :
    ¬ (f * 2 ^ n - 1 ≡ 1 [MOD ordCompl[p] (f * 2 ^ n)]) := by
  intro h
  have hM : f * 2 ^ n ≠ 0 := by positivity
  have hd : ordCompl[p] (f * 2 ^ n) ∣ 2 := by
    have h2 := h.add_right 1
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hM)] at h2
    exact (h2.dvd_iff dvd_rfl).1 (Nat.ordCompl_dvd _ _)
  have key : ∀ d : ℕ, d ∣ f * 2 ^ n → ¬ p ∣ d → d ∣ 2 := fun d hd1 hd2 =>
    (Nat.dvd_ordCompl_of_dvd_not_dvd hd1 hd2).trans hd
  by_cases h2 : p = 2
  · subst h2
    have h3 := Nat.le_of_dvd two_pos (key f (dvd_mul_right _ _) hf.not_two_dvd_nat)
    obtain ⟨k, rfl⟩ := hf
    omega
  · have h4 : 2 ^ 2 ∣ f * 2 ^ n := (pow_dvd_pow 2 hn).mul_left f
    have h3 := key _ h4 fun h5 => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h5))
    omega

private theorem unrJ_conj (L : Type) [Field L] [NumberField L] [IsCMField L] (M : ℕ) (hM : M ≠ 0) (ζ : L)
    (hζ : ζ ^ M = 1) : IsCMField.complexConj L ζ = ζ ^ (M - 1) := by
  let φ : L →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h1 : (φ ζ) ^ M = 1 := by rw [← map_pow, hζ, map_one]
  have h2 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 hM
  rw [IsCMField.complexEmbedding_complexConj, map_pow, ← Complex.inv_eq_conj h2]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hM), h1]

theorem UpperTheory.V.FW.unrJ :
    ∀ (f n : ℕ) [NeZero (f * 2 ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * 2 ^ n} ℚ L] [IsCMField L], Odd f → 1 < f → 2 ≤ n → UnrFin L := by
  intro f n _ L _ _ _ _ hf h1 hn w
  rw [← UpperTheory.V.CF.ineCard.1 (maximalRealSubfield L) L w, Subgroup.card_eq_one, eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  by_contra hne
  have hc : Nat.card Gal(L/maximalRealSubfield L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hτc : τ = IsCMField.complexConj L :=
    ((Nat.card_eq_two_iff' 1).1 hc).unique hne (IsCMField.complexConj_ne_one L)
  subst hτc
  obtain ⟨p, hp, hw⟩ := unrJ_prime L w
  have hζ := IsCyclotomicExtension.zeta_spec (f * 2 ^ n) ℚ L
  have h := (UpperTheory.V.CF.cycIne (f * 2 ^ n) L _ p hp hζ w hw
    (UpperTheory.V.CF.relIncl ℚ (maximalRealSubfield L) L (IsCMField.complexConj L)) (f * 2 ^ n - 1)
    (unrJ_conj L _ (NeZero.ne _) _ hζ.pow_eq_one)).1.1 (fun z => hτ z)
  exact unrJ_arith f n p hp hf h1 hn h
