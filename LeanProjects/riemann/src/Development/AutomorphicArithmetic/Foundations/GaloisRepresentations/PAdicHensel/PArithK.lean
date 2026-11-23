import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateSqrtNeg
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

private lemma conj_sqrt_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (d : ℕ) (x : E)
    (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : IsCMField.complexConj E x = -x :=
  _root_.UpperTheory.Reformulated.B.ConjugateSqrtNeg.conj_sqrt_neg d x hd hx

private lemma omega_at {E : Type} [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) (d : ℕ) (x : E)
    (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (tr nm : ℤ) (f : ℚ)
    (hdisc : ((tr ^ 2 - 4 * nm : ℤ) : ℚ) = f ^ 2 * (-(d : ℚ))) :
    ∃ ω : 𝓞 E, ω + bar ω = (tr : 𝓞 E) ∧ ω * bar ω = (nm : 𝓞 E) ∧
      2 * (ω : E) - (tr : E) = (f : E) * x := by
  have hcx := conj_sqrt_neg d x hd hx
  have hdiscE : ((tr : E) ^ 2 - 4 * (nm : E)) = (f : E) ^ 2 * (-(d : E)) := by
    have := congrArg (algebraMap ℚ E) hdisc
    simpa using this
  obtain ⟨w, hw⟩ : ∃ w : E, w = ((tr : E) + (f : E) * x) / 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : E, v = ((tr : E) - (f : E) * x) / 2 := ⟨_, rfl⟩
  have hcw : IsCMField.complexConj E w = v := by
    simp only [hw, hv, map_div₀, map_add, map_mul, map_intCast, map_ratCast, hcx, map_ofNat]
    ring
  have hsum : w + v = (tr : E) := by
    rw [hw, hv]; ring
  have hprod : w * v = (nm : E) := by
    have h : w * v = ((tr : E) ^ 2 - (f : E) ^ 2 * x ^ 2) / 4 := by
      rw [hw, hv]; ring
    rw [h, hx]
    linear_combination (1 / 4 : E) * hdiscE
  have hroot : w ^ 2 - (tr : E) * w + (nm : E) = 0 := by
    rw [← hsum, ← hprod]; ring
  have hint : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + (Polynomial.C (-tr) * Polynomial.X + Polynomial.C nm), ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add ?_
      exact lt_of_le_of_lt (Polynomial.degree_linear_le) (by norm_num)
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      simp only [eq_intCast, Int.cast_neg]
      linear_combination hroot
  obtain ⟨ω, hω⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp hint
  have hω' : (ω : E) = w := hω
  have hbω : ((bar ω : 𝓞 E) : E) = v := by rw [hbar, hω', hcw]
  refine ⟨ω, ?_, ?_, ?_⟩
  · apply RingOfIntegers.ext
    simp only [map_add, map_intCast, hω', hbω, hsum]
  · apply RingOfIntegers.ext
    simp only [map_mul, map_intCast, hω', hbω, hprod]
  · rw [hω', hw]; ring

theorem UpperTheory.Gal.G1.pArithK :
    BarEx → QuadEx → CEx → UnitMod → CodiffGen → CodiffUnit → IdemEx → RealGen → PosGen → DeltaEx → PerfOf → ArithK := by
  intro hBar hQuad hC hUnit _ _ hIdem hReal hPos hDelta hPerf E _ _ _ d hd x hx τ₀ Q hQ
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ∏ q ∈ Q, q := ⟨_, rfl⟩
  have hprime : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1.out
  have hM : 0 < M := by
    rw [hMdef]
    exact Finset.prod_pos fun q hq => (hprime q hq).pos
  have hmem : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ Q := by
    intro q hq hqM
    rw [hMdef] at hqM
    obtain ⟨a, ha, hqa⟩ := (Prime.dvd_finset_prod_iff hq.prime _).1 hqM
    rwa [(Nat.prime_dvd_prime_iff_eq hq (hprime a ha)).1 hqa]
  obtain ⟨bar, hbar⟩ := hBar E
  obtain ⟨tr, nm, f, hneg, hdisc, hsplit⟩ := hQuad d hd
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h0 : ((tr ^ 2 - 4 * nm : ℤ) : ℚ) = 0 := by rw [hdisc]; ring
    have h1 : tr ^ 2 - 4 * nm = 0 := by exact_mod_cast h0
    omega
  obtain ⟨ω, htr, hnm, hωx⟩ := omega_at bar hbar d x hd hx tr nm f hdisc
  obtain ⟨c, hc1, hc2, hc3, b, hb⟩ := hC E τ₀ M hM
  have hbb : ∀ y, bar (bar y) = y := by
    intro y
    apply Subtype.ext
    show ((bar (bar y) : 𝓞 E) : E) = (y : E)
    rw [hbar, hbar, IsCMField.complexConj_apply_apply]
  have hsp : ∀ q ∈ Q, ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm := by
    intro q hq
    obtain ⟨hF, hs⟩ := hQ q hq
    exact hsplit q hs
  obtain ⟨ε, hε⟩ := hIdem E bar ω tr nm hbb htr hnm M hM
    (fun q hq hqM => hsp q (hmem q hq hqM))
  obtain ⟨t, ht1, ht2⟩ := hReal E bar hbar M hM ε hε
  obtain ⟨t', ht1', ht2', ht3'⟩ := hPos E M hM t ht1 ht2
  have hcop : IsCoprime (tr ^ 2 - 4 * nm) (M : ℤ) := by
    rw [hMdef, Nat.cast_prod]
    refine IsCoprime.prod_right fun q hq => ?_
    exact ((Nat.prime_iff_prime_int.1 (hprime q hq)).coprime_iff_not_dvd.2 (hsp q hq).1).symm
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := hDelta E bar hbar ω tr nm htr hnm hneg M hcop t' ht1' ht2' ht3' τ₀
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc2
  let A : Arith E :=
    { bar := bar, bar_eq := hbar, ω := ω, tr := tr, nm := nm, tr_eq := htr, nm_eq := hnm, disc_neg := hneg,
      τ₀ := τ₀, c := c, c_real := Subtype.ext ((hbar c).trans hc1), c_neg := hc2, c_pos := hc3,
      δ := δ, δ_im := hδ1, δ_int := hδ2.1, δ_sign := hδ3 }
  refine ⟨A, rfl, ⟨f, hf0, hωx⟩, fun q _ hq => hsplit q hq, fun q hq => ⟨hsp q hq, ?_⟩⟩
  have hdvd : q ∣ M := by
    rw [hMdef]
    exact Finset.dvd_prod_of_mem _ hq
  exact hPerf E A M hδ2 (hUnit E M c b hc0 hb) q hdvd
