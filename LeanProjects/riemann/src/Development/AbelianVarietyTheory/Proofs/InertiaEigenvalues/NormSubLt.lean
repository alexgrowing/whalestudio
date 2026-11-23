import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff

noncomputable section
namespace GlobalTheory.WildMove
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws
open scoped Formalism.Per

private theorem charP_closedBallSubring_quotient_openBallIdeal {l : ℕ} [hl : Fact l.Prime] :
    CharP (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸ GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) l := by
  have hM := GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal (PadicAlgCl l)
  have : (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)).IsPrime := hM.isPrime
  refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
  have e : ((l : PadicAlgCl l)) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := (map_natCast _ l).symm
  push_cast
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem exists_norm_pow_prime_pow_sub_lt_one {l : ℕ} [hl : Fact l.Prime] (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) :
    ∃ f : ℕ, 0 < f ∧ ‖a ^ (l ^ f) - a‖ < 1 := by
  classical
  have : NeZero l := ⟨hl.out.ne_zero⟩
  set O := GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) with hO
  set M := GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l) with hM
  have : M.IsMaximal := GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal _
  let : Field (O ⧸ M) := Ideal.Quotient.field M
  have : CharP (O ⧸ M) l := charP_closedBallSubring_quotient_openBallIdeal
  let : Algebra (ZMod l) (O ⧸ M) := ZMod.algebra _ l

  have hcoef : ∀ c : ℚ_[l], ‖c‖ ≤ 1 → ∀ h : algebraMap ℚ_[l] (PadicAlgCl l) c ∈ O,
      Ideal.Quotient.mk M ⟨_, h⟩ ∈ Set.range (algebraMap (ZMod l) (O ⧸ M)) := by
    intro c hc h
    have key : ∀ x : ℤ_[l], ∃ n : ℕ, ‖(x : ℚ_[l]) - n‖ < 1 := by
      intro x
      obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := x)
      rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def, PadicInt.coe_sub,
        PadicInt.coe_natCast] at hn
      exact ⟨n, hn⟩
    obtain ⟨n, hn'⟩ := key ⟨c, hc⟩
    refine ⟨(n : ZMod l), ?_⟩
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
    have e : ((n : PadicAlgCl l)) = algebraMap ℚ_[l] (PadicAlgCl l) (n : ℚ_[l]) := (map_natCast _ n).symm
    push_cast
    rw [e, ← map_sub, PadicAlgCl.norm_extends, norm_sub_rev]
    exact hn'

  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  set P := minpoly ℚ_[l] a with hP
  have hPm : P.Monic := minpoly.monic hint
  have hPc : ∀ n, ‖P.coeff n‖ ≤ 1 := by
    have h1 : spectralValue P ≤ 1 := by
      rw [← PadicAlgCl.spectralNorm_eq] at ha
      exact ha
    exact (spectralValue_le_one_iff hPm).1 h1
  set Pm := P.map (algebraMap ℚ_[l] (PadicAlgCl l)) with hPm'
  have hPmO : ∀ n, Pm.coeff n ∈ O := by
    intro n
    rw [Polynomial.coeff_map, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring, PadicAlgCl.norm_extends]
    exact hPc n
  have hsub : (↑Pm.coeffs : Set (PadicAlgCl l)) ⊆ O := by
    intro x hx
    obtain ⟨n, -, hn⟩ := Polynomial.mem_coeffs_iff.1 hx
    rw [hn]
    exact hPmO n
  set Q := Pm.toSubring O hsub with hQ
  set Qb := Q.map (Ideal.Quotient.mk M) with hQb
  have hQm : Qb.Monic := ((Polynomial.monic_toSubring _ _ _).2 (hPm.map _)).map _
  have hlift : Qb ∈ Polynomial.lifts (algebraMap (ZMod l) (O ⧸ M)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hQb, Polynomial.coeff_map]
    have e : Q.coeff n = ⟨algebraMap ℚ_[l] (PadicAlgCl l) (P.coeff n), by
        rw [← Polynomial.coeff_map]; exact hPmO n⟩ := by
      apply Subtype.ext
      rw [hQ, Polynomial.coeff_toSubring]
      exact Polynomial.coeff_map _ _
    rw [e]
    exact hcoef _ (hPc n) _
  set a' : O := ⟨a, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring.2 ha⟩ with ha'
  have hQa : Q.eval a' = 0 := by
    apply Subtype.ext
    show O.subtype (Q.eval a') = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hQ, Polynomial.map_toSubring]
    show Pm.eval a = 0
    rw [hPm', Polynomial.eval_map, ← Polynomial.aeval_def, hP, minpoly.aeval]
  have hroot : Qb.eval (Ideal.Quotient.mk M a') = 0 := by
    rw [hQb, Polynomial.eval_map, Polynomial.eval₂_at_apply, hQa, map_zero]
  obtain ⟨R, hRmap, -, hRmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hQm
  have hab : IsIntegral (ZMod l) (Ideal.Quotient.mk M a') :=
    ⟨R, hRmon, by rw [← Polynomial.eval_map, hRmap]; exact hroot⟩

  have := IntermediateField.adjoin.finiteDimensional hab
  have : Finite (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) :=
    Module.finite_of_finite (ZMod l)
  let : Fintype (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) =
      l ^ Module.finrank (ZMod l) (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) := by
    rw [Module.card_eq_pow_finrank (K := ZMod l), ZMod.card]
  have hx := FiniteField.pow_card (⟨Ideal.Quotient.mk M a', IntermediateField.mem_adjoin_simple_self _ _⟩ :
    IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})
  rw [hcard] at hx
  have hx' := congrArg Subtype.val hx
  simp only [SubmonoidClass.coe_pow] at hx'
  refine ⟨Module.finrank (ZMod l) (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank (ZMod l)
        (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})) with h0 | h0
    · have h1 := Fintype.one_lt_card (α := IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})
      rw [hcard, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h0
  · have h2 : Ideal.Quotient.mk M (a' ^ (l ^ Module.finrank (ZMod l)
        (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})) - a') = 0 := by
      rw [map_sub, map_pow, hx', sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal] at h2
    simpa [ha'] using h2

private theorem exists_teichmuller_root_norm_sub_lt_one {l : ℕ} [hl : Fact l.Prime] (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) :
    ∃ ζ : PadicAlgCl l, (ζ = 0 ∨ ∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) ∧ ‖a - ζ‖ < 1 := by
  classical
  obtain ⟨f, hf, hlt⟩ := exists_norm_pow_prime_pow_sub_lt_one a ha
  have hl1 : 1 < l := hl.out.one_lt
  have hq1 : 1 < l ^ f := Nat.one_lt_pow hf.ne' hl1
  set q := l ^ f with hq
  set P : Polynomial (PadicAlgCl l) := Polynomial.X ^ q - Polynomial.X with hP
  have hPm : P.Monic := Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq1)
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm
    IsAlgClosed.card_roots_eq_natDegree
  have heval : a ^ q - a = (P.roots.map fun r => a - r).prod := by
    have h := congrArg (Polynomial.eval a) hprod
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at h
    simpa [hP, Function.comp_def] using h.symm
  by_contra hcon
  push_neg at hcon
  have hge : ∀ r ∈ P.roots, 1 ≤ ‖a - r‖ := by
    intro r hr
    have hr' : r ^ q = r := by
      have h := Polynomial.isRoot_of_mem_roots hr
      simp only [Polynomial.IsRoot, hP, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at h
      exact sub_eq_zero.1 h
    by_cases h0 : r = 0
    · exact hcon r (Or.inl h0)
    · refine hcon r (Or.inr ⟨q - 1, by omega, ?_, ?_⟩)
      · intro hd
        have h2 : l ∣ q - 1 + 1 := by rw [Nat.sub_add_cancel hq1.le, hq]; exact dvd_pow_self l hf.ne'
        have h3 : l ∣ 1 := (Nat.dvd_add_right hd).1 h2
        exact hl1.ne' (Nat.dvd_one.1 h3)
      · have h4 : r ^ (q - 1) * r = 1 * r := by
          rw [← pow_succ, Nat.sub_add_cancel hq1.le, one_mul, hr']
        exact mul_right_cancel₀ h0 h4
  have key : ∀ s : Multiset (PadicAlgCl l), (∀ r ∈ s, 1 ≤ ‖a - r‖) →
      1 ≤ ‖(s.map fun r => a - r).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons r s ih =>
      intro h
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact one_le_mul_of_one_le_of_one_le (h r (Multiset.mem_cons.2 (Or.inl rfl)))
        (ih fun x hx => h x (Multiset.mem_cons.2 (Or.inr hx)))
  have h5 := key _ hge
  rw [← heval] at h5
  exact absurd hlt (not_lt.2 h5)

private theorem norm_apply_sub_lt_one_of_fixes_prime_to_l_roots {l : ℕ} [hl : Fact l.Prime] (γ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (hγ : ∀ ζ : PadicAlgCl l, (∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) → γ ζ = ζ)
    (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) : ‖γ a - a‖ < 1 := by
  obtain ⟨ζ, hζ, hlt⟩ := exists_teichmuller_root_norm_sub_lt_one a ha
  have hfix : γ ζ = ζ := by
    rcases hζ with h0 | h1
    · rw [h0, map_zero]
    · exact hγ ζ h1
  have e : γ a - a = γ (a - ζ) + -(a - ζ) := by rw [map_sub, hfix]; ring
  have hn : ‖γ (a - ζ)‖ = ‖a - ζ‖ := (spectralNorm_eq_of_equiv γ (a - ζ)).symm
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt ?_
  rw [hn, norm_neg, max_self]
  exact hlt

private theorem apply_root_eq_of_mem_fixingSubgroup_Kur {l : ℕ} [hl : Fact l.Prime] (γ : GQ l) (hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup) :
    ∀ ζ : PadicAlgCl l, (∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) → γ ζ = ζ := by
  intro ζ hζ
  have hmem : ζ ∈ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    exact IntermediateField.subset_adjoin _ _ hζ
  exact hγ ⟨ζ, hmem⟩

theorem norm_sub_lt (l : ℕ) [hl : Fact l.Prime] (γ : GQ l) (hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup)
    (n : ℕ) (x : Om l) (hx : x ≠ 0) (h : (γ ^ l ^ n) x = x) : ‖γ x - x‖ < ‖x‖ := by
  have hn : ∀ (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (y : PadicAlgCl l), ‖g y‖ = ‖y‖ :=
    fun g y => (spectralNorm_eq_of_equiv g y).symm
  have hfix := apply_root_eq_of_mem_fixingSubgroup_Kur γ hγ
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hγx : γ x ≠ 0 := by
    intro h0
    apply hx
    rw [← norm_eq_zero, ← hn γ x, h0, norm_zero]
  set u : Om l := γ x / x with hu'
  have hu : ‖u‖ = 1 := by rw [hu', norm_div, hn, div_self hx0]
  have hind : ∀ k : ℕ, ‖(γ ^ k) x / x - u ^ k‖ < 1 := by
    intro k
    induction k with
    | zero => simp [div_self hx]
    | succ k ih =>
      have hvk : ‖(γ ^ k) x / x‖ = 1 := by rw [norm_div, hn, div_self hx0]
      have e : (γ ^ (k + 1)) x / x - u ^ (k + 1) =
          ((γ ((γ ^ k) x / x) - (γ ^ k) x / x) + ((γ ^ k) x / x - u ^ k)) * u := by
        rw [show γ ^ (k + 1) = γ * γ ^ k from pow_succ' γ k, AlgEquiv.mul_apply, pow_succ u k, map_div₀, hu']
        field_simp
        ring
      rw [e, norm_mul, hu, mul_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (norm_apply_sub_lt_one_of_fixes_prime_to_l_roots γ hfix _ hvk.le) ih)
  have hq : ‖u ^ (l ^ n) - 1‖ < 1 := by
    have h1 := hind (l ^ n)
    rw [h, div_self hx, norm_sub_rev] at h1
    exact h1
  have hM : (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)).IsMaximal :=
    GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal _
  let : Field (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸ GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) :=
    Ideal.Quotient.field _
  have : CharP (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸
    GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) l := charP_closedBallSubring_quotient_openBallIdeal
  set u' : GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) :=
    ⟨u, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring.2 hu.le⟩ with hu''
  have h1 : (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) u') ^ (l ^ n) = 1 := by
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l))),
      Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
    simpa [hu''] using hq
  have h2 : (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) u' - 1) ^ (l ^ n) = 0 := by
    rw [sub_pow_char_pow, h1, one_pow, sub_self]
  have h3 := pow_eq_zero_iff (pow_ne_zero n hl.out.ne_zero) |>.1 h2
  rw [sub_eq_zero, ← map_one (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l))),
    Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal] at h3
  have h4 : ‖u - 1‖ < 1 := by simpa [hu''] using h3
  have e : γ x - x = x * (u - 1) := by
    rw [mul_sub, mul_one, hu', mul_div_assoc', mul_comm x (γ x), mul_div_assoc, div_self hx, mul_one]
  rw [e, norm_mul]
  exact mul_lt_of_lt_one_right (norm_pos_iff.2 hx) h4

end GlobalTheory.WildMove
