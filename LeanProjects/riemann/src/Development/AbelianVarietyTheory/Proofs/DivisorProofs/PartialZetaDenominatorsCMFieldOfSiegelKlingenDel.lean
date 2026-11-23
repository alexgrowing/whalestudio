import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesMinPadicValBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesExponentLogSumLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionMulPrimeWideIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionTopWideIndicatorIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimesOverPrimeCoprimalityEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatInPadicIntegersOfTwistedDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorExponentLeOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinPadicValPowSubOneCoprimeEqClosedFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenomSumBoundOfLocalBoundsStatement

noncomputable section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom

theorem eulerStep {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)) (hmax : 𝔭.IsMaximal) (hp : 𝔭 ≠ ⊥) (hcop : 𝔭 ⊔ 𝔪 = ⊤)
    (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ) (hZ : IsRayL 𝔪 (wideInd C) Z) (hZ' : IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z') :
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) :=
  GlobalTheory.T.isNarrowRayClassLFunction_mul_prime_wideIndicator 𝔪 𝔭 hmax hp hcop C Z Z' hZ hZ'

theorem isRayL_top_iff {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) :
    IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z :=
  GlobalTheory.T.isNarrowRayClassLFunction_top_wideIndicator_iff C Z

theorem primesOver_exists {F : Type} [Field F] [NumberField F] (l : ℕ) (hl : l.Prime) :
    ∃ P : Finset (Ideal (𝓞 F)), (∀ 𝔭 ∈ P, 𝔭.IsMaximal ∧ 𝔭 ≠ ⊥ ∧ l ∣ Ideal.absNorm 𝔭) ∧
      ∀ I : Ideal (𝓞 F), CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔ CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I :=
  GlobalTheory.T.exists_finite_primes_over_prime_coprimality_equiv l hl

theorem inZl_of_shift {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime] (g : G) (q : ℕ) (hq : l ∣ q)
    (x : G → ℚ) (h : ∀ C, InZl l (x C - (q : ℚ) * x (C * g))) (C : G) : InZl l (x C) :=
  GlobalTheory.T.isRatInPadicIntegers_of_twisted_difference l g q hq x h C

theorem cE_le_of_inZl {F : Type} [Field F] [NumberField F] (z : ClassGroup (𝓞 F) → ℚ) (l a n : ℕ) [Fact l.Prime]
    (ha : 2 ≤ a) (hn : 1 ≤ n) (h : ∀ C, InZl l (((a ^ n - 1 : ℕ) : ℚ) * z C)) :
    cE z l ≤ finrank ℚ F * padicValNat l 2 + padicValNat l (a ^ n - 1) :=
  GlobalTheory.T.partialZetaDenominatorExponent_le_of_integral z l a n ha hn h

theorem mMin_eq_mE (hmin : Formalism.PairingDivisionLocalBalance.MinVal) (l n : ℕ) (hl : l.Prime) (hn : 2 ≤ n) (he : Even n) :
    mMin l n = Formalism.PairingDivisionLocalBalance.mE l n :=
  GlobalTheory.T.minPadicValPowSubOneCoprime_eq_closedFormula hmin l n hl hn he

theorem sumBound_of_local {F : Type} [Field F] [NumberField F] (hsum : Formalism.PairingDivisionLocalBalance.CESum) (k : ℕ)
    (z : ClassGroup (𝓞 F) → ℚ) (hk : 2 ≤ k) (h16 : 16 ≤ finrank ℚ F * k)
    (h : ∀ l : ℕ, l.Prime → cE z l ≤ finrank ℚ F * padicValNat l 2 + Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k)) : SumBound k z :=
  GlobalTheory.T.partialZetaDenomSumBound_of_local_bounds hsum k z hk h16 h

theorem isRayL_of_coprime_iff {F : Type} [Field F] [NumberField F] {𝔣 𝔤 : Ideal (𝓞 F)}
    (h : ∀ I, CoprimeTo F 𝔣 I ↔ CoprimeTo F 𝔤 I) {ε : Ideal (𝓞 F) → ℚ} {L : ℂ → ℂ} (hL : IsRayL 𝔣 ε L) : IsRayL 𝔤 ε L :=
  ⟨hL.1, fun s hs => (Equiv.subtypeEquivRight fun I => (h I).symm).hasSum_iff
    (f := fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} => (ε I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) |>.2 (hL.2 s hs)⟩

theorem exists_isZetaValues (h : GlobalTheory.Published.SiegelKlingen) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ)
    (hk : 1 ≤ k) : ∃ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z := by
  have : ∀ C : ClassGroup (𝓞 F), ∃ r : ℚ, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (r : ℂ) := by
    intro C
    obtain ⟨L, hL, hv⟩ := h F ⊤ top_ne_bot (wideInd C) (isRayFun_wideInd _ C)
    obtain ⟨r, hr⟩ := hv k hk
    exact ⟨r, L, (isRayL_top_iff C L).1 hL, hr⟩
  choose z hz using this
  exact ⟨z, hz⟩

theorem inZl_mul_zeta (h : GlobalTheory.Published.DeligneRibet) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (l : ℕ) [hl : Fact l.Prime] (a k : ℕ) (ha : 2 ≤ a) (hac : a.Coprime l) (hk : 2 ≤ k)
    (z : ClassGroup (𝓞 F) → ℚ) (hz : IsZetaValues k z) (C : ClassGroup (𝓞 F)) :
    InZl l (((a ^ (finrank ℚ F * k) - 1 : ℕ) : ℚ) * z C) := by
  classical
  obtain ⟨P, hP, hPc⟩ := primesOver_exists (F := F) l hl.out
  set c : ℚ := ((a ^ (finrank ℚ F * k) - 1 : ℕ) : ℚ) with hcdef
  let St : Finset (Ideal (𝓞 F)) → Prop := fun T => ∀ x : ClassGroup (𝓞 F) → ℚ,
    (∀ C, ∃ Z : ℂ → ℂ, IsRayL (∏ 𝔭 ∈ T, 𝔭) (wideInd C) Z ∧ Z (1 - (k : ℂ)) = (x C : ℂ)) → ∀ C, InZl l (c * x C)

  have hfull : St P := by
    intro x hx C
    obtain ⟨Z, hZ, e⟩ := hx C
    have hZ1 : IsRayL (powMod F l 1) (wideInd C) Z :=
      isRayL_of_coprime_iff (fun I => by rw [hPc, coprimeTo_powMod_iff le_rfl]) hZ
    have ha0 : (a : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hcop : CoprimeTo F (powMod F l 1) (Ideal.span {(a : 𝓞 F)}) := by
      rw [coprimeTo_powMod_iff le_rfl]
      refine ⟨by simpa using ha0, ?_⟩
      rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
      simpa using (Nat.isCoprime_iff_coprime.2 hac).map (Int.castRingHom (𝓞 F))
    have hv : IsRayValue (powMod F l 1) (wideInd C) k (x C) := ⟨Z, hZ1, e⟩
    have hv' : IsRayValue (powMod F l 1) (translate (Ideal.span {(a : 𝓞 F)}) (wideInd C)) k (x C) := by
      rw [translate_wideInd ha0]; exact hv
    have hint : ∀ I, CoprimeTo F (powMod F l 1) I → InZl l (wideInd C I) := fun I _ => by
      unfold wideInd; split_ifs <;> simp [InZl]
    have := h F l 1 le_rfl (wideInd C) (isRayFun_wideInd _ C) hint _ hcop k (by omega) (x C) (x C) hv hv'
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at this
    have e2 : c * x C = -(x C - (((a ^ finrank ℚ F : ℕ) : ℚ)) ^ k * x C) := by
      rw [hcdef, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]; push_cast; ring
    rw [e2, inZl_iff, padicValRat.neg, ← inZl_iff]; exact this

  have step : ∀ (T : Finset (Ideal (𝓞 F))) (𝔭 : Ideal (𝓞 F)), 𝔭 ∉ T → 𝔭 ∈ P → T ⊆ P → St (insert 𝔭 T) → St T := by
    intro T 𝔭 h𝔭T h𝔭P hTP hSt x hx
    choose Zf hZf eZ using hx
    obtain ⟨hmax, hne, hdvd⟩ := hP 𝔭 h𝔭P
    have hcopT : 𝔭 ⊔ ∏ 𝔮 ∈ T, 𝔮 = ⊤ := by
      rw [← Ideal.isCoprime_iff_sup_eq]
      refine IsCoprime.prod_right fun 𝔮 h𝔮 => Ideal.isCoprime_iff_sup_eq.2 ?_
      exact Ideal.IsMaximal.coprime_of_ne hmax (hP 𝔮 (hTP h𝔮)).1 (fun e => h𝔭T (e ▸ h𝔮))
    set q : ℕ := Ideal.absNorm 𝔭 ^ (k - 1) with hqdef
    have hy : ∀ C, ∃ Z : ℂ → ℂ, IsRayL (∏ 𝔮 ∈ insert 𝔭 T, 𝔮) (wideInd C) Z ∧
        Z (1 - (k : ℂ)) = ((x C - (q : ℚ) * x (C * (cls 𝔭)⁻¹) : ℚ) : ℂ) := by
      intro C
      refine ⟨fun s => Zf C s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Zf (C * (cls 𝔭)⁻¹) s, ?_, ?_⟩
      · rw [Finset.prod_insert h𝔭T, mul_comm]
        exact eulerStep _ 𝔭 hmax hne hcopT C _ _ (hZf C) (hZf _)
      · have e1 : -(1 - (k : ℂ)) = ((k - 1 : ℕ) : ℂ) := by rw [Nat.cast_sub (by omega)]; push_cast; ring
        simp only [e1, Complex.cpow_natCast, eZ, hqdef]
        push_cast; ring
    have := hSt _ hy
    intro C
    have hmul := inZl_of_shift l ((cls 𝔭)⁻¹) q (dvd_pow hdvd (by omega)) (fun C => c * x C)
      (fun C => by have := this C; rwa [mul_sub, mul_left_comm] at this) C
    exact hmul
  have key : ∀ U : Finset (Ideal (𝓞 F)), U ⊆ P → St (P \ U) := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro _; simpa using hfull
    | insert 𝔭 U h𝔭U ih =>
      intro hU
      have h𝔭P : 𝔭 ∈ P := hU (Finset.mem_insert_self _ _)
      have ih := ih ((Finset.subset_insert _ _).trans hU)
      have e : P \ U = insert 𝔭 (P \ insert 𝔭 U) := by
        ext 𝔮; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩; by_cases h : 𝔮 = 𝔭 <;> simp_all
        · rintro (h | ⟨h1, h2⟩)
          · subst h; exact ⟨h𝔭P, h𝔭U⟩
          · exact ⟨h1, fun h => h2 (Or.inr h)⟩
      rw [e] at ih
      exact step _ 𝔭 (by simp) h𝔭P Finset.sdiff_subset ih
  have h0 := key P subset_rfl
  rw [Finset.sdiff_self] at h0
  refine h0 z (fun C => ?_) C
  obtain ⟨Z, hZ, e⟩ := hz C
  exact ⟨Z, by rw [Finset.prod_empty, Ideal.one_eq_top]; exact (isRayL_top_iff C Z).2 hZ, e⟩

theorem zetaDenominators (h : GlobalTheory.Published.SiegelKlingenDeligneRibet) : ZetaDenominators := by
  apply ZetaDenominatorsReal.cm
  intro F _ _ _ s hs
  have hf : 1 ≤ finrank ℚ F := (Module.finrank_pos : 0 < finrank ℚ F)
  have hn2 : 2 ≤ finrank ℚ F * (2 * s) := by nlinarith
  have hev : Even (finrank ℚ F * (2 * s)) := ⟨finrank ℚ F * s, by ring⟩
  have hloc : ∀ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues (2 * s) z → ∀ l : ℕ, l.Prime → LocalBound (2 * s) z l := by
    intro z hz l hl
    haveI := Fact.mk hl
    have hm := mMin_eq_mE GlobalTheory.T.dividedPowerValuations_minVal l _ hl hn2 hev
    obtain ⟨a, ha2, hac, hv⟩ := GlobalTheory.T.dividedPowerValuations_minVal l _ hl hn2 hev
    have hc := cE_le_of_inZl (F := F) z l a _ ha2 (by omega) (inZl_mul_zeta h.2 F l a (2 * s) ha2 hac (by omega) z hz)
    rw [hv] at hc
    refine ⟨by rw [hm]; exact hc, fun h2 hd => ?_, fun h2 hd => ?_, fun h2 => ?_⟩ <;> rw [hm] <;> simp [Formalism.PairingDivisionLocalBalance.mE, *]
  refine ⟨exists_isZetaValues h.1 F (2 * s) (by omega), fun z hz => ⟨hloc z hz, fun h16 =>
    sumBound_of_local GlobalTheory.T.cmValues_exponent_log_sum_le (2 * s) z (by omega) h16 fun l hl => ?_⟩⟩
  have h1 := hloc z hz l hl
  have h2 := h1.1
  rwa [h1.mMin_eq] at h2

end GlobalTheory.ZetaDenom
