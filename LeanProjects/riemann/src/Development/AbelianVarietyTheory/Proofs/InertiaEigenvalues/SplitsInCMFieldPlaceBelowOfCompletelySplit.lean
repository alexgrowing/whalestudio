import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.SplitBelow

theorem ef_eq_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hm : (p : 𝓞 E) ∈ P)
    (hN : Ideal.absNorm P = p) : P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = 1 := by

  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmZ : ((p : ℤ) : 𝓞 E) ∈ P := by simpa using hm
  have hU : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpZ).mp hd P hP hmZ
  have he : P.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one P ℤ
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpZ).mpr hmZ
  have hf : P.inertiaDeg ℤ = 1 := by
    have h := Ideal.pow_inertiaDeg p P
    rw [hN] at h
    exact Nat.pow_right_injective hp.two_le (by simpa using h)
  have het := Ideal.ramificationIdx_tower (R := ℤ) (P.under (𝓞 F)) P
  have hft := Ideal.inertiaDeg_tower (R := ℤ) (P.under (𝓞 F)) P
  rw [he] at het
  rw [hf] at hft
  rw [(mul_eq_one.mp het.symm).2, (mul_eq_one.mp hft.symm).2]
  exact mul_one 1

theorem splits_below_of_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ discr E → (∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) → ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Splits (below P) := by

  intro E _ _ _ p hp hd hN P hPm
  classical
  by_contra hns
  have hO : ∀ Q : HeightOneSpectrum (𝓞 E), GlobalTheory.CMVal.Over Q (below P) → Q = P := by
    intro Q hQ
    by_contra hne
    exact hns ⟨Q, P, hne, hQ, over_below P⟩
  have hq1 : ∀ q : (below P).asIdeal.primesOver (𝓞 E), q.1 = P.asIdeal := by
    intro q
    have hq := q.2
    have := hq.1
    have := hq.2
    have hne : q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (below P).ne_bot q.1
    have h := hO ⟨q.1, hq.1, hne⟩ (Ideal.LiesOver.over (P := q.1) (p := (below P).asIdeal)).symm
    exact congrArg HeightOneSpectrum.asIdeal h
  have hterm : ∀ q : (below P).asIdeal.primesOver (𝓞 E),
      q.1.ramificationIdx (OF E) * q.1.inertiaDeg (OF E) = 1 := by
    intro q
    rw [hq1 q]
    have := P.isPrime
    exact ef_eq_one (maximalRealSubfield E) E hp hd P.asIdeal hPm (hN P hPm)
  have hfr : Module.finrank (OF E) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (OF E) (maximalRealSubfield E) (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (below P).asIdeal (𝓞 E)
  rw [Finset.sum_congr rfl (fun q _ => hterm q), hfr] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  have hle : Fintype.card ((below P).asIdeal.primesOver (𝓞 E)) ≤ 1 :=
    Fintype.card_le_one_iff.mpr (fun a b => Subtype.ext ((hq1 a).trans (hq1 b).symm))
  omega

end GlobalTheory.LamTie.SplitBelow
