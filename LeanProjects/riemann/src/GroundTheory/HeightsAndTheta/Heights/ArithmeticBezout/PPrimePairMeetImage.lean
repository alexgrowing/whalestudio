import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPrimePairMeetImage
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFiniteFibresDimLe
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImageDimLe
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBadSetSmaller
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.HeightCoheightQuotient
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem PrimePairMeetImage.projHom_not_injective (hF : FiniteFibresDimLe.Statement) {n d : ℕ}
    {Q Q' P : Ideal (MvPolynomial (Fin n) ℂ)} (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hQ' : Q'.IsPrime) (hne : Q ≠ Q') (hfin : ∀ y, (ComplexSets.fibre Q A y).Finite)
    (hfin' : ∀ y, (ComplexSets.fibre Q' A y).Finite) (hP : P.IsPrime) (hle : Q ⊔ Q' ≤ P) :
    ¬ Function.Injective (ComplexSets.projHom P A) := by
  intro hinj
  obtain ⟨R, hR, hRfin, hlt⟩ :
      ∃ R : Ideal (MvPolynomial (Fin n) ℂ), R.IsPrime ∧ (∀ y, (ComplexSets.fibre R A y).Finite) ∧ R < P := by
    by_cases h : Q = P
    · refine ⟨Q', hQ', hfin', lt_of_le_of_ne (le_sup_right.trans hle) ?_⟩
      intro h'
      exact hne (h.trans h'.symm)
    · exact ⟨Q, hQ, hfin, lt_of_le_of_ne (le_sup_left.trans hle) h⟩

  have hlow : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by
    have h := ImageDimLe.proof n d P (ComplexSets.linPoly A) hP
    have hker : RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval (ComplexSets.linPoly A))) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 hinj
    rw [hker, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simpa using h

  have hup := hF n d R A hR hRfin
  have hdrop := Order.coheight_add_one_le (a := (⟨P, hP⟩ : PrimeSpectrum (MvPolynomial (Fin n) ℂ)))
    (b := ⟨R, hR⟩) hlt
  rw [ringKrullDim_quotient_eq_coheight] at hlow hup
  have h1 : ((d : ℕ) : ℕ∞) ≤ Order.coheight (⟨P, hP⟩ : PrimeSpectrum (MvPolynomial (Fin n) ℂ)) := by
    exact_mod_cast hlow
  have h2 : Order.coheight (⟨R, hR⟩ : PrimeSpectrum (MvPolynomial (Fin n) ℂ)) ≤ ((d : ℕ) : ℕ∞) := by
    exact_mod_cast hup
  have h3 := (add_le_add h1 (le_refl (1 : ℕ∞))).trans (hdrop.trans h2)
  exact lt_irrefl _ ((ENat.add_one_le_iff (ENat.natCast_ne_top d)).1 h3)

theorem PrimePairMeetImage.proof (hF : FiniteFibresDimLe.Statement) : PrimePairMeetImage.Statement := by
  classical
  intro n d Q Q' A hQ hQ' hne hfin hfin'
  have hker : ∀ P ∈ (Q ⊔ Q').minimalPrimes,
      ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧ ComplexSets.pullback A e ∈ P := by
    intro P hPm
    have hni := PrimePairMeetImage.projHom_not_injective hF A hQ hQ' hne hfin hfin' hPm.1.1 hPm.1.2
    rw [injective_iff_map_eq_zero] at hni
    obtain ⟨e, he0, hne0⟩ : ∃ e, ComplexSets.projHom P A e = 0 ∧ e ≠ 0 := by
      by_contra hc
      exact hni fun e he => by_contra fun h => hc ⟨e, he, h⟩
    exact ⟨e, hne0, Ideal.Quotient.eq_zero_iff_mem.1 he0⟩
  choose! f hf0 hfP using hker
  have hfs := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) (Q ⊔ Q')
  refine ⟨∏ P ∈ hfs.toFinset, f P,
    Finset.prod_ne_zero_iff.2 fun P hP => hf0 P (hfs.mem_toFinset.1 hP), ?_⟩
  rintro x ⟨hx, hx'⟩
  have hmx : Q ⊔ Q' ≤ RingHom.ker (eval x) :=
    sup_le (fun q hq => RingHom.mem_ker.2 (hx q hq)) (fun q hq => RingHom.mem_ker.2 (hx' q hq))
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hmx
  have hPs : P ∈ hfs.toFinset := hfs.mem_toFinset.2 hP
  have hmem : ComplexSets.pullback A (∏ P ∈ hfs.toFinset, f P) ∈ P := by
    rw [← Finset.prod_erase_mul _ _ hPs, map_mul]
    exact P.mul_mem_left _ (hfP P hP)
  rw [← ComplexSets.eval_pullback]
  exact RingHom.mem_ker.1 (hPle hmem)

end GroundTheory.Heights₂.Heights
