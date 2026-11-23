import Formalism.SharpRestriction.SmoothDesignExistence.ClosedLinkSOfClosedPeriodAndFiltration
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Formalism.LocalToGlobal.GlobalTheory.GL2.ModEqOfNormOneMod

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk

noncomputable section

namespace Formalism.L2.SG.ResidEvFree

section

open Formalism.MainNotions.ShortIntervalPrimes Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

section Cyc

open NumberField Ideal

theorem not_dvd_of_mod {N p : ℕ} (hN : 0 < N) (hp : p.Prime) (h : p % N = 1 % N) : ¬ p ∣ N := by
  intro hd
  have hle : p ≤ N := Nat.le_of_dvd hN hd
  rcases Nat.lt_or_ge N 2 with h2 | h2
  · have := hp.two_le
    omega
  · have h1 : 1 % N = 1 := Nat.mod_eq_of_lt h2
    rcases Nat.lt_or_ge p N with hl | hl
    · rw [Nat.mod_eq_of_lt hl, h1] at h
      exact hp.one_lt.ne' h
    · have hpN : p = N := le_antisymm hle hl
      rw [hpN, Nat.mod_self, h1] at h
      exact absurd h (by norm_num)

theorem cycSplit (N p : ℕ) (K : Type) [Field K] [NumberField K] [Algebra K (CyclotomicField N ℚ)]
    (hN : 0 < N) (hp : p.Prime) (h : p % N = 1 % N) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = Module.finrank ℚ K := by
  have : NeZero N := ⟨hN.ne'⟩
  have hpF : Fact p.Prime := ⟨hp⟩
  have hm : ¬ p ∣ N := not_dvd_of_mod hN hp h
  have hord : orderOf (p : ZMod N) = 1 := by
    rw [orderOf_eq_one_iff]
    have := (ZMod.natCast_eq_natCast_iff' p 1 N).mpr h
    simpa using this
  have hCyc : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := by
    have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN.ne'⟩
    convert CyclotomicField.isCyclotomicExtension N ℚ
    · rfl
    · exact Subsingleton.elim _ _
  have hL : ∀ (Q : Ideal (𝓞 (CyclotomicField N ℚ))) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})],
      Q.ramificationIdx ℤ = 1 ∧ Q.inertiaDeg ℤ = 1 := by
    intro Q _ _
    exact ⟨IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p (CyclotomicField N ℚ) Q hm,
      (IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p (CyclotomicField N ℚ) Q hm).trans hord⟩
  have hK : ∀ P : (span {(p : ℤ)}).primesOver (𝓞 K), P.1.ramificationIdx ℤ = 1 ∧ P.1.inertiaDeg ℤ = 1 := by
    rintro ⟨P, hP1, hP2⟩
    obtain ⟨Q, hQ1, hQ2⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 (CyclotomicField N ℚ)))).some
    have : Q.LiesOver (span {(p : ℤ)}) := LiesOver.trans Q P _
    have he := ramificationIdx_tower (R := ℤ) P Q
    have hf := inertiaDeg_tower (R := ℤ) P Q
    obtain ⟨h1, h2⟩ := hL Q
    rw [h1] at he
    rw [h2] at hf
    exact ⟨Nat.eq_one_of_mul_eq_one_right he.symm, Nat.eq_one_of_mul_eq_one_right hf.symm⟩
  have : Fintype ((span {(p : ℤ)}).primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (span {(p : ℤ)})).fintype
  have hs := sum_ramification_inertia_eq_finrank (span {(p : ℤ)}) (𝓞 K)
  have hs1 : ∑ q : (span {(p : ℤ)}).primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ =
      ∑ _q : (span {(p : ℤ)}).primesOver (𝓞 K), 1 :=
    Finset.sum_congr rfl (fun q _ => by rw [(hK q).1, (hK q).2])
  rw [hs1, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at hs
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, hs, RingOfIntegers.rank]

theorem cycSplit_holds : CycSplit := fun N p K _ _ _ hN hp h => cycSplit N p K hN hp h

end Cyc

end

open Ideal NumberField IsDedekindDomain in

theorem splitsE_g (D : D7) (i : Fin 2) : S.SplitsCompl D.host.E (D.host.g i) := by
  have hp := D.host.g_prime i
  refine S.splitsCompl_of_ncard _ _ hp ?_
  have h := D.nd.g_split i
  have e := Formalism.MainNotions.J.ncard_places D.host.E (D.host.g i) hp
  have := Formalism.MainNotions.J.pI_max (D.host.g i) hp
  rw [← IsDedekindDomain.coe_primesOverFinset (Formalism.MainNotions.J.pI_ne_bot _ hp) (𝓞 D.host.E), Set.ncard_coe_finset, ← e]
  exact h

theorem residEv_free {eps : ℝ} (Fm : FamP eps) : S.ResidEv Fm :=
  ⟨0, fun x _ i => ⟨S.root_discriminant_ge_two _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _),
    fun u => S.splitsCompl_of_ncard _ _ ((Fm.D x i).mem u).A.T_prime
      (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ cycSplit_holds _ ((Fm.D x i).mem u).A.T_prime (S.level_norm_one_mod_conductor _ u)).2,
    splitsE_g _ 0, splitsE_g _ 1, S.discriminant_eq_base_sq _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _)⟩⟩

theorem residEv_closed_free (𝒞 : FamClass) : Closed 𝒞 fun Fm _ => S.ResidEv Fm :=
  Closed.of_class fun Fm _ _ => residEv_free Fm

end Formalism.L2.SG.ResidEvFree

end
