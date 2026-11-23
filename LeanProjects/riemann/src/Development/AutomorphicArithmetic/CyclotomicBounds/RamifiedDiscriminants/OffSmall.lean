import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.RamDiscr

open NumberField Ideal Formalism.BasicNotions
open scoped Pointwise

namespace UpperTheory.Ram

variable {R : Ranks} (H : Host R)

theorem natCast_notMem_of_coprime {A : Type} [CommRing A] {I : Ideal A} (hI : I ≠ ⊤) {l n : ℕ} (hl : (l : A) ∈ I)
    (h : Nat.Coprime n l) : (n : A) ∉ I := by
  intro hn
  obtain ⟨x, y, e⟩ : IsCoprime (n : A) (l : A) := Nat.Coprime.cast h
  exact hI ((Ideal.eq_top_iff_one _).2 (e ▸ I.add_mem (I.mul_mem_left _ hn) (I.mul_mem_left _ hl)))

theorem coprime_QSq {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) (hq : l ≠ H.q) : Nat.Coprime (H.QS * H.q) l := by
  refine ((Nat.Prime.coprime_iff_not_dvd hl).2 fun h => ?_).symm
  rcases (H.toHostRaw.dvd_QSq_iff hl).1 h with h | h
  · exact UpperTheory.Small.not_dvd_QS H hl hs h
  · exact hq h

theorem coprime_condN {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) (hq : l ≠ H.q) (hd : l ≠ H.d) :
    Nat.Coprime (H.QS * H.q * H.d) l :=
  ((Nat.Prime.coprime_iff_not_dvd hl).2 (UpperTheory.Small.not_dvd_condN H hl hs hq hd)).symm

theorem QSq_notMem {A : Type} [CommRing A] {Q : Ideal A} (hQ : Q ≠ ⊤) {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) (hq : l ≠ H.q)
    (hlQ : (l : A) ∈ Q) : ((H.QS * H.q : ℕ) : A) ∉ Q :=
  natCast_notMem_of_coprime hQ hlQ (coprime_QSq H hl hs hq)

theorem notMem_small_of_QS_notMem {A : Type} [CommRing A] {Q : Ideal A} {l : ℕ} (hlQ : (l : A) ∈ Q)
    (h : ((H.QS : ℕ) : A) ∉ Q) : l ∉ H.small := by
  intro hs
  obtain ⟨c, hc⟩ := ((H.toHostRaw.mem_small_iff).1 hs).2
  exact h (by rw [hc]; push_cast; exact Q.mul_mem_right _ hlQ)

theorem half_ne_bot : H.𝔟 ≠ ⊥ := by
  intro hb
  have h1 := H.𝔟_spec.1
  rw [hb, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem half_not_le (Q : Ideal (𝓞 H.E)) [hQ : Q.IsPrime] (h : ((H.QS * H.q : ℕ) : 𝓞 H.E) ∉ Q) : ¬ H.𝔟 ≤ Q := by
  intro hle
  refine h (H.der.diffSupport Q hQ ?_)
  rw [H.𝔟_spec.1]
  exact (Ideal.dvd_iff_le.2 hle).mul_right _

theorem exists_den (Q : Ideal (𝓞 H.E)) [Q.IsPrime] (h : ((H.QS * H.q : ℕ) : 𝓞 H.E) ∉ Q) :
    ∃ z : 𝓞 H.E, z ∉ Q ∧ ∀ t ∈ H.AA0, ∃ w : 𝓞 H.E, (w : H.E) = t * (z : H.E) := by
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 (half_not_le H Q h)
  have hB : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (half_ne_bot H)
  refine ⟨z, hzP, fun t ha => ?_⟩
  unfold Host.AA0 at ha
  rw [FractionalIdeal.mem_inv_iff hB] at ha
  obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  exact ⟨w, hw⟩

theorem not_dvd_natAbs_discr {p : ℕ} (hp : p.Prime) (hs : p ∉ H.small) (hq : p ≠ H.q) (hd : p ≠ H.d) :
    ¬ p ∣ (discr H.E).natAbs :=
  fun h => UpperTheory.Small.not_dvd_condN H hp hs hq hd ((H.dvd_natAbs_discr_iff hp).1 h)

theorem inertiaK_trivial {l : ℕ} (hl : l.Prime) (hs : l ∉ H.small) (hq : l ≠ H.q) (P : Ideal (𝓞 H.E)) [hP : P.IsPrime]
    (hlP : (l : 𝓞 H.E) ∈ P) (σ : H.E ≃ₐ[H.K] H.E) (hσ : ∀ x : 𝓞 H.E, σ • x - x ∈ P) : σ = 1 := by
  have : Fact l.Prime := ⟨hl⟩
  have hlz : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have hlo : P.LiesOver (span {(l : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hlz).2 (by simpa using hlP)
  set σ' : H.E ≃ₐ[ℚ] H.E := σ.restrictScalars ℚ with hσ'
  have hin : ∀ x : 𝓞 H.E, σ' • x - x ∈ P := hσ
  suffices h1 : σ' = 1 from AlgEquiv.ext fun x => DFunLike.congr_fun h1 x
  by_cases hd : l = H.d
  · subst hd
    rcases (H.der.inertia_d P σ').1 hin with h | h
    · exact (H.toHostAx.galE_eq_one_iff σ').1 h
    · have hm : H.toHostAx.galE σ' ∈ R.toFrame.Psi :=
        (H.toHostAx.galE_mem_Psi_iff σ').2 (σ.commutes ⟨H.sqd, H.toHostRaw.sqd_mem_K⟩)
      rw [Formalism.HC.Frame.mem_Psi_iff] at hm
      have h2 : (H.gal σ').1.2 = 1 := hm
      rw [h] at h2
      exact absurd (show (-1 : ℤˣ) = 1 from h2) (by decide)
  · exact ((H.der.frob l (UpperTheory.Small.not_dvd_condN H hl hs hq hd) P).2.2.2 σ').1 hin

theorem g_notMem_small (D : D7) (k : Fin 2) : D.host.g k ∉ D.host.small :=
  UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k)

end UpperTheory.Ram
