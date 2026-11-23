import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlacesPrime

theorem not_both_mem {R : Type} [CommRing R] {I : Ideal R} (hI : I.IsPrime) {a b : ℕ} (h : Nat.Coprime a b)
    (ha : (a : R) ∈ I) : (b : R) ∉ I := by
  intro hb
  obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom R)
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem coprime_level {D : D7} {large₂ : SizeData₂ D} (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) {p : ℕ} (hp : p.Prime)
    (hl : p ∈ D.host.levelPrimes) : Nat.Coprime p (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := h
  exact Nat.Coprime.mul_right (UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hp (P.level_split p hl))
    (D.host.ccK_coprime p (by simp [hl])).symm

theorem leastSplitAuxiliaryPrime_coprime_host_invariants (D : D7) : Nat.Coprime (q0 D) (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
  obtain ⟨hp, hm, hn⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  have hM : Nat.Coprime (q0 D) (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hm, Nat.gcd_one_left]
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D :=
    Dvd.dvd.mul_left dvd_rfl _
  exact Nat.Coprime.mul_right (hM.coprime_dvd_right hdvd) ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)

theorem places_prime_to_level : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ w ∈ ch.G.pl.W0,
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro w hw
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  have hunder := ch.G.pl.under_w hv

  have lift : ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ (ch.G.pl.w v).asIdeal := by
    intro n hn
    rw [← hunder] at hn
    have := Ideal.mem_comap.1 hn
    simpa using this
  obtain ⟨p, hp, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧
      Nat.Coprime p (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
    rcases ch.G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
    · exact ⟨q0 D, ch.G.pl.basePlace_over_qZero, leastSplitAuxiliaryPrime_coprime_host_invariants D⟩
    · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
      · exact ⟨_, h, coprime_level hS.size (D.host.g_prime 0) (D.host.g_level 0)⟩
      · exact ⟨_, h, coprime_level hS.size (D.host.g_prime 1) (D.host.g_level 1)⟩
      · exact ⟨_, h, coprime_level hS.size D.host.pde_prime D.host.pde_level.1⟩
      · exact ⟨_, h, coprime_level hS.size D.host.pde'_prime D.host.pde_level.2⟩
  exact not_both_mem (ch.G.pl.w v).isPrime hcop (lift p hp)

end GlobalTheory.PlacesPrime
