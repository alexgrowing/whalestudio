import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassC0PrimeNotExceptional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DifferentAtBasePlace

theorem ne_of_mod_eq_one' {p M k : ℕ} (hp : p % M = 1) (hk : k ∣ M) (hk1 : 1 < k) : p ≠ k := by
  rintro rfl
  have h := Nat.mod_mod_of_dvd p hk
  rw [hp, Nat.mod_self, Nat.mod_eq_of_lt hk1] at h
  exact one_ne_zero h

theorem natAbs_discr_F_dvd (D : D7) : (discr D.host.F).natAbs ∣ (discr D.host.E).natAbs := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow D.host.F (𝓞 D.host.F) D.host.E (𝓞 D.host.E)]
  exact Dvd.dvd.mul_left (dvd_pow_self _ Module.finrank_pos.ne') _

theorem leastSplitAuxiliaryPrime_not_dvd_discr_base (D : D7) : ¬ q0 D ∣ (discr D.host.F).natAbs := by
  obtain ⟨hp, hm, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  intro h
  have hc : q0 D ∣ Formalism.BasicNotions.LevelStarExponents.condE D :=
    D.host.der.discr_primes.1 _ hp (Int.natCast_dvd.2 (h.trans (natAbs_discr_F_dvd D)))
  exact ne_of_mod_eq_one' hm (dvd_mul_of_dvd_right hc _) hp.one_lt rfl

theorem not_dvd_different {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) :
    ¬ G.pl.v0.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro h
  have hdisc : ((discr D.host.F : ℤ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal :=
    Ideal.le_of_dvd h (discr_mem_differentIdeal D.host.F (𝓞 D.host.F))
  have hq : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal := G.pl.basePlace_over_qZero
  have hcop : IsCoprime (q0 D : ℤ) (discr D.host.F) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm, Int.gcd, Int.natAbs_natCast]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (leastSplitAuxiliaryPrimeThetaChain_spec D).1).2 (leastSplitAuxiliaryPrime_not_dvd_discr_base D))
  obtain ⟨u, v, huv⟩ := hcop
  apply G.pl.v0.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have := congrArg (Int.cast : ℤ → 𝓞 D.host.F) huv
  push_cast at this
  rw [← this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast hq)) (Ideal.mul_mem_left _ _ hdisc)

end GlobalTheory.DifferentAtBasePlace
