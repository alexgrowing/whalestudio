import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
import Formalism.LocalToGlobal.UnitaryNorms.CharShare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.WildA.prime_eq_of_mem_prime_ideal {R : Type} [CommRing R] {I : Ideal R} (hI : I.IsPrime) {a b : ℕ} (ha : a.Prime)
    (hb : b.Prime) (hai : (a : R) ∈ I) (hbi : (b : R) ∈ I) : a = b := by
  by_contra hne
  have h : Nat.Coprime a b := (Nat.coprime_primes ha hb).2 hne
  obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom R)
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hai) (Ideal.mul_mem_left _ _ hbi)

private theorem UpperTheory.WildA.split_of_split_class {D : D7} {p : ℕ} (h : D.host.cls p = .splitK) : GlobalTheory.NormSum.SplitIn D p := by
  right
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | cases h

theorem UpperTheory.WildA.small_set_primes_split :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ v ∈ G.pl.S0, ∀ l : ℕ, l.Prime → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := by
  intro D T L sc G large₂ hS v hv l hl hlv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hS
  have key : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := fun p hp hm h => by
    rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal v.isPrime hl hp hlv h]
    exact UpperTheory.WildA.split_of_split_class (Pm.level_split p hm)
  rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
  · rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal G.pl.v0.isPrime hl (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1 hlv G.pl.basePlace_over_qZero]
    exact Or.inr (Formalism.L2.Host.split_prime_jacobi_neg_d D)
  · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
    · exact key _ (D.host.g_prime 0) (D.host.g_level 0) h
    · exact key _ (D.host.g_prime 1) (D.host.g_level 1) h
    · exact key _ D.host.pde_prime D.host.pde_level.1 h
    · exact key _ D.host.pde'_prime D.host.pde_level.2 h
