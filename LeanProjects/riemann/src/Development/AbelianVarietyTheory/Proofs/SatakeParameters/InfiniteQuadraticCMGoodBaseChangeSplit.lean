import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsInfiniteQcmSplitRam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmQuadraticAdjoinSqrtNegNatStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceBelowCMFieldOfSqrtNegPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsUnramifiedAtOfSqEqNegPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatUnramifiedOverRealOfCmSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankMaximalRealEvenStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CMFam

open IntermediateField

theorem exists_qcm_adjoin (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ) (hp : 0 < p) (δ : Ω) (hδ : δ ^ 2 = -(p : Ω))
    (hn : δ ∉ Set.range (algebraMap E Ω)) :
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} :=
  GlobalTheory.T.exists_cmQuadratic_adjoin_sqrt_neg_nat E Ω p hp δ hδ hn

theorem isSplitAt_of_dvd (L : Type) [Field L] [NumberField L] [IsCMField L] (p q : ℕ) (δ : L) (hp : 0 < p)
    (hδ : δ ^ 2 = -(p : L)) (hq : ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1) (w : HeightOneSpectrum (𝓞 L))
    (hw : (q : 𝓞 L) ∈ w.asIdeal) : GlobalTheory.UnitaryBC.IsSplitAt w :=
  GlobalTheory.T.isSplitPlaceBelowCMField_of_sqrt_neg_prime L p q δ hp hδ hq w hw

theorem not_isUnramifiedAt (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (p : ℕ) (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (δ : K) (hδ : δ ^ 2 = -(p : K))
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal :=
  GlobalTheory.T.not_isUnramifiedAt_of_sq_eq_neg_prime E K p hp hd δ hδ w hw

theorem exists_unram (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra E K]
      (w : HeightOneSpectrum (𝓞 K)), (N : 𝓞 K) ∉ w.asIdeal →
        Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) w.asIdeal :=
  GlobalTheory.T.exists_nat_unramified_over_maximalRealSubfield E

theorem even_finrank (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    (Q : GlobalTheory.RealGal.QCM E Ω) : Even (Module.finrank ℚ (maximalRealSubfield Q.K)) :=
  GlobalTheory.T.finrank_maximal_real_even E Ω Q

end GlobalTheory.CMFam

namespace GlobalTheory.CMFam

theorem dvd_of_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q n : ℕ} (hq : q.Prime)
    (hqw : (q : 𝓞 K) ∈ w.asIdeal) (hn : (n : 𝓞 K) ∈ w.asIdeal) : q ∣ n := by
  by_contra h
  have hc : Nat.gcd q n = 1 := (Nat.Prime.coprime_iff_not_dvd hq).2 h
  have hm : (((Nat.gcd q n : ℕ) : ℤ) : 𝓞 K) ∈ w.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab q n]
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_right _ hqw) (w.asIdeal.mul_mem_right _ hn)
  rw [hc] at hm
  simp only [Nat.cast_one, Int.cast_one] at hm
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem natCast_mem_under {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : (n : 𝓞 E) ∈ (w.under (𝓞 E)).asIdeal ↔ (n : 𝓞 K) ∈ w.asIdeal := by
  change _ ∈ Ideal.comap _ _ ↔ _
  rw [Ideal.mem_comap, map_natCast]

end GlobalTheory.CMFam

open GlobalTheory.CMFam GlobalTheory.ExSplitCM in

theorem GlobalTheory.GalCut.infinite_qcm_split_good : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)), {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P}.Infinite := by
  intro hAF E Ω _ _ _ _ _ _ l _ a π w₀
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q₀, hq₀, hq₀w⟩ := exists_prime_mem w₀
  haveI : Fact q₀.Prime := ⟨hq₀⟩
  obtain ⟨N, hN0, hN⟩ := exists_unram E
  set S : Set (HeightOneSpectrum (𝓞 E)) := {v | ¬ ∃ B, (CG.mk π).HasSat v B} with hSdef
  have hS : S.Finite := Filter.eventually_cofinite.1 (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hAF E a π)
  set T : Finset ℕ := ({2, l, q₀} : Finset ℕ) ∪ N.primeFactors ∪ (discr E).natAbs.primeFactors ∪
    (finite_primes_of_finite hS).toFinset with hTdef
  set M : ℕ := 8 * ∏ q ∈ T, q with hM
  have hT2 : 2 ∈ T := by simp [hTdef]
  have hTl : l ∈ T := by simp [hTdef]
  have hTq₀ : q₀ ∈ T := by simp [hTdef]
  have hTN : ∀ r : ℕ, r.Prime → r ∣ N → r ∈ T := fun r hr hd => by
    simp [hTdef, Nat.mem_primeFactors, hr, hd, hN0]
  have hTd : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ discr E → r ∈ T := fun r hr hd => by
    have : r ∈ (discr E).natAbs.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hr, Int.natCast_dvd.1 hd, Int.natAbs_ne_zero.2 (discr_ne_zero E)⟩
    simp [hTdef, this]
  have hTS : ∀ r : ℕ, r.Prime → ∀ v ∈ S, (r : 𝓞 E) ∈ v.asIdeal → r ∈ T := fun r hr v hv h => by
    have : r ∈ (finite_primes_of_finite hS).toFinset := by simpa using ⟨hr, v, hv, h⟩
    simp [hTdef, this]
  have hM0 : M ≠ 0 := by
    rw [hM]
    refine mul_ne_zero (by norm_num) ?_
    rw [Finset.prod_ne_zero_iff]
    intro q hq h0
    subst h0
    simp [hTdef] at hq
    rcases hq with h | h | h
    · exact (Fact.out : l.Prime).ne_zero h.symm
    · exact hq₀.ne_zero h.symm
    · exact Nat.not_prime_zero h.1
  haveI : NeZero M := ⟨hM0⟩
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  set Gd : Set ℕ := {p | p.Prime ∧ p ∉ T ∧ (M : ℤ) ∣ (p : ℤ) + 1} with hGd
  have hGood : Gd.Infinite := by
    refine ((Nat.infinite_setOfPred_prime_and_eq_mod (q := M) isUnit_one.neg).diff T.finite_toSet).mono ?_
    rintro p ⟨⟨hp, hpe⟩, hpT⟩
    refine ⟨hp, hpT, ?_⟩
    have : (((p : ℤ) + 1 : ℤ) : ZMod M) = 0 := by push_cast; rw [hpe]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have h8 : ∀ p ∈ Gd, ∀ q ∈ T, ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1 := fun p hp q hq => by
    refine dvd_trans ?_ hp.2.2
    rw [Int.natCast_dvd_natCast, hM]
    exact Nat.mul_dvd_mul_left 8 (Finset.dvd_prod_of_mem _ hq)
  have hodd : ∀ p ∈ Gd, p ≠ 2 := fun p hp h => hp.2.1 (h ▸ hT2)
  have hdisc : ∀ p ∈ Gd, ¬ (p : ℤ) ∣ discr E := fun p hp h => hp.2.1 (hTd p hp.1 h)
  have hmove : ∀ p ∈ Gd, ∀ (u : HeightOneSpectrum (𝓞 E)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 E) ∈ u.asIdeal →
      IsPlaceOver A' u → ∃ s ∈ Ine (F := E) A', s (δ p) ≠ δ p := fun p hp u A' hu hA' =>
    GlobalTheory.SqrtNegRam.sqrt_neg_moved_by_inertia E Ω p hp.1 (hodd p hp) (hdisc p hp) (δ p) (hδ p) u A' hu hA'
  have hnot : ∀ p ∈ Gd, δ p ∉ Set.range (algebraMap E Ω) := by
    rintro p hp ⟨x, hx⟩
    obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
    obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
    obtain ⟨s, -, hs⟩ := hmove p hp u A' hu hA'
    exact hs (by rw [← hx]; exact s.commutes x)
  have hQ : ∀ p ∈ Gd, ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} := fun p hp =>
    exists_qcm_adjoin E Ω p hp.1.pos (δ p) (hδ p) (hnot p hp)
  have hmem : ∀ p ∈ Gd, ∀ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ p} →
      Q ∈ {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P} := by
    intro p hp Q hQK
    have hδK : δ p ∈ Q.K := by rw [hQK]; exact IntermediateField.mem_adjoin_simple_self E (δ p)
    set y : ↥Q.K := ⟨δ p, hδK⟩ with hy
    have hy2 : y ^ 2 = -(p : ↥Q.K) := Subtype.ext (by simpa using hδ p)
    have hsplit : ∀ q ∈ T, ∀ w : HeightOneSpectrum (𝓞 ↥Q.K), (q : 𝓞 ↥Q.K) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w :=
      fun q hq w hw => isSplitAt_of_dvd _ p q y hp.1.pos hy2 (h8 p hp q hq) w hw
    refine ⟨fun A hA s hs => ?_, fun w hw => ?_, ?_, fun P hP => ?_⟩
    · rw [mem_range_res_iff, hQK]
      refine fix_adjoin (halg.isAlgebraic (δ p)).isIntegral s ?_
      exact GlobalTheory.SqFix.sqrt_fixed_of_isSquare_padic E Ω w₀ A hA q₀ hq₀w (-(p : ℤ)) (δ p)
        (by push_cast; exact hδ p)
        (by push_cast; exact GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q₀ p (h8 p hp q₀ hTq₀)) s hs
    · refine hsplit q₀ hTq₀ w ?_
      rw [← natCast_mem_under (E := E), hw]
      exact hq₀w
    · obtain ⟨w, hw⟩ := exists_mem_of_prime (F := ↥Q.K) hp.1
      refine ⟨w, not_isUnramifiedAt E ↥Q.K p hp.1 (hdisc p hp) y hy2 w hw, ?_⟩
      by_contra hB
      exact hp.2.1 (hTS p hp.1 _ hB ((natCast_mem_under w p).2 hw))
    · refine ⟨⟨y, p, hp.1.pos, by rw [hy2]⟩, even_finrank E Ω Q, fun w hw => ?_⟩
      obtain ⟨q, hq, hqw⟩ := exists_prime_mem w
      have hqT : q ∉ T := fun h => hw (hsplit q h w hqw)
      refine ⟨fun hl => hqT (prime_eq_of_mem w (Fact.out : l.Prime) hq hl hqw ▸ hTl), ?_, ?_⟩
      · refine hN ↥Q.K w fun h => hqT (hTN q hq (dvd_of_mem w hq hqw h))
      · have hB : ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B := by
          by_contra hB
          exact hqT (hTS q hq _ hB ((natCast_mem_under w q).2 hqw))
        obtain ⟨B, hB⟩ := hB
        exact ⟨_, hP.sat w _ B (GlobalTheory.RealGal.AttRes.normV_eq_pow w) hB⟩
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : GlobalTheory.RealGal.QCM E Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 E) |
      ¬ ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Ine (F := E) A' ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 E) ∈ u.asIdeal})
    fun Q _ => finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds E ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_of_prime (F := E) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  refine ⟨u, fun hall => ?_, hu⟩
  obtain ⟨s, hs, hne⟩ := hmove p hp u A' hu hA'
  refine hne ((mem_range_res_iff Q.K s).1 (hall A' hA' hs) (δ p) ?_)
  rw [hQK]
  exact IntermediateField.mem_adjoin_simple_self E (δ p)

end
