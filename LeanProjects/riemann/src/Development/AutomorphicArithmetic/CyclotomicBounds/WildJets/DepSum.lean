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
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem false_of_coprime_natCast_mem_heightOne {R : Type*} [CommRing R] [IsDomain R] (v : HeightOneSpectrum R)
    (a b : ℕ) (hab : Nat.Coprime a b) (ha : (a : R) ∈ v.asIdeal) (hb : (b : R) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h1 : (x : R) * a + (y : R) * b = 1 := by
    have := congrArg (Int.cast : ℤ → R) hxy
    push_cast at this
    exact this
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

private theorem prime_le_absNorm_of_mem_heightOne (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (l : ℕ)
    (hl : l.Prime) (h : (l : 𝓞 K) ∈ v.asIdeal) : l ≤ Ideal.absNorm v.asIdeal := by
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
  by_contra hd
  exact false_of_coprime_natCast_mem_heightOne v l _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hd) h (Ideal.absNorm_mem _)

private theorem prime_eq_of_natCast_mem_heightOne {R : Type*} [CommRing R] [IsDomain R] (v : HeightOneSpectrum R)
    (l m : ℕ) (hl : l.Prime) (hm : m.Prime) (h1 : (l : R) ∈ v.asIdeal) (h2 : (m : R) ∈ v.asIdeal) : l = m := by
  by_contra hne
  exact false_of_coprime_natCast_mem_heightOne v l m ((Nat.coprime_primes hl hm).2 hne) h1 h2

theorem UpperTheory.WildA.depSum :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}, ∃ S : Finset ℕ, GlobalTheory.NormSum.Exponents S (fun l => if l.Prime then (depL G l : ℝ) else 0) (sig G) := by
  classical
  intro D T L sc G
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal ≤ N := by
    refine ⟨∑ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal, fun v hv => ?_⟩
    exact Finset.single_le_sum (f := fun v : Pl ↥D.host.F => Ideal.absNorm v.asIdeal)
      (fun _ _ => Nat.zero_le _) hv
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, ∀ l, l ∈ S ↔ l.Prime ∧ l ≤ N :=
    ⟨(Finset.range (N + 1)).filter Nat.Prime, fun l => by
      rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, and_comm]⟩
  have key : ∀ v ∈ G.pl.S0, ∀ l : ℕ, l.Prime → ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal →
      l ≤ Ideal.absNorm v.asIdeal := by
    intro v hv l hl h
    apply prime_le_absNorm_of_mem_heightOne _ v l hl
    have := G.pl.w_over v hv
    rw [← this]
    simpa [IsDedekindDomain.HeightOneSpectrum.under] using h
  have hdep : ∀ l : ℕ, depL G l ≤
      ∑ v ∈ G.pl.S0.filter (fun v => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), G.pl.depth sc v := by
    intro l
    unfold GlobalTheory.SumSize.depL
    apply Finset.sup_le
    intro PP hPP
    obtain ⟨hPP1, hmem⟩ := Finset.mem_filter.1 hPP
    unfold GlobalTheory.ChiGrid.Places.W0 at hPP1
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPP1
    rw [(GlobalTheory.FunObj.depthAt_w G hv).2]
    exact Finset.single_le_sum (f := fun v => G.pl.depth sc v) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨hv, hmem⟩)
  have hinner : ∀ v ∈ G.pl.S0,
      ∑ l ∈ S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), Real.log (l : ℝ) ≤
        Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    intro v hv
    rcases (S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal)).eq_empty_or_nonempty
      with he | ⟨l0, hl0⟩
    · rw [he, Finset.sum_empty]
      exact Real.log_natCast_nonneg _
    · obtain ⟨hl0S, hl0P⟩ := Finset.mem_filter.1 hl0
      have hp0 : l0.Prime := ((hS l0).1 hl0S).1
      have hsub : S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal) ⊆ {l0} := by
        intro m hm
        rw [Finset.mem_singleton]
        obtain ⟨hmS, hmP⟩ := Finset.mem_filter.1 hm
        exact prime_eq_of_natCast_mem_heightOne _ m l0 ((hS m).1 hmS).1 hp0 hmP hl0P
      calc _ ≤ ∑ l ∈ ({l0} : Finset ℕ), Real.log (l : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Real.log_natCast_nonneg i)
        _ = Real.log (l0 : ℝ) := Finset.sum_singleton _ _
        _ ≤ _ := by
          apply Real.log_le_log (by exact_mod_cast hp0.pos)
          exact_mod_cast key v hv l0 hp0 hl0P
  refine ⟨S, ?_⟩
  unfold GlobalTheory.NormSum.Exponents
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl
    exact ((hS l).1 hl).1
  · intro l
    dsimp only
    split_ifs <;> positivity
  · intro l hl
    dsimp only
    split_ifs with hp
    · have h0 : depL G l = 0 := by
        apply Nat.eq_zero_of_le_zero
        refine (hdep l).trans (le_of_eq (Finset.sum_eq_zero ?_))
        intro v hv'
        obtain ⟨hv, hmem⟩ := Finset.mem_filter.1 hv'
        exact absurd ((hS l).2 ⟨hp, (key v hv l hp hmem).trans (hN v hv)⟩) hl
      rw [h0, Nat.cast_zero]
    · rfl
  · dsimp only
    calc ∑ l ∈ S, (if l.Prime then (depL G l : ℝ) else 0) * Real.log (l : ℝ)
        ≤ ∑ l ∈ S, ∑ v ∈ G.pl.S0, (if ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal then
            (G.pl.depth sc v : ℝ) * Real.log (l : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro l hl
          have hp : l.Prime := ((hS l).1 hl).1
          rw [if_pos hp, ← Finset.sum_filter, ← Finset.sum_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg l)
          exact_mod_cast hdep l
      _ = ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) *
            ∑ l ∈ S.filter (fun l : ℕ => ((l : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal), Real.log (l : ℝ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.mul_sum, Finset.sum_filter]
      _ ≤ ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
          apply Finset.sum_le_sum
          intro v hv
          exact mul_le_mul_of_nonneg_left (hinner v hv) (by positivity)
      _ = sig G := by
          unfold GlobalTheory.SumSize.sig
          rfl
