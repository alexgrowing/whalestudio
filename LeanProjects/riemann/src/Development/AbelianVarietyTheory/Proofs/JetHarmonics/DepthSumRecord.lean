import Mathlib
import Development.AutomorphicArithmetic.CMTraceForms.CmDatumNatCastMemHeightOneSpectrumIff
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsGeneratesIffFg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnscaledWeightDepthFiniteBoundedAboveChartsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAddStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumFinitePlacesLeSumOverPrimesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLogPrimeDepthBoundsLeMulWeightSizeStatement

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie GlobalTheory.PlusRec
namespace GlobalTheory.DepthSum

noncomputable def primeBound (N Q q d : ℕ) (g : Fin 2 → ℕ) (a b : ℝ) (p : ℕ) : ℝ :=
  (if p ∈ (Finset.range (N + 1)).filter Nat.Prime then (N : ℝ) / ((p : ℝ) - 1) else 0) +
    ((padicValNat p Q : ℝ) * a + (if p = q then b else 0) + (if p = d then b else 0)) +
    ∑ i : Fin 2, if p = g i then (N : ℝ) / ((g i : ℝ) - 1) else 0

theorem div_pred_nonneg (N : ℕ) {p : ℕ} (hp : p.Prime) : 0 ≤ (N : ℝ) / ((p : ℝ) - 1) := by
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact div_nonneg (by positivity) (by linarith)

theorem sum_primeBound (N Q q d : ℕ) (g : Fin 2 → ℕ) (a b : ℝ) (S : Finset ℕ)
    (hA : (Finset.range (N + 1)).filter Nat.Prime ⊆ S) (h2 : Q.primeFactors ⊆ S) (hS : ∀ p ∈ S, p.Prime) (hq : q ∈ S) (hd : d ∈ S) (hg : ∀ i, g i ∈ S) :
    ∑ p ∈ S, primeBound N Q q d g a b p * Real.log p =
      (N : ℝ) * (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)) +
        (a * Real.log Q + b * Real.log q + b * Real.log d) + ∑ i : Fin 2, (N : ℝ) / ((g i : ℝ) - 1) * Real.log (g i) := by
  have hQ : ∑ p ∈ S, (padicValNat p Q : ℝ) * a * Real.log p = a * Real.log Q := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, Finset.mul_sum]
    symm
    refine Finset.sum_subset_zero_on_sdiff h2 (fun p hp => ?_) fun p hp => ?_
    · obtain ⟨h3, h4⟩ := Finset.mem_sdiff.1 hp
      rw [← Nat.factorization_def _ (hS p h3), Finsupp.notMem_support_iff.1 (Nat.support_factorization Q ▸ h4)]; simp
    · rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]; ring
  unfold primeBound
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_mul]
  rw [hQ, Finset.sum_ite_mem, Finset.inter_eq_right.2 hA, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', hq, hd, hg, if_true, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem depth_sum {D : D7} (B : WeightFamilies.Prov D) {j : ℕ} (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j)
    (hn : 2 * D.R.f * D.R.r ≤ w.n) (hL : Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L)
    (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ) (h0 : ∀ la, 0 ≤ nu la)
    (h1 : ∀ la, nu la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1)) (h2 : ∀ la, WeightAlgebra.DF w < resCharOf la → nu la = 0) :
    (∀ la, 0 ≤ nusOf B w nu la) ∧ (Function.support (nusOf B w nu)).Finite ∧
      (∑ᶠ la, |nusOf B w nu la| * lw B.KO la) ≤ WeightAlgebra.PN D large₂ * w.size := by
  classical
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hg := D.host.g_prime
  have hn1 : 1 ≤ w.n := by
    have hf : 1 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity)
      omega
    have hr : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      unfold Ranks.r
      omega
    have : 1 ≤ 2 * D.R.f * D.R.r := Nat.mul_pos (by omega) hr
    omega
  have hpos : ∀ la, 0 ≤ nusOf B w nu la := by
    intro la
    unfold nusOf
    split_ifs with ha hb hc
    · rw [mul_div_assoc]
      exact mul_nonneg (by positivity) (div_pred_nonneg _ (hg _))
    all_goals exact mul_nonneg (by positivity) (add_nonneg (h0 la) (by positivity))
  set N := WeightAlgebra.DF w with hN
  set A := (Finset.range (N + 1)).filter Nat.Prime with hA
  set S : Finset ℕ := A ∪ (D.host.small ∪ {D.host.q, D.host.d, D.host.g 0, D.host.g 1}) with hS
  have hgS : ∀ i, D.host.g i ∈ S := by
    intro i
    fin_cases i <;> simp [hS]
  have e1 : ∀ p, 0 ≤ (if p ∈ A then (N : ℝ) / ((p : ℝ) - 1) else 0) := by
    intro p
    split_ifs with hp
    · exact div_pred_nonneg _ (Finset.mem_filter.1 hp).2
    · exact le_rfl
  have e2 : ∀ (p x c : ℕ), (0 : ℝ) ≤ (if p = x then (c : ℝ) else 0) := by
    intro p x c
    split_ifs <;> positivity
  have e3 : ∀ p i, 0 ≤ (if p = D.host.g i then (N : ℝ) / ((D.host.g i : ℝ) - 1) else 0) := by
    intro p i
    split_ifs with hp
    · exact div_pred_nonneg _ (hg _)
    · exact le_rfl
  have e4 : ∀ la : HeightOneSpectrum (𝓞 B.KO),
      nu la ≤ (if resCharOf la ∈ A then (N : ℝ) / ((resCharOf la : ℝ) - 1) else 0) := by
    intro la
    split_ifs with hp
    · exact h1 la
    · refine (h2 la ?_).le
      by_contra hlt
      exact hp (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), Crude.resCharOf_prime la⟩)
  have hsm : D.host.small ⊆ S := Finset.subset_union_left.trans Finset.subset_union_right
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    simp only [hS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | rfl | rfl | rfl | rfl
    exacts [(Finset.mem_filter.1 hp).2, (D.host.mem_small_iff.1 hp).1, hq, hd, hg _, hg _]
  have hQ : ∀ la : HeightOneSpectrum (𝓞 B.KO), ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ↔ resCharOf la ∈ D.host.small :=
    fun la => (UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff D.host.toHostRaw B.KO la).1
  have e5 : ∀ p : ℕ, (0 : ℝ) ≤ (padicValNat p D.host.QS : ℝ) * (c2 D w : ℝ) := fun p => by positivity
  have key := GlobalTheory.T.sum_finitePlaces_le_sum_over_primes B.KO (primeBound N D.host.QS D.host.q D.host.d D.host.g (c2 D w) (cHalf w)) S hSp ?_
    (nusOf B w nu) hpos ?_ ?_
  · refine ⟨hpos, key.1, key.2.trans ?_⟩
    rw [sum_primeBound _ _ _ _ _ _ _ S Finset.subset_union_left hsm hSp (by simp [hS]) (by simp [hS]) hgS]
    refine le_trans ?_ (GlobalTheory.T.sum_log_prime_depth_bounds_le_mul_weight_size D large₂ j w hn1 hL)
    have := mul_le_mul_of_nonneg_left (GlobalTheory.T.sum_prime_log_div_pred_le_log_add N) (Nat.cast_nonneg (α := ℝ) N)
    linarith
  · intro p
    unfold primeBound
    exact add_nonneg (add_nonneg (e1 p) (add_nonneg (add_nonneg (e5 _) (e2 _ _ _)) (e2 _ _ _)))
      (Finset.sum_nonneg fun i _ => e3 p i)
  · intro la
    have s3 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => e3 (resCharOf la) i
    have a1 := e1 (resCharOf la)
    have a2 := e5 (resCharOf la)
    have a3 := e2 (resCharOf la) D.host.q (cHalf w)
    have a4 := e2 (resCharOf la) D.host.d (cHalf w)
    have a5 := e4 la
    unfold nusOf primeBound
    rw [H1algLink.eWL_eq]
    by_cases ha : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
    · rw [dif_pos ha, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hc := (H1algLink.prime_mem_iff la (hg _)).1 (Classical.choose_spec ha)
      have := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => e3 (resCharOf la) i)
        (Finset.mem_univ (Classical.choose ha))
      rw [if_pos hc] at this
      linarith
    · rw [dif_neg ha]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      by_cases hb : ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
      · rw [if_pos hb, show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
        linarith
      · rw [if_neg hb]
        by_cases hc : ((D.host.q : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ∨ ((D.host.d : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
        · rw [if_pos hc]
          rw [H1algLink.prime_mem_iff la hq, H1algLink.prime_mem_iff la hd] at hc
          rcases hc with hc | hc
          · rw [if_pos hc]
            linarith
          · rw [if_pos hc]
            linarith
        · rw [if_neg hc]
          linarith
  · intro la hla
    have hne : ∀ p ∈ S, p.Prime → ((p : ℕ) : 𝓞 B.KO) ∉ la.asIdeal := fun p hp hpp hm =>
      hla ((H1algLink.prime_mem_iff la hpp).1 hm ▸ hp)
    have hnA : resCharOf la ∉ A := fun h => hla (Finset.mem_union_left _ h)
    have a5 := e4 la
    rw [if_neg hnA] at a5
    unfold nusOf
    rw [dif_neg (fun ⟨i, hi⟩ => hne _ (hgS i) (hg i) hi), if_neg (fun h => hla (hsm ((hQ la).1 h))),
      if_neg (not_or.2 ⟨hne _ (by simp [hS]) hq, hne _ (by simp [hS]) hd⟩), le_antisymm a5 (h0 la)]
    simp

theorem depth_sum_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) w (nusOf (recB h.toLawsCore) w (nuWt T w)) ∧ ∀ (Nd : NormDatum (recB h.toLawsCore)), WeightedPrimeSumBoundAlt large₂ (Nd.X' (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)) w (nusOf (recB h.toLawsCore) w (nuWt T w)) := by
  intro D T h j hj large₂ w hn hL
  have hb := GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts D T h j hj w hn
  have key := depth_sum (recB h.toLawsCore) large₂ w hn hL (nuWt T w) (fun la => (hb la).2.1) (fun la => (hb la).2.2.1)
    (fun la => (hb la).2.2.2.1)
  exact ⟨key, fun _ => key⟩

end GlobalTheory.DepthSum
