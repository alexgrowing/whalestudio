import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpsTuple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointPreservesHeckeEigenvectorsMatcheStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleSplitLabMemSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfSplitVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KeptRows
open GlobalTheory.Hk3

section Transfer
open Polynomial GlobalTheory.Hk3.SplitChain
open Formalism.L2.Col (heckePolyOf blockPoly)

theorem blockPoly_ne_zero (ν : ℂ) (q t : ℕ) : blockPoly ν q t ≠ 0 := by
  intro h
  have h0 : Polynomial.eval 0 (blockPoly ν q t) = 1 := by
    unfold blockPoly
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_one
    intro c _
    simp
  rw [h, eval_zero] at h0
  exact zero_ne_one h0

set_option maxHeartbeats 1000000 in

theorem transfer_good {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (hL : GlobalTheory.Chain.LiftInteg D) (hC : Core R F) (hS : SchurAll R) (t : T) (P : Pl D.host.E) (hG : Good R t P)
    (hP : Formalism.DivisionValues.conjPl P ≠ P) :
    ∃ (z : ℕ → ℕ → ℂ) (c : ℂ) (B : ℂ[X]), c ≠ 0 ∧ B ≠ 0 ∧
      (∀ k, k ≤ D.sp.X'.rank → MatchE R t P (Finsupp.single (splitLab D.sp.X'.rank k) 1) (splitC (Yc D 0).rank (z k))) ∧
      ∀ a : ℕ → ℂ, heckePolyOf D.sp.X'.rank (Ideal.absNorm P.asIdeal)
          (fun k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z k j * a j) =
        (heckePolyOf (Yc D 0).rank (Ideal.absNorm P.asIdeal) a).comp (C c * X) * B := by
  obtain ⟨q, hq⟩ : ∃ q, q = Ideal.absNorm P.asIdeal := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨-, g2, -, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  have hG' := (g2 t _ hG).2.1
  obtain ⟨u1, u2⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t _ hG
  obtain ⟨v1, v2⟩ := GlobalTheory.T.splittingCharacters_unramified_offLevels R F hC.lev t _ hG'
  have hm := D.R.two_le_m
  have hP' : conjPl (conjPl P) ≠ conjPl P := by rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]; exact hP.symm
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt (conjPl P) (by
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
    exact fun h => hP' (HeightOneSpectrum.ext h))
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ ∈ (conjPl P).asIdeal, ϖ ∉ (conjPl P).asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ (conjPl P).ne_bot (conjPl P).isPrime.ne_top 2 le_rfl)
  have h0 : (ϖ : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h => h2 (h ▸ zero_mem _)
  obtain ⟨x, hx⟩ : ∃ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) :=
    ⟨Formalism.L2.JoinChr.locU he.1.1 (Units.mk0 _ h0), by
      rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, Units.val_mk0]; ring⟩
  have hY : ∀ j, j ≤ D.R.m → (Yc D j).rank = D.R.r + j * D.R.t := fun j hj => by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]; rfl
  have hX : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
  have hn : ∀ j, D.R.r + (j + 1) * D.R.t = D.R.r + j * D.R.t + D.R.t := fun j => by ring
  let μ := R.toLevCh.mu t
  let ν : ℕ → ℂ := fun i => (((Lift.chrStep μ R.eta (i + 1)).1 x : ℂ) * (Real.sqrt q : ℂ) ^ (D.R.r + i * D.R.t))⁻¹
  let s : ℕ → ℂ := fun i => ν i * (((Lift.chrStep μ R.eta (i + 1)).2 x : ℂ) * (Real.sqrt q : ℂ) ^ (D.R.r + (i + 1) * D.R.t))
  obtain ⟨W, w0, w1⟩ := exists_chain D.R.m (fun j => D.R.r + j * D.R.t)
    fun j => stepMat q (D.R.r + j * D.R.t) D.R.t (ν j) (s j)
  have hmm : D.R.m - 1 + 1 = D.R.m := by omega
  have hfix : FixAll R t P := by
    refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
    · have := unrPl_step (u2 (k + 1) (by omega) hk.le) u1
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.chain.ωY t k hk) hP this.1 this.2).1
    · have := unrPl_step (u2 D.R.m (by omega) le_rfl) u1
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.chain.ωX t) hP this.1 this.2).1
    · have := u2 ((i : ℕ) + 1) (by omega) i.2
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.thP.ωP i t) hP this (unrPl_mul_inv this u1)).1
  have hσ : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq0)))
  have hs0 : ∀ i, s i ≠ 0 := fun i =>
    mul_ne_zero (inv_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ hσ)))
      (mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ hσ))
  refine ⟨W 0, ∏ i ∈ Finset.Ico 0 D.R.m, s i,
    ∏ i ∈ Finset.Ico 0 D.R.m, blockPoly (ν i * (q : ℂ) ^ (D.R.r + i * D.R.t) * ∏ l ∈ Finset.Ico (i + 1) D.R.m, s l) q D.R.t,
    Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, Finset.prod_ne_zero_iff.2 fun i _ => blockPoly_ne_zero _ _ _,
    fun k hk => ?_, fun a => ?_⟩
  · rw [hY 0 (Nat.zero_le _)]
    refine GlobalTheory.T.matchE_of_chainStep_matches R F hL hC hS t _ hG hfix _ (fun j => splitC (D.R.r + j * D.R.t) (W j k)) ?_ fun j hj => ?_
    · have hW := hC.chain.ωX t
      have h3 := step_match (ν := ν (D.R.m - 1)) (s := s (D.R.m - 1)) hW hP (unrPl_step (u2 D.R.m (by omega) le_rfl) u1)
        (unrPl_step (v2 D.R.m (by omega) le_rfl) v1) he h1 h2 hx (hY _ (Nat.sub_le _ _)) hX
        (by rw [← hn, hmm]) hq (by simp only [ν, hmm, μ]) (by simp only [s, hmm, μ]) (W D.R.m k)
      rw [funext (w0 k), ← hX, splitC_delta hk] at h3
      have h4 := funext (w1 (D.R.m - 1) (by omega) k)
      simp only [hmm] at h4
      rw [funext (w0 k), ← hX] at h4
      simp only [h4]
      exact h3
    · have h3 := step_match (ν := ν j) (s := s j) (hC.chain.ωY t j hj) hP (unrPl_step (u2 (j + 1) (by omega) hj.le) u1)
        (unrPl_step (v2 (j + 1) (by omega) hj.le) v1) he h1 h2 hx (hY _ (by omega)) (hY _ hj.le)
        (hn j) hq rfl rfl (W (j + 1) k)
      simp only [funext (w1 j (by omega) k)]
      exact h3
  · have h3 := chain_poly q D.R.t D.R.m (fun j => D.R.r + j * D.R.t) hn ν s W w0 w1 D.R.m 0 (zero_add _) a
    rw [hX, hY 0 (Nat.zero_le _), h3]

end Transfer

set_option maxHeartbeats 1000000 in

theorem kept : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Core R F → (∀ t P, Good R t P → Formalism.DivisionValues.conjPl P = P → FixAll R t P) → Kept R := by
  intro hCR hHU D G _ _ Pl0 T A Ks _ _ _ R F hC hFix t c x hx
  have hS : SchurAll R := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCR R
  have hLI := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCR D
  have H1 := GlobalTheory.Hk3.OpsRowsTuple.exists_ops_tuple R F hC hS t
  cases H1 with
  | intro h H2 =>
  have hh := H2.1
  have hn := H2.2.1
  have he := H2.2.2.1
  have hin := H2.2.2.2
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, map_zero]
    exact Submodule.zero_mem _
  have hxe : ∀ P, Good R t P → ∀ cc, h P cc x = evC (Yc D 0) P (fun d => c P (dualLab d)) cc • x :=
    fun P hP cc => he c P hP cc x hx
  have hmatch : ∀ P, Good R t P → ∀ cX c0, MatchE R t P cX c0 →
      h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) =
        evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • R.Th t (LinearMap.adjoint (R.Th t) x) :=
    fun P hP cX c0 hM => GlobalTheory.T.thetaLiftAdjoint_preserves_heckeEigenvectors_matchedPair R F hC t h hh hn P hP cX c0 hM x _ (hxe P hP c0)
  have evS : ∀ P d, IsLab (Yc D 0) P d →
      evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single d 1) = c P (dualLab d) := by
    intro P d hd
    unfold evC
    rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]
  have gp := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hsplit : ∀ P, Good R t P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank,
      h P (Finsupp.single (splitLab (Yc D 0).rank k) 1) (R.Th t (LinearMap.adjoint (R.Th t) x)) =
        evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) •
          R.Th t (LinearMap.adjoint (R.Th t) x) := by
    intro P hP hs k hk
    have HZ := transfer_good R F hLI hC hS t P hP hs
    cases HZ with
    | intro z Hz =>
    cases Hz with
    | intro c0 Hz =>
    cases Hz with
    | intro B Hz =>
    have hz := Hz.2.2.1
    have hq : Ideal.absNorm P.asIdeal ≠ 0 := fun e => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    have hspan := GlobalTheory.SpanPoly.single_splitLab_mem_span _ _ _ hq c0 Hz.1 B Hz.2.1 z Hz.2.2.2 k hk
    refine GlobalTheory.EigSpan.eig_span R F hC t h hh _ hP _ _ _ ?_ _ hspan
    rintro _ ⟨j, hj, rfl⟩
    exact hmatch _ hP _ _ (hz j hj)
  refine hin c (R.Th t (LinearMap.adjoint (R.Th t) x)) fun P d hP hd => ?_
  by_cases hs : Formalism.DivisionValues.conjPl P = P
  · have HM := (GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert hHU R F hLI hC hS t P hP hs (hFix t P hP hs)).1.2
      (Finsupp.single d 1)
    cases HM with
    | intro cX hM =>
    have e1 := hmatch P hP cX _ hM
    exact e1.trans (congrArg (fun z : ℂ => z • R.Th t (LinearMap.adjoint (R.Th t) x)) (evS P d hd))
  · have hcP : Good R t (Formalism.DivisionValues.conjPl P) := (gp.2.1 t P hP).2.1
    have hcs : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) ≠ Formalism.DivisionValues.conjPl P := by
      rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl P]
      exact fun e => hs e.symm
    exact GlobalTheory.Hk3.SplitLabels.eq_of_split_vec R F hC t h hh P hP hs c x _ hx0 hxe (fun k hk => ⟨hsplit P hP hs k hk, hsplit _ hcP hcs k hk⟩) d hd

end GlobalTheory.KeptRows

end
