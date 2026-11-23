import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProductStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBound

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.CoordBound

theorem split_of_dvd {D : D7} {Q Q' p : ℕ} [hp : Fact p.Prime] (hQ : GoodLevel D Q) (h0 : 0 < Q')
    (h : padicValNat p Q' ≤ padicValNat p Q) (hd : p ∣ Q') : SplitIn D p := by
  have hpp : p.Prime := hp.out
  obtain ⟨hQ0, hQs⟩ := hQ
  have h1 : 1 ≤ padicValNat p Q' := one_le_padicValNat_of_dvd h0.ne' hd
  have hpQ : p ^ 1 ∣ Q := (padicValNat_dvd_iff_le hQ0.ne').2 (h1.trans h)
  exact hQs p hpp (by simpa using hpQ)

open GlobalTheory.NormSum.Term in

theorem term_bound_of_jets (hJ : type_of% @GlobalTheory.T.jets_torsion_translates_cm_theta_product) (D : D7) (hI : Inp D) (S : Finset ℕ) (dl : ℕ → ℝ) (hL : Letters D S dl) (δ t0 : ℂ) (Q : ℕ)
    (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (hQ : p ∣ Q → SplitIn D p) (lam : Qbar →+* ℂ_[p]) (g : GA D P.a)
    (g' k' : GA D P.d) (hk : k' ∈ intG D P.d) (hg : TrivAt D p (g : GL (Fin P.a) (AE D)))
    (hg' : TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D))) (T) :
    P.term g g' T ∈ Qbar ∧ ‖lamC lam (P.term g g' T)‖ ≤ (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) *
      (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + ((P.a * P.d : ℕ) : ℝ) * (padicValNat p Q : ℝ)) := by
  classical
  obtain ⟨b, k, M, r, s, hOnB, hLoc, hM0, hMp, hLa, hr, hOm⟩ :=
    GlobalTheory.T.kernelAtPrime_eq_sum_torsionTranslates D hI δ t0 Q P.crv P.pt0 P.level_pos P p lam g g' k' hk hg hg'
  obtain ⟨-, -, -, -, hLk⟩ := hL
  have hpp : p.Prime := Fact.out
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hQ0 : Q ≠ 0 := P.level_pos.ne'
  have hM0' : M ≠ 0 := hM0.ne'
  have hpM : ¬ p ∣ M := fun h => hpp.one_lt.ne' (hMp.symm.eq_one_of_dvd h)
  have hvM : padicValNat p M = 0 := padicValNat.eq_zero_of_not_dvd hpM
  have hnQ : ‖(Q : ℂ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p Q : ℝ) := norm_natCast_inv p hQ0
  have hnMQ : ‖((M * Q : ℕ) : ℂ_[p])‖⁻¹ = (p : ℝ) ^ (padicValNat p Q : ℝ) := by
    rw [norm_natCast_inv p (Nat.mul_ne_zero hM0' hQ0), padicValNat.mul hM0' hQ0, hvM, zero_add]
  have hsplit : p ∣ M * Q → SplitIn D p := fun h =>
    (hpp.dvd_mul.1 h).elim (fun h' => absurd h' hpM) hQ
  set B : ℝ := (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) * (dl p + (if p = D.host.d then 1 / 4 else 0) +
    (padicValNat p Q : ℝ)) + ((P.a * P.d : ℕ) : ℝ) * (padicValNat p Q : ℝ)) with hBdef
  have hB : 0 ≤ B := Real.rpow_nonneg hp0.le _
  suffices H : Bd lam B (P.term g g' T) from H
  unfold Pair.term
  rw [← map_minorZ D T]
  refine bd_applyAt0 D hB _ _ (minorZ_homogeneous D T) ?_
  intro f
  rw [hOm]
  have hc := iteratedFDeriv_comb (P.a * ∑ τ, P.n τ) (fun i => (r i : ℂ))
    (fun i => U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0)))
    (fun i => contDiff_U_pullB D _ b _ (differentiable_evenTheta D ⊤ δ t0 P.crv) (s i) _)
    (fun i => coordV D (f i))
  beta_reduce at hc
  rw [hc]
  refine Bd.sum hB _ _ (fun i _ => ?_)
  have hjet := bd_coord D (A := (p : ℝ) ^ dl p)
    (B := (‖((M * Q : ℕ) : ℂ_[p])‖⁻¹) ^ (P.a * ∑ τ, P.n τ) *
      (if p = D.host.d then (p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) / 4) else 1))
    (Real.rpow_nonneg hp0.le _) (by split_ifs <;> positivity) (tor0 D ⊤ δ) (fun _ _ => rfl)
    (YYl D (stdL D P.a) (stdL D P.d)) (fun kk => hLk p lam P.a P.d kk)
    (iteratedFDeriv ℂ (P.a * ∑ τ, P.n τ)
      (U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0))) 0)
    (fun y hy => hJ D hI p lam ⊤ δ P.crv (by simp) t0 P.pt0 P.a P.d _ b hOnB hLoc (s i) (M * Q)
      (Nat.mul_pos hM0 P.level_pos) (hLa i) hsplit _ y hy) f
  have hri : Bd lam ((‖(Q : ℂ_[p])‖⁻¹) ^ (P.a * P.d)) ((r i : Qbar) : ℂ) := Bd.coe (hr i)
  refine (hri.mul hjet).mono (le_of_eq ?_)
  rw [hnQ, hnMQ, mul_left_comm, rpow_collect hp0]

theorem nonempty_place (p : ℕ) [Fact p.Prime] : Nonempty (Qbar →+* ℂ_[p]) := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[p])).toRingHom⟩

private theorem bd_finsum {p : ℕ} [Fact p.Prime] {ι : Type*} {r : ℝ} (hr : 0 ≤ r) (f : ι → ℂ)
    (h : ∀ i, GlobalTheory.NormVal.Bd p r (f i)) : GlobalTheory.NormVal.Bd p r (∑ᶠ i, f i) := by
  classical
  by_cases hf : (Function.support f).Finite
  · rw [finsum_eq_sum f hf]
    refine Finset.induction_on hf.toFinset ?_ ?_
    · simpa using GlobalTheory.NormVal.Bd.zero (p := p) hr
    · intro a t ha ih
      rw [Finset.sum_insert ha]
      exact (h a).add ih
  · rw [finsum_of_infinite_support hf]
    exact GlobalTheory.NormVal.Bd.zero hr

set_option maxHeartbeats 1000000 in
open GlobalTheory.NormVal in

theorem coordInt_of_jets (hJ : type_of% @GlobalTheory.T.jets_torsion_translates_cm_theta_product) (D : D7) (hI : Inp D) (S : Finset ℕ) (dl : ℕ → ℝ) (hL : Letters D S dl) (Q N : ℕ) (B : ℝ)
    (hQ : GoodLevel D Q) (_hB : 0 ≤ B) :
    CoordInt D N B Q (fun p => (padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) : ℝ) +
      4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) +
      4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ)) := by
  classical
  have hL' := hL
  obtain ⟨-, hdl0, -, -, -⟩ := hL'
  have hcard : Fintype.card D.what₂.Tau = fF D := (GlobalTheory.T.derivationDenominators_and_hostField_sizes D hI.g1).2.2.2.2.1
  unfold CoordInt
  intro δ t0 p _ Q' hQ' P hP
  obtain ⟨hPd, hPn⟩ := hP
  have hpp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hMN0 : 8 ^ (4 * fF D * N) * (8 * fF D * N).factorial ≠ 0 := by positivity
  have hvle : ∀ m : ℕ, m ∣ 8 ^ (4 * fF D * N) * (8 * fF D * N).factorial →
      padicValNat p m ≤ padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) := fun m hm =>
    (padicValNat_dvd_iff_le hMN0).1 ((pow_padicValNat_dvd (p := p) (n := m)).trans hm)
  have hvQ : (padicValNat p Q' : ℝ) ≤ padicValNat p Q := by exact_mod_cast hQ'
  have hite : (0 : ℝ) ≤ (if p = D.host.d then 1 / 4 else 0) := by split_ifs <;> norm_num
  have hX : 0 ≤ dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ) := by
    have := hdl0 p; positivity
  have hrest : 0 ≤ 4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) +
      4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ) := by positivity
  obtain ⟨hreps, hstab⟩ := reps_and_stabilisers P p
  refine ⟨hreps, fun h => ⟨(hstab h).1, ?_⟩, ?_⟩
  · have h1 := (hstab h).2
    have h2 := hvle _ (GlobalTheory.NormVal.order_dvd (f := fF D) hPd)
    have h3 : (padicValNat p (gam D P.J h) : ℝ) ≤
        padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) := by exact_mod_cast h1.trans h2
    linarith
  · intro h hInt T
    obtain ⟨k', hk', htriv⟩ := hInt
    have hrep : ∀ q : Cls D P.a (intG D P.a), ∃ x : GA D P.a,
        DoubleCoset.mk (ratG D P.a) (intG D P.a) x = q ∧ TrivAt D p (x : GL (Fin P.a) (AE D)) := by
      intro q
      obtain ⟨γA, k, γ, hγ, hk, htr⟩ := hI.rep P.a p hpp q.out
      refine ⟨γA * q.out * k, ?_, htr⟩
      have hγ' : γA ∈ ratG D P.a := (mem_ratG γA).2 ⟨γ, hγ⟩
      have hk' : k ∈ intG D P.a := (mem_intG k).2 hk
      have hq : DoubleCoset.mk (ratG D P.a) (intG D P.a) q.out = q := Quotient.out_eq' q
      exact ((DoubleCoset.eq (ratG D P.a) (intG D P.a) q.out (γA * q.out * k)).2
        ⟨γA, hγ', k, hk', rfl⟩).symm.trans hq
    choose s hs htr using hrep
    rw [(GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives D hI ⊤ δ t0 Q' P.crv P.pt0 P P.level_pos).2.2.1 s hs h T]
    have hsp : p ∣ Q' → SplitIn D p := split_of_dvd hQ P.level_pos hQ'
    have hS : ∑ τ, (P.n τ : ℝ) ≤ fF D * (2 * B) := by
      calc ∑ τ, (P.n τ : ℝ) ≤ ∑ _τ : D.what₂.Tau, 2 * B := Finset.sum_le_sum fun τ _ => hPn τ
        _ = fF D * (2 * B) := by rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    have hS0 : 0 ≤ ∑ τ, (P.n τ : ℝ) := Finset.sum_nonneg fun τ _ => Nat.cast_nonneg _
    have ha : (P.a : ℝ) ≤ 2 * N := by exact_mod_cast le_trans P.a_le hPd
    have hd : (P.d : ℝ) ≤ 2 * N := by exact_mod_cast hPd
    have han : ((P.a * ∑ τ, P.n τ : ℕ) : ℝ) ≤ 4 * fF D * N * B := by
      push_cast
      calc (P.a : ℝ) * ∑ τ, (P.n τ : ℝ) ≤ (2 * N) * (fF D * (2 * B)) :=
            mul_le_mul ha hS hS0 (by positivity)
        _ = 4 * fF D * N * B := by ring
    have had : ((P.a * P.d : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
      push_cast
      nlinarith [mul_le_mul ha hd (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * N)]
    refine bd_finsum (Real.rpow_nonneg hp0.le _) _ (fun q => ?_)
    have hg1 := GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant D P.a (intG D P.a) le_rfl (s q)
    have hdvd : gam D (intG D P.a) (s q) ∣ 8 ^ (4 * fF D * N) * (8 * fF D * N).factorial :=
      hg1.2.1.trans (GlobalTheory.NormVal.order_dvd (f := fF D) (le_trans P.a_le hPd))
    have hA := GlobalTheory.NormVal.Bd.inv_nat (p := p) hMN0 hdvd
    have tb := fun lam => term_bound_of_jets hJ D hI S dl hL δ t0 Q' P p hsp lam (s q) h k' hk' (htr q) htriv T
    obtain ⟨lam0⟩ := nonempty_place p
    have hTm : GlobalTheory.NormVal.Bd p ((p : ℝ) ^ (((P.a * ∑ τ, P.n τ : ℕ) : ℝ) *
        (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q' : ℝ)) +
        ((P.a * P.d : ℕ) : ℝ) * (padicValNat p Q' : ℝ))) (P.term (s q) h T) :=
      ⟨(tb lam0).1, fun lam => (tb lam).2⟩
    refine (hA.mul hTm).mono ?_
    rw [← Real.rpow_add hp0]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have hX' : 0 ≤ dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q' : ℝ) := by
      have := hdl0 p; positivity
    have e1 := mul_le_mul han (by linarith : dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q' : ℝ) ≤
      dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) hX' (by positivity)
    have e2 := mul_le_mul had hvQ (Nat.cast_nonneg _) (by positivity)
    linarith

theorem coordInt : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (Q N : ℕ) (B : ℝ), GoodLevel D Q → 0 ≤ B → CoordInt D N B Q (fun p => (padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) : ℝ) + 4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + 4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ)) :=
  fun D hI S dl hL Q N B hQ hB => coordInt_of_jets @GlobalTheory.T.jets_torsion_translates_cm_theta_product D hI S dl hL Q N B hQ hB

end GlobalTheory.NormSum.CoordBound
