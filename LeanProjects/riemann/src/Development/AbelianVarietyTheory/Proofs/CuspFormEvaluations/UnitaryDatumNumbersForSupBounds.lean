import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusFrame

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.SupDict

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  simp only [Ranks.f, Ranks.n]
  ring

theorem xiR_pos (D : D7) : 0 < xiR D := by
  unfold xiR
  refine norm_pos_iff.mpr ((map_ne_zero _).mpr ?_)
  have hd : (D.host.d : D.host.E) ≠ 0 := by
    have hlt := D.host.qd_big.2
    exact_mod_cast (Nat.zero_lt_of_lt hlt).ne'
  have hs : D.host.sqd ≠ 0 := by
    intro h0
    have h2 := D.host.sqd_sq
    rw [h0] at h2
    apply hd
    have h3 : -(D.host.d : D.host.E) = 0 := by rw [← h2]; ring
    exact neg_eq_zero.mp h3
  have hn : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  simp only [Host.xi0, Host.sqrtMinusD]
  exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) (mul_ne_zero hn hs)

theorem one_le_dE (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  unfold dE
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero E)

private lemma sum_ext0_le_sum {l : ℕ} (a : Fin l → ℕ) (M : ℕ) : ∑ i : Fin M, ext0 a (i : ℕ) ≤ ∑ i, a i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ext0 a i) M]
  have h1 : ∑ i ∈ Finset.range M, ext0 a i = ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with hi
    · rfl
    · simp [ext0, hi]
  have h2 : ∑ i ∈ (Finset.range M).filter (· < l), ext0 a i ≤ ∑ i ∈ Finset.range l, ext0 a i :=
    Finset.sum_le_sum_of_subset (fun i hi => by simp at hi ⊢; omega)
  have h3 : ∑ i ∈ Finset.range l, ext0 a i = ∑ i, a i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ext0 a i) l]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [ext0, i.isLt]
  omega

theorem record_dictionary : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), fdeg D.host.E = D.R.f ∧ Real.log (rdE D.host.E) = lrd D ∧ 1 ≤ rdE D.host.E ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ 0 < xiR D ∧ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ WeightAlgebra.DF w ∧ absA w = (WeightAlgebra.DF w : ℝ) ∧ (∀ σ, GoodEmb T.Q.c σ → ∀ k τ, ((T.U j σ).X k).c τ = 2 * xiR D) ∧ lieFac (T.Q.Dw j) (xiR D) (wtA w) = Real.exp (-(((Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) ∧ T.Q.l.A = 1 ∧ 0 < D.host.pde ∧ 0 < D.host.pde' ∧ ∀ (ι : Type) (σ : T.Q.c.F →+* ℂ) (P : MvPolynomial ι T.Q.c.F), l1At (goodOf T.Q.c σ) P = l1At σ P := by
  intro D T h j hj w
  have hfin := finrank_host D
  have hdpos : 0 < dE D.host.E := lt_of_lt_of_le one_pos (one_le_dE _)
  refine ⟨?_, ?_, ?_, ?_, ?_, xiR_pos D, ?_, ?_, ?_, ?_, ?_, D.host.pde_prime.pos, D.host.pde'_prime.pos, ?_⟩
  · unfold fdeg
    rw [hfin]
    omega
  · rw [rdE, Real.log_rpow hdpos, hfin, lrd, dE]
    push_cast
    ring
  · unfold rdE
    exact Real.one_le_rpow (one_le_dE _) (by positivity)
  · have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    simp only [Ranks.f, Ranks.n]
    omega
  · have h1 := D.R.two_le_m
    simp only [Ranks.r]
    omega
  · unfold wtA Formalism.L2.Pj.DF WeightAlgebra.DF WeightAlgebra.degP
    simp only [Finset.sum_add_distrib]
    apply add_le_add
    · rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_le_sum (fun t _ => ?_)
      rw [Finset.sum_eq_single (DV.tauEmb D t)]
      · simp only [↓reduceIte]
        exact sum_ext0_le_sum _ _
      · intro τ _ hτ
        simp [hτ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_le_sum (fun t _ => ?_)
      rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
      · simp only [↓reduceIte]
        exact sum_ext0_le_sum _ _
      · intro τ _ hτ
        simp [hτ]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
  · unfold absA WeightAlgebra.DF WeightAlgebra.degP
    push_cast
    rfl
  · intro σ hσ k τ
    unfold Data.c
    rw [h.xiAbs j hj σ hσ k τ.1]
  · unfold lieFac Formalism.L2.Pj.DF
    rw [show (2 : ℝ) * Real.pi * xiR D = Real.pi * (2 * xiR D) by ring]
    push_cast
    rfl
  · obtain ⟨-, hl, -, -⟩ := h.pins
    unfold Par.PinLevel at hl
    exact hl.2
  · intro ι σ P
    unfold l1At goodOf
    split_ifs with hg
    · rfl
    · simp only [RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.SupDict
