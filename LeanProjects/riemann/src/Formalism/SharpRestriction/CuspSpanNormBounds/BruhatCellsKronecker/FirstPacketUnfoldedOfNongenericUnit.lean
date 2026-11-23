import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

section P29cRecord

variable (D : D7)

def ngLoop (u u' : D.what₂.Word) : Set (D.s.Pair u u') :=
  {p | p ∈ pairsIn D.s (famNG D.s) ∧ 2 ≤ D.s.s0 p}

def ngOne (u u' : D.what₂.Word) : Set (D.s.Pair u u') :=
  {p | p ∈ pairsIn D.s (famNG D.s) ∧ D.s.s0 p < 2}

theorem nongeneric_pairs_eq_loop_union_unit (u u' : D.what₂.Word) :
    (pairsIn D.s (famNG D.s) : Set (D.s.Pair u u')) = ngLoop D u u' ∪ ngOne D u u' := by
  ext p
  simp only [ngLoop, ngOne, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · intro h
    rcases le_or_gt 2 (D.s.s0 p) with h2 | h2
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr ⟨h, h2⟩
  · rintro (h | h) <;> exact h.1

theorem disjoint_nongeneric_loop_unit (u u' : D.what₂.Word) : Disjoint (ngLoop D u u') (ngOne D u u') :=
  Set.disjoint_left.2 fun _ h1 h2 => absurd h1.2 (not_le.2 h2.2)

theorem loop_pair_of_nongeneric_loop {u u' : D.what₂.Word} {p : D.s.Pair u u'} (h : p ∈ ngLoop D u u') : loopP D.s p :=
  ⟨h.1.1.2.1, h.1.2.2.1, Or.inl h.2⟩

theorem gamma_factor_pos (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) : 0 < gaG D := by
  rw [gaG_eq D h0 h1]
  have key : ∀ j : Fin 2, 0 < ∏ i ∈ Finset.Icc 1 D.R.k, ((D.host.g j : ℝ) ^ i - 1) := by
    intro j
    refine Finset.prod_pos fun i hi => ?_
    have hg : (2 : ℝ) ≤ (D.host.g j : ℝ) := by exact_mod_cast (D.host.g_prime j).two_le
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have : (1 : ℝ) < (D.host.g j : ℝ) ^ i := one_lt_pow₀ (by linarith) (by omega)
    linarith
  exact mul_pos (pow_pos (key 0) _) (pow_pos (key 1) _)

theorem cubic_factor_bounds (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) :
    0 ≤ UnitaryVolumeMass.f3 D ∧ UnitaryVolumeMass.f3 D ≤ Real.exp (3 * (D.R.f : ℝ)) := by
  unfold UnitaryVolumeMass.f3
  rw [finprod_typedPl D h0 h1 (fun q => 1 + 3 / q)]
  have key : ∀ j : Fin 2, 0 ≤ 1 + 3 / (D.host.g j : ℝ) ∧ 1 + 3 / (D.host.g j : ℝ) ≤ Real.exp (3 / 2) := by
    intro j
    have hg : (2 : ℝ) ≤ (D.host.g j : ℝ) := by exact_mod_cast (D.host.g_prime j).two_le
    have h3 : 3 / (D.host.g j : ℝ) ≤ 3 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hp : 0 ≤ 3 / (D.host.g j : ℝ) := by positivity
    refine ⟨by linarith, ?_⟩
    have := Real.add_one_le_exp (3 / 2 : ℝ)
    linarith
  refine ⟨mul_nonneg (pow_nonneg (key 0).1 _) (pow_nonneg (key 1).1 _), ?_⟩
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (3 / 2) ^ D.R.f * Real.exp (3 / 2) ^ D.R.f :=
        mul_le_mul (pow_le_pow_left₀ (key 0).1 (key 0).2 _) (pow_le_pow_left₀ (key 1).1 (key 1).2 _)
          (pow_nonneg (key 1).1 _) (by positivity)
    _ = Real.exp (3 * (D.R.f : ℝ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

def NGOneAt (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C : ℝ) : Prop :=
  Summable (fun p : ngOne D u u' => ‖D.s.pval p.1‖) ∧
  gaG D * (∑' p : ngOne D u u', D.s.pval p.1).re ≤
    (2 : ℝ) ^ (-((D.R.k : ℝ) - 2 * (D.R.rS : ℝ) - 5)) *
      Real.exp (C * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) *
      ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar

theorem Dstar_pos' (u : D.what₂.Word) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos

theorem nongeneric_loop_sum_bound (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) {u u' : D.what₂.Word} {c : ℝ}
    (hB : UnitaryVolumeMass.LoopPairSumBound D u u' c) :
    Summable (fun p : ngLoop D u u' => ‖D.s.pval p.1‖) ∧
    gaG D * ∑' p : ngLoop D u u', ‖D.s.pval p.1‖ ≤
      Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar := by
  have hg := gamma_factor_pos D h0 h1
  set R : ℝ := Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar with hR
  have hfin : ∀ s : Finset (ngLoop D u u'), ∑ p ∈ s, ‖D.s.pval p.1‖ ≤ R / gaG D := by
    intro s
    have h := hB (s.map (Function.Embedding.subtype _)) (by
      intro p hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_map.1 hp
      exact loop_pair_of_nongeneric_loop D q.2)
    rw [Finset.sum_map] at h
    rw [le_div_iff₀ hg, mul_comm]
    exact h
  have hs : Summable (fun p : ngLoop D u u' => ‖D.s.pval p.1‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hfin
  refine ⟨hs, ?_⟩
  have := hs.tsum_le_of_sum_le hfin
  rw [le_div_iff₀ hg, mul_comm] at this
  exact this

theorem first_packet_bound_of_unit_bounds (large₂ : SizeData₂ D) {cL c C : ℝ}
    (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1))
    (h2a : UnitaryVolumeMass.c2aG D) (hB3 : ∀ u u', UnitaryVolumeMass.LoopPairSumBound D u u' cL) (hN : ∀ u u', NGOneAt D large₂ u u' C)
    (hk : 3 ≤ (cL - c) * (D.R.k : ℝ) * Real.log (D.R.k : ℝ)) (hL : 3 ≤ (D.R.m : ℝ) ^ 5 * large₂.sc.L) :
    UnitaryVolumeMass.NonGenericKernelBound D large₂ c (C + 1) := by
  intro u u'
  obtain ⟨hA, hAb⟩ := nongeneric_loop_sum_bound D h0 h1 (hB3 u u')
  obtain ⟨hB, hBb⟩ := hN u u'
  have hg := gamma_factor_pos D h0 h1
  obtain ⟨hf0, hf1⟩ := cubic_factor_bounds D h0 h1
  have hdis := disjoint_nongeneric_loop_unit D u u'
  have hUn := HasSum.add_disjoint (f := fun q : D.s.Pair u u' => ‖D.s.pval q‖) hdis hA.hasSum hB.hasSum
  have hUc := HasSum.add_disjoint (f := fun q : D.s.Pair u u' => D.s.pval q) hdis
    (Summable.of_norm hA).hasSum (Summable.of_norm hB).hasSum
  have hsumP : Summable (fun p : (pairsIn D.s (famNG D.s) : Set (D.s.Pair u u')) => ‖D.s.pval p.1‖) := by
    rw [nongeneric_pairs_eq_loop_union_unit D u u']; exact hUn.summable
  have hts : (∑' p : (pairsIn D.s (famNG D.s) : Set (D.s.Pair u u')), D.s.pval p.1) =
      (∑' p : ngLoop D u u', D.s.pval p.1) + ∑' p : ngOne D u u', D.s.pval p.1 := by
    rw [nongeneric_pairs_eq_loop_union_unit D u u']; exact hUc.tsum_eq
  have hle := h2a u u' (famNG D.s) (Or.inr (Or.inl rfl)) (fun t ht => ht.2.1) hsumP
  rw [hts, Complex.add_re] at hle
  have hre : (∑' p : ngLoop D u u', D.s.pval p.1).re ≤ ∑' p : ngLoop D u u', ‖D.s.pval p.1‖ :=
    (Complex.re_le_norm _).trans (norm_tsum_le_tsum_norm hA)
  set Q : ℝ := ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar with hQ
  have hQ0 : 0 ≤ Q := div_nonneg (by positivity) (Dstar_pos' D u).le
  set X : ℝ := (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ) with hX
  set Y : ℝ := (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L with hY
  set P2 : ℝ := (2 : ℝ) ^ (-((D.R.k : ℝ) - 2 * (D.R.rS : ℝ) - 5)) with hP2
  have hP20 : 0 ≤ P2 := by positivity
  have hf : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have e1 : Real.exp (3 * (D.R.f : ℝ)) * Real.exp (-(cL * X)) ≤ Real.exp (-(c * X)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : 3 * (D.R.f : ℝ) ≤ ((cL - c) * (D.R.k : ℝ) * Real.log (D.R.k : ℝ)) * (D.R.f : ℝ) :=
      mul_le_mul_of_nonneg_right hk hf
    rw [hX]; nlinarith
  have e2 : Real.exp (3 * (D.R.f : ℝ)) * Real.exp (C * Y) ≤ Real.exp ((C + 1) * Y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : 3 * (D.R.f : ℝ) ≤ ((D.R.m : ℝ) ^ 5 * large₂.sc.L) * (D.R.f : ℝ) := mul_le_mul_of_nonneg_right hL hf
    rw [hY]; nlinarith
  have a1 : gaG D * (∑' p : ngLoop D u u', D.s.pval p.1).re ≤ Real.exp (-(cL * X)) * Q := by
    have := (mul_le_mul_of_nonneg_left hre hg.le).trans hAb
    rw [mul_div_assoc] at this
    have hx : cL * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ) = cL * X := by rw [hX]; ring
    rwa [hx] at this
  have a2 : gaG D * (∑' p : ngOne D u u', D.s.pval p.1).re ≤ P2 * Real.exp (C * Y) * Q := by
    have := hBb
    rw [mul_div_assoc] at this
    have hy : C * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L = C * Y := by rw [hY]; ring
    rwa [hy] at this
  have hx' : c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ) = c * X := by rw [hX]; ring
  have hy' : (C + 1) * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L = (C + 1) * Y := by rw [hY]; ring
  unfold UnitaryVolumeMass.Kng
  rw [hx', hy', mul_div_assoc]
  calc hsNormSq (KOf D.s u u' (famNG D.s))
      ≤ UnitaryVolumeMass.f3 D * gaG D * ((∑' p : ngLoop D u u', D.s.pval p.1).re + (∑' p : ngOne D u u', D.s.pval p.1).re) := hle
    _ = UnitaryVolumeMass.f3 D * (gaG D * (∑' p : ngLoop D u u', D.s.pval p.1).re +
          gaG D * (∑' p : ngOne D u u', D.s.pval p.1).re) := by ring
    _ ≤ UnitaryVolumeMass.f3 D * (Real.exp (-(cL * X)) * Q + P2 * Real.exp (C * Y) * Q) :=
        mul_le_mul_of_nonneg_left (add_le_add a1 a2) hf0
    _ ≤ Real.exp (3 * (D.R.f : ℝ)) * (Real.exp (-(cL * X)) * Q + P2 * Real.exp (C * Y) * Q) :=
        mul_le_mul_of_nonneg_right hf1 (by positivity)
    _ = (Real.exp (3 * (D.R.f : ℝ)) * Real.exp (-(cL * X))) * Q +
          P2 * (Real.exp (3 * (D.R.f : ℝ)) * Real.exp (C * Y)) * Q := by ring
    _ ≤ Real.exp (-(c * X)) * Q + P2 * Real.exp ((C + 1) * Y) * Q :=
        add_le_add (mul_le_mul_of_nonneg_right e1 hQ0)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hP20) hQ0)
    _ = (Real.exp (-(c * X)) + P2 * Real.exp ((C + 1) * Y)) * Q := by ring

theorem theorem_B_second_bound_of_large {C : ℝ} (hC : 64 ≤ C) : UniformConstantsAndStatements.ConjugateSelfDualCharacter D C := BesselShellMomentBounds.theorem_B_second_bound_ge_64 D C hC

theorem theorem_B_first_bound_of_one_place {Ch Cg CK : ℝ} {A : ℕ} (hCg : 2 ≤ Cg)
    (hO : BesselShellMomentBounds.OnePlace D Ch Cg 0 (fun _ _ _ _ => True) A CK 4 0) : UniformConstantsAndStatements.TelescopingFormStatement D Ch Cg (CK + 6) :=
  BesselShellMomentBounds.theorem_B_first_bound_one_place hCg hO

theorem theorem_B_third_bound_of_one_place {Aw Ch Cg CK : ℝ} {A : ℕ} (hCg : 2 ≤ Cg)
    (hO : BesselShellMomentBounds.OnePlace D Ch Cg 0
      (fun _ _ _ X => ∀ v, ThB.AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) A CK 5
      (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) : UniformConstantsAndStatements.TheoremBWeightedBound D Aw Ch Cg (CK + 6) :=
  BesselShellMomentBounds.theorem_B_weighted_bound_one_place hCg hO

theorem bessel_datum_character_eq {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : ThB.BData D Ch Cg T T' b dist) (v : D.what₂.Tau) :
    (X.L v).c = cOfDpsi ((Bridge.kaS D : ℝ) : ℂ) := (X.hL v).2.2.1

theorem NGOneAt_of_pairAbs (large₂ : SizeData₂ D) {u u' : D.what₂.Word} {C : ℝ}
    (hS : Summable (fun p : D.s.Pair u u' => ‖D.s.pval p‖))
    (hb : gaG D * (∑' p : ngOne D u u', D.s.pval p.1).re ≤
      (2 : ℝ) ^ (-((D.R.k : ℝ) - 2 * (D.R.rS : ℝ) - 5)) *
        Real.exp (C * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar) : NGOneAt D large₂ u u' C :=
  ⟨hS.subtype _, hb⟩

theorem second_packet_bound_of_summable (large₂ : SizeData₂ D) {C : ℝ}
    (hS : ∀ u : D.what₂.Word, Summable (fun p : D.s.Pair u u => ‖D.s.pval p‖))
    (hb : ∀ u : D.what₂.Word, ‖(gaG D : ℂ) * ∑' p : UnitaryVolumeMass.scalG D u u, D.s.pval p.1‖ ≤
      Real.exp (C * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) * (D.duS u : ℝ) ^ 2 / D.what₂.Dstar) :
    UnitaryVolumeMass.GenericScalarPairSum D large₂ C :=
  fun u => ⟨(Summable.of_norm (hS u)).subtype _, hb u⟩

theorem loop_hypothesis_of_scale_le (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hm : Cl ≤ C' * (D.R.m : ℝ)) (hk3 : (3 : ℝ) ≤ (D.R.k : ℝ)) :
    Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) ≤ (D.R.k : ℝ) * Real.log (D.R.k : ℝ) := by
  obtain ⟨h1, h2, h3, _⟩ := hH
  have hC' : 0 < C' := by have := large₂.CGam_pos; linarith
  have hL : 0 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by have := large₂.sc.one_lt_alt; linarith) _
  have hm2 : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
  have hf : (D.R.m : ℝ) ^ 4 ≤ (D.R.f : ℝ) := by exact_mod_cast h3
  have hlog : 1 ≤ Real.log (D.R.k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := by linarith
  have s1 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * Real.log (D.R.k : ℝ) := by nlinarith
  have hm6 : 0 ≤ (D.R.m : ℝ) ^ 6 * large₂.sc.L := by positivity
  have s2 : C' * (D.R.m : ℝ) ^ 5 * (D.R.m : ℝ) ^ 4 * large₂.sc.L ≤ C' * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul_of_nonneg_left hf (by positivity)
  have s3 : Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) ≤ C' * (D.R.m : ℝ) ^ 5 * (D.R.m : ℝ) ^ 4 * large₂.sc.L := by
    have e : C' * (D.R.m : ℝ) ^ 5 * (D.R.m : ℝ) ^ 4 * large₂.sc.L =
        (C' * (D.R.m : ℝ) * (D.R.m : ℝ) ^ 2) * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hm6
    have hp : 0 ≤ C' * (D.R.m : ℝ) := by positivity
    have h4 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    nlinarith
  linarith [h2]

end P29cRecord

section Chain

open scoped ENNReal

theorem cauchy_schwarz_weighted_tsum {ι : Type} (x W : ι → ℝ≥0∞) (h0 : ∀ i, W i ≠ 0) (ht : ∀ i, W i ≠ ⊤) :
    (∑' i, x i) ^ 2 ≤ (∑' i, (W i)⁻¹) * ∑' i, W i * x i ^ 2 := by
  let _ : MeasurableSpace ι := ⊤
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.Measure.count : MeasureTheory.Measure ι) hpq
    (f := fun i => (W i) ^ (-(1 / 2 : ℝ))) (g := fun i => (W i) ^ (1 / 2 : ℝ) * x i)
    (measurable_from_top.aemeasurable) (measurable_from_top.aemeasurable)
  simp only [MeasureTheory.lintegral_count, Pi.mul_apply] at H
  have e1 : ∀ i, (W i) ^ (-(1 / 2 : ℝ)) * ((W i) ^ (1 / 2 : ℝ) * x i) = x i := by
    intro i
    rw [← mul_assoc, ← ENNReal.rpow_add _ _ (h0 i) (ht i)]
    norm_num
  have e2 : ∀ i, ((W i) ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) = (W i)⁻¹ := by
    intro i
    rw [← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_neg_one]
  have e3 : ∀ i, ((W i) ^ (1 / 2 : ℝ) * x i) ^ (2 : ℝ) = W i * x i ^ 2 := by
    intro i
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  simp only [e1, e2, e3] at H
  calc (∑' i, x i) ^ 2 ≤ ((∑' i, (W i)⁻¹) ^ (1 / 2 : ℝ) * (∑' i, W i * x i ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' H 2
    _ = (∑' i, (W i)⁻¹) * ∑' i, W i * x i ^ 2 := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

theorem weighted_cauchy_schwarz_chain {Cls Pt : Type} (wC : Cls → ℝ≥0∞) (t a : Cls → Pt → ℝ≥0∞) (nu J W M : Pt → ℝ≥0∞)
    (h0 : ∀ γ, W γ ≠ 0) (ht : ∀ γ, W γ ≠ ⊤)
    (h1 : ∀ c γ, t c γ ^ 2 ≤ nu γ * a c γ * J γ)
    (h2 : ∀ γ, nu γ * ∑' c, wC c * a c γ ≤ M γ) :
    ∑' c, wC c * (∑' γ, t c γ) ^ 2 ≤ (∑' γ, (W γ)⁻¹) * ∑' γ, W γ * M γ * J γ := by
  have step : ∀ c, wC c * (∑' γ, t c γ) ^ 2 ≤
      (∑' γ, (W γ)⁻¹) * ∑' γ, wC c * (W γ * (nu γ * a c γ * J γ)) := by
    intro c
    calc wC c * (∑' γ, t c γ) ^ 2 ≤ wC c * ((∑' γ, (W γ)⁻¹) * ∑' γ, W γ * t c γ ^ 2) :=
          mul_le_mul' le_rfl (cauchy_schwarz_weighted_tsum _ _ h0 ht)
      _ ≤ wC c * ((∑' γ, (W γ)⁻¹) * ∑' γ, W γ * (nu γ * a c γ * J γ)) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun γ => mul_le_mul' le_rfl (h1 c γ)))
      _ = (∑' γ, (W γ)⁻¹) * ∑' γ, wC c * (W γ * (nu γ * a c γ * J γ)) := by
          rw [ENNReal.tsum_mul_left]; ring
  calc ∑' c, wC c * (∑' γ, t c γ) ^ 2
      ≤ ∑' c, (∑' γ, (W γ)⁻¹) * ∑' γ, wC c * (W γ * (nu γ * a c γ * J γ)) := ENNReal.tsum_le_tsum step
    _ = (∑' γ, (W γ)⁻¹) * ∑' γ, ∑' c, wC c * (W γ * (nu γ * a c γ * J γ)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
    _ = (∑' γ, (W γ)⁻¹) * ∑' γ, W γ * (nu γ * ∑' c, wC c * a c γ) * J γ := by
        congr 1
        refine tsum_congr fun γ => ?_
        have : ∀ c, wC c * (W γ * (nu γ * a c γ * J γ)) = (W γ * nu γ * J γ) * (wC c * a c γ) := fun c => by ring
        simp_rw [this]
        rw [ENNReal.tsum_mul_left]; ring
    _ ≤ (∑' γ, (W γ)⁻¹) * ∑' γ, W γ * M γ * J γ :=
        mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun γ =>
          mul_le_mul' (mul_le_mul' le_rfl (h2 γ)) le_rfl)

variable (D : D7)

abbrev PtB (u u' : D.what₂.Word) : Type :=
  {γ : Point D.host.E (D.R.rS + 1) // ThB.IsBPt D (Lat.Tu D u) (Lat.Tu D u') γ}

structure NGObj (u u' : D.what₂.Word) : Type 1 where
  Cls : Type
  wC : Cls → ℝ≥0∞
  t : Cls → PtB D u u' → ℝ≥0∞
  a : Cls → PtB D u u' → ℝ≥0∞
  nu : PtB D u u' → ℝ≥0∞
  Jsq : PtB D u u' → ℝ≥0∞

variable {D} {u u' : D.what₂.Word}

def StepClass (O : NGObj D u u') (S : ℝ) : Prop :=
  ENNReal.ofReal S ≤ ∑' c, O.wC c * (∑' γ, O.t c γ) ^ 2 ∧ ∀ c γ, O.t c γ ^ 2 ≤ O.nu γ * O.a c γ * O.Jsq γ

def StepMean (O : NGObj D u u') (G1 cc p : ℝ) : Prop :=
  ∀ γ : PtB D u u', O.nu γ * ∑' c, O.wC c * O.a c γ ≤
    ENNReal.ofReal (G1 * cc * (ptWeightG D (rhoReal D) (Lat.Tu D u) (Lat.Tu D u') γ.1.1 *
      ThB.normWt D (Lat.Tu D u) (Lat.Tu D u') γ.1 ^ p))

def StepB (O : NGObj D u u') (p B2 : ℝ) (MM : ℝ≥0∞) : Prop :=
  ∑' γ : PtB D u u', ENNReal.ofReal (ThB.wPt D γ.1 * ptWeightG D (rhoReal D) (Lat.Tu D u) (Lat.Tu D u') γ.1.1 *
      ThB.normWt D (Lat.Tu D u) (Lat.Tu D u') γ.1 ^ p) * O.Jsq γ ≤ ENNReal.ofReal B2 * MM

theorem weighted_sum_bound_of_factor_estimates (O : NGObj D u u') {S G1 cc p B2 B3 B4 : ℝ} {MM : ℝ≥0∞}
    (hG1 : 0 ≤ G1) (hcc : 0 ≤ cc) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3) (hB4 : 0 ≤ B4) (hg : 0 ≤ gaG D)
    (h1 : StepClass O S) (h24 : StepMean O G1 cc p) (hB : StepB O p B2 MM)
    (h7b : ∑' γ : PtB D u u', ENNReal.ofReal (ThB.wPt D γ.1)⁻¹ ≤ ENNReal.ofReal B3)
    (hM : ENNReal.ofReal (gaG D * cc) * MM ≤ ENNReal.ofReal B4) :
    gaG D * S ≤ G1 * B2 * B3 * B4 := by
  have hw : ∀ γ : PtB D u u', 0 < ThB.wPt D γ.1 := fun γ => BesselShellMomentBounds.wPt_pos D γ.1
  have hch := weighted_cauchy_schwarz_chain O.wC O.t O.a O.nu O.Jsq (fun γ => ENNReal.ofReal (ThB.wPt D γ.1))
    (fun γ => ENNReal.ofReal (G1 * cc * (ptWeightG D (rhoReal D) (Lat.Tu D u) (Lat.Tu D u') γ.1.1 *
      ThB.normWt D (Lat.Tu D u) (Lat.Tu D u') γ.1 ^ p)))
    (fun γ => (ENNReal.ofReal_pos.2 (hw γ)).ne') (fun γ => ENNReal.ofReal_ne_top) h1.2 h24
  have e1 : ∀ γ : PtB D u u', (ENNReal.ofReal (ThB.wPt D γ.1))⁻¹ = ENNReal.ofReal (ThB.wPt D γ.1)⁻¹ :=
    fun γ => (ENNReal.ofReal_inv_of_pos (hw γ)).symm
  have e2 : ∀ γ : PtB D u u', ENNReal.ofReal (ThB.wPt D γ.1) *
      ENNReal.ofReal (G1 * cc * (ptWeightG D (rhoReal D) (Lat.Tu D u) (Lat.Tu D u') γ.1.1 *
        ThB.normWt D (Lat.Tu D u) (Lat.Tu D u') γ.1 ^ p)) * O.Jsq γ =
      ENNReal.ofReal (G1 * cc) * (ENNReal.ofReal (ThB.wPt D γ.1 *
        ptWeightG D (rhoReal D) (Lat.Tu D u) (Lat.Tu D u') γ.1.1 *
        ThB.normWt D (Lat.Tu D u) (Lat.Tu D u') γ.1 ^ p) * O.Jsq γ) := by
    intro γ
    rw [ENNReal.ofReal_mul (mul_nonneg hG1 hcc), mul_assoc (ThB.wPt D γ.1), ENNReal.ofReal_mul (hw γ).le]
    ring
  simp_rw [e1, e2] at hch
  rw [ENNReal.tsum_mul_left] at hch
  have hfin : ENNReal.ofReal (gaG D * S) ≤ ENNReal.ofReal (G1 * B2 * B3 * B4) := by
    calc ENNReal.ofReal (gaG D * S) = ENNReal.ofReal (gaG D) * ENNReal.ofReal S := ENNReal.ofReal_mul hg
      _ ≤ ENNReal.ofReal (gaG D) * (ENNReal.ofReal B3 * (ENNReal.ofReal (G1 * cc) * (ENNReal.ofReal B2 * MM))) :=
          mul_le_mul' le_rfl ((h1.1.trans hch).trans (mul_le_mul' h7b (mul_le_mul' le_rfl hB)))
      _ = ENNReal.ofReal G1 * ENNReal.ofReal B2 * ENNReal.ofReal B3 * (ENNReal.ofReal (gaG D * cc) * MM) := by
          rw [ENNReal.ofReal_mul hG1, ENNReal.ofReal_mul hg]; ring
      _ ≤ ENNReal.ofReal G1 * ENNReal.ofReal B2 * ENNReal.ofReal B3 * ENNReal.ofReal B4 := mul_le_mul' le_rfl hM
      _ = ENNReal.ofReal (G1 * B2 * B3 * B4) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hG1]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin

end Chain

section Assembly

open scoped ENNReal
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def MainCount (D : D7) (u u' : D.what₂.Word) (C cInf : ℝ) (constP : HeightOneSpectrum (𝓞 D.host.F) → ℝ)
    (dens : Cnt.GramM D → HeightOneSpectrum (𝓞 D.host.F) → ℝ) : Prop :=
  0 < cInf ∧ (∀ p, 0 < constP p) ∧ Multipliable constP ∧ 0 < ∏' p, constP p ∧
  (∀ Z p, |dens Z p - 1| ≤ C * (Ideal.absNorm p.asIdeal : ℝ) ^ (-((D.R.k : ℝ) - 2 * D.R.rS - 3))) ∧
  (∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
    ∀ what₂ : Finset (Cnt.LatV D), IsRowReps D F0 what₂ →
    ∀ Z : Cnt.GramM D, (∀ τ, 0 < Cnt.Gz D (Tr D u) (Tr D u') Z τ) →
      (∃ Λ ∈ what₂, ∃ F' : Cnt.FlagU D u', UniformConstantsAndStatements.IsNormFrame D Λ (lf D F0) F' ∧ Lat.ZhatL (lf D F0) F' = Z) →
      Multipliable (dens Z) ∧
      UniformConstantsAndStatements.nuTot D u u' F0 what₂ Z =
        ENNReal.ofReal (cInf * (∏' p, constP p) * (∏' p, dens Z p) *
          ∏ τ, Cnt.Gz D (Tr D u) (Tr D u') Z τ ^ ((D.R.k : ℝ) - 1)))

theorem size_product_bound (D : D7) (large₂ : SizeData₂ D) {K Cb secondBesselConstant Cn CM e θ gain Q : ℝ}
    (hK : 0 ≤ K) (hCB2 : 1 ≤ secondBesselConstant) (hCn : 0 ≤ Cn) (hCM : 0 ≤ CM) (he0 : 0 ≤ e) (he : e ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2)) (hgain : 0 ≤ gain) (hQ : 0 ≤ Q) :
    gain * large₂.sc.b ^ (K * (D.R.m : ℝ) ^ 4 * (D.R.f : ℝ)) * Real.exp (Cb * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) *
        secondBesselConstant ^ (D.R.f * (D.R.rS + 1)) *
        (θ ^ (2 * D.R.f) * large₂.sc.b ^ (CM * (D.R.m : ℝ) ^ 2 * (D.R.f : ℝ)) * ((1 + e) * Q)) ≤
      gain * Real.exp ((K + Cb + Real.log secondBesselConstant + 2 * Cn + CM + 1) * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) * Q := by
  have hb : ∀ t : ℝ, large₂.sc.b ^ t = Real.exp (large₂.sc.L * t) := fun t => by unfold Scale.b; rw [Real.exp_mul]
  have hL1 : 1 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hm2 : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by linarith
  have hf1 : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := by
      have h1 : 0 < D.R.n := D.R.ord_pos
      have h2 : D.R.f = 2 * D.R.n := rfl
      omega
    exact_mod_cast this
  have hf0 : (0 : ℝ) ≤ (D.R.f : ℝ) := by linarith
  set y : ℝ := (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L with hy
  have hm45 : (D.R.m : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm25 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm15 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
    calc (D.R.m : ℝ) = (D.R.m : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hm1 (by norm_num)
  have y4 : (D.R.m : ℝ) ^ 4 * (D.R.f : ℝ) * large₂.sc.L ≤ y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm45 hf0) hL0
  have y2 : (D.R.m : ℝ) ^ 2 * (D.R.f : ℝ) * large₂.sc.L ≤ y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm25 hf0) hL0
  have y1 : 1 ≤ y := by
    have h5 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ hm1
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ y := mul_le_mul (mul_le_mul h5 hf1 (by norm_num) (by linarith)) hL1 (by norm_num) (by positivity)
  have F1 : large₂.sc.b ^ (K * (D.R.m : ℝ) ^ 4 * (D.R.f : ℝ)) ≤ Real.exp (K * y) := by
    rw [hb]; apply Real.exp_le_exp.2
    calc large₂.sc.L * (K * (D.R.m : ℝ) ^ 4 * (D.R.f : ℝ)) = K * ((D.R.m : ℝ) ^ 4 * (D.R.f : ℝ) * large₂.sc.L) := by ring
      _ ≤ K * y := mul_le_mul_of_nonneg_left y4 hK
  have F4b : large₂.sc.b ^ (CM * (D.R.m : ℝ) ^ 2 * (D.R.f : ℝ)) ≤ Real.exp (CM * y) := by
    rw [hb]; apply Real.exp_le_exp.2
    calc large₂.sc.L * (CM * (D.R.m : ℝ) ^ 2 * (D.R.f : ℝ)) = CM * ((D.R.m : ℝ) ^ 2 * (D.R.f : ℝ) * large₂.sc.L) := by ring
      _ ≤ CM * y := mul_le_mul_of_nonneg_left y2 hCM
  have hr : ((D.R.rS + 1 : ℕ) : ℝ) ≤ (D.R.m : ℝ) := by
    have : D.R.rS + 1 ≤ D.R.m := by
      have := D.R.two_le_m
      unfold Ranks.rS; omega
    exact_mod_cast this
  have F3 : secondBesselConstant ^ (D.R.f * (D.R.rS + 1)) ≤ Real.exp (Real.log secondBesselConstant * y) := by
    have hlog : 0 ≤ Real.log secondBesselConstant := Real.log_nonneg hCB2
    conv_lhs => rw [← Real.exp_log (show 0 < secondBesselConstant by linarith)]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hn : ((D.R.f * (D.R.rS + 1) : ℕ) : ℝ) ≤ y := by
      push_cast
      have h1 : (D.R.f : ℝ) * ((D.R.rS : ℝ) + 1) ≤ (D.R.f : ℝ) * (D.R.m : ℝ) ^ 5 := by
        apply mul_le_mul_of_nonneg_left _ hf0
        have : ((D.R.rS : ℝ) + 1) ≤ (D.R.m : ℝ) := by exact_mod_cast hr
        linarith
      have h2 : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 5 ≤ y := by
        rw [hy]
        have : 0 ≤ (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) := by positivity
        nlinarith
      linarith
    calc ((D.R.f * (D.R.rS + 1) : ℕ) : ℝ) * Real.log secondBesselConstant ≤ y * Real.log secondBesselConstant := mul_le_mul_of_nonneg_right hn hlog
      _ = Real.log secondBesselConstant * y := by ring
  have F4a : θ ^ (2 * D.R.f) ≤ Real.exp (2 * Cn * y) := by
    calc θ ^ (2 * D.R.f) ≤ (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2)) ^ (2 * D.R.f) := pow_le_pow_left₀ hθ0 hθ _
      _ = Real.exp (((2 * D.R.f : ℕ) : ℝ) * (large₂.sc.L * (Cn * (D.R.m : ℝ) ^ 2))) := by rw [hb, ← Real.exp_nat_mul]
      _ ≤ Real.exp (2 * Cn * y) := by
          apply Real.exp_le_exp.2
          push_cast
          calc 2 * (D.R.f : ℝ) * (large₂.sc.L * (Cn * (D.R.m : ℝ) ^ 2)) =
                2 * Cn * ((D.R.m : ℝ) ^ 2 * (D.R.f : ℝ) * large₂.sc.L) := by ring
            _ ≤ 2 * Cn * y := mul_le_mul_of_nonneg_left y2 (by positivity)
  have F4c : 1 + e ≤ Real.exp y := by
    have := Real.add_one_le_exp y
    linarith
  have e5 : Cb * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L = Cb * y := by rw [hy]; ring
  have e6 : (K + Cb + Real.log secondBesselConstant + 2 * Cn + CM + 1) * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L =
      K * y + Cb * y + Real.log secondBesselConstant * y + (2 * Cn * y + CM * y + y) := by rw [hy]; ring
  rw [e5, e6, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
  have hb0 : ∀ t : ℝ, 0 ≤ large₂.sc.b ^ t := fun t => by rw [hb]; positivity
  calc gain * large₂.sc.b ^ (K * (D.R.m : ℝ) ^ 4 * (D.R.f : ℝ)) * Real.exp (Cb * y) * secondBesselConstant ^ (D.R.f * (D.R.rS + 1)) *
        (θ ^ (2 * D.R.f) * large₂.sc.b ^ (CM * (D.R.m : ℝ) ^ 2 * (D.R.f : ℝ)) * ((1 + e) * Q))
      ≤ gain * Real.exp (K * y) * Real.exp (Cb * y) * Real.exp (Real.log secondBesselConstant * y) *
        (Real.exp (2 * Cn * y) * Real.exp (CM * y) * (Real.exp y * Q)) := by
        have := hb0 (K * (D.R.m : ℝ) ^ 4 * (D.R.f : ℝ))
        have := hb0 (CM * (D.R.m : ℝ) ^ 2 * (D.R.f : ℝ))
        gcongr
    _ = gain * (Real.exp (K * y) * Real.exp (Cb * y) * Real.exp (Real.log secondBesselConstant * y) *
        (Real.exp (2 * Cn * y) * Real.exp (CM * y) * Real.exp y)) * Q := by ring

theorem nongeneric_object_bound_of_estimates {D : D7} (large₂ : SizeData₂ D) (h : UniformConstantsAndStatements.LargenessConstants) {u u' : D.what₂.Word} {Cn : ℝ} {X : TermTie D}
    (Y : LoopTie D large₂ X u u' Cn) (μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (hsec : ∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (μsec τ))
    {CM Ce secondBesselConstant S gain K A Cb : ℝ} (hH : UniformConstantsAndStatements.Hyp D large₂ h) (h8 : UniformConstantsAndStatements.adm8 D large₂ h CM Ce) (h7b : UniformConstantsAndStatements.ConjugateSelfDualCharacter D secondBesselConstant)
    (O : NGObj D u u') (h1 : StepClass O S)
    (h24 : ∀ cInf constP dens, MainCount D u u' CM cInf constP dens →
      StepMean O (gain * large₂.sc.b ^ (K * (D.R.m : ℝ) ^ 4 * (D.R.f : ℝ))) (cInf * ∏' p, constP p)
        (A * ((D.R.rS : ℝ) + 1) ^ 2))
    (hB : StepB O (A * ((D.R.rS : ℝ) + 1) ^ 2) (Real.exp (Cb * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L))
      (∏ τ, MMv D u u' (Y.A τ) (μsec τ)))
    (hgain : 0 ≤ gain) (hK : 0 ≤ K) (hCB2 : 1 ≤ secondBesselConstant) (hCn : 0 ≤ Cn) (hCM : 0 ≤ CM)
    (he0 : 0 ≤ eSum D Ce) (he : eSum D Ce ≤ 1) :
    gaG D * S ≤ gain * Real.exp ((K + Cb + Real.log secondBesselConstant + 2 * Cn + CM + 1) * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) *
      ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar := by
  obtain ⟨cInf, constP, dens, a1, a2, a3, a4, a5, a6, a7⟩ := h8 hH u u'
  have hD : StandingNumericalData D h.C0 := hH.1
  have hg := gamma_factor_pos D hD.2.2.2.2.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.2.2.2.2.1
  have hbpos : 0 < large₂.sc.b := by unfold Scale.b; positivity
  have hθ0 : 0 < Y.θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hbpos _) Y.θ_win.1
  have hM := a7 Y.θ hθ0 Y.W Y.goodW Y.A Y.goodS Y.deg_eq μsec hsec
  have hT : 1 ≤ Lat.Tu D u := (D.mem u).A.T_prime.one_lt.le
  have hT' : 1 ≤ Lat.Tu D u' := (D.mem u').A.T_prime.one_lt.le
  have h7 := h7b (Lat.Tu D u) (Lat.Tu D u') hT hT'
  set Q : ℝ := ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar with hQ
  have hQ0 : 0 ≤ Q := div_nonneg (by positivity) (Dstar_pos' D u).le
  rw [D.what₂.card_Tau] at hM h7
  have hrow := weighted_sum_bound_of_factor_estimates O (B4 := Y.θ ^ (2 * D.R.f) * large₂.sc.b ^ (CM * (D.R.m : ℝ) ^ 2 * (D.R.f : ℝ)) *
      ((1 + eSum D Ce) * ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar))
    (mul_nonneg hgain (Real.rpow_nonneg hbpos.le _)) (mul_pos a1 a4).le (Real.exp_pos _).le
    (pow_nonneg (by linarith) _)
    (by
      rw [mul_div_assoc]
      have : 0 ≤ large₂.sc.b ^ (CM * (D.R.m : ℝ) ^ 2 * (D.R.f : ℝ)) := Real.rpow_nonneg hbpos.le _
      positivity)
    hg.le h1 (h24 cInf constP dens ⟨a1, a2, a3, a4, a5, a6⟩) hB h7 hM
  rw [mul_div_assoc]
  refine hrow.trans ?_
  rw [mul_div_assoc (1 + eSum D Ce)]
  exact size_product_bound D large₂ hK hCB2 hCn hCM he0 he hθ0.le Y.θ_win.2 hgain hQ0

theorem nongeneric_unit_bound_of_estimates {D : D7} (large₂ : SizeData₂ D) (h : UniformConstantsAndStatements.LargenessConstants) {u u' : D.what₂.Word} {Cn : ℝ} {X : TermTie D}
    (Y : LoopTie D large₂ X u u' Cn) (μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (hsec : ∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (μsec τ))
    {CM Ce secondBesselConstant K A Cb : ℝ} (hH : UniformConstantsAndStatements.Hyp D large₂ h) (h8 : UniformConstantsAndStatements.adm8 D large₂ h CM Ce) (h7b : UniformConstantsAndStatements.ConjugateSelfDualCharacter D secondBesselConstant)
    (O : NGObj D u u') (h1 : StepClass O (∑' p : ngOne D u u', D.s.pval p.1).re)
    (h24 : ∀ cInf constP dens, MainCount D u u' CM cInf constP dens →
      StepMean O ((2 : ℝ) ^ (-((D.R.k : ℝ) - 2 * (D.R.rS : ℝ) - 5)) * large₂.sc.b ^ (K * (D.R.m : ℝ) ^ 4 * (D.R.f : ℝ)))
        (cInf * ∏' p, constP p) (A * ((D.R.rS : ℝ) + 1) ^ 2))
    (hB : StepB O (A * ((D.R.rS : ℝ) + 1) ^ 2) (Real.exp (Cb * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L))
      (∏ τ, MMv D u u' (Y.A τ) (μsec τ)))
    (hK : 0 ≤ K) (hCB2 : 1 ≤ secondBesselConstant) (hCn : 0 ≤ Cn) (hCM : 0 ≤ CM) (he0 : 0 ≤ eSum D Ce) (he : eSum D Ce ≤ 1) :
    gaG D * (∑' p : ngOne D u u', D.s.pval p.1).re ≤
      (2 : ℝ) ^ (-((D.R.k : ℝ) - 2 * (D.R.rS : ℝ) - 5)) *
        Real.exp ((K + Cb + Real.log secondBesselConstant + 2 * Cn + CM + 1) * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) *
        ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar :=
  nongeneric_object_bound_of_estimates large₂ h Y μsec hsec hH h8 h7b O h1 h24 hB (by positivity) hK hCB2 hCn hCM he0 he

theorem second_packet_bound_of_estimates {D : D7} (large₂ : SizeData₂ D) (h : UniformConstantsAndStatements.LargenessConstants) {u : D.what₂.Word} {Cn : ℝ} {X : TermTie D}
    (Y : LoopTie D large₂ X u u Cn) (μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (hsec : ∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (Y.W τ).z (Y.W τ).z' (μsec τ))
    {CM Ce secondBesselConstant S K A Cb : ℝ} (hH : UniformConstantsAndStatements.Hyp D large₂ h) (h8 : UniformConstantsAndStatements.adm8 D large₂ h CM Ce) (h7b : UniformConstantsAndStatements.ConjugateSelfDualCharacter D secondBesselConstant)
    (hS : ∑' p : UnitaryVolumeMass.scalG D u u, D.s.pval p.1 = ((S : ℝ) : ℂ)) (hS0 : 0 ≤ S)
    (O : NGObj D u u) (h1 : StepClass O S)
    (h24 : ∀ cInf constP dens, MainCount D u u CM cInf constP dens →
      StepMean O (1 * large₂.sc.b ^ (K * (D.R.m : ℝ) ^ 4 * (D.R.f : ℝ))) (cInf * ∏' p, constP p)
        (A * ((D.R.rS : ℝ) + 1) ^ 2))
    (hB : StepB O (A * ((D.R.rS : ℝ) + 1) ^ 2) (Real.exp (Cb * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L))
      (∏ τ, MMv D u u (Y.A τ) (μsec τ)))
    (hK : 0 ≤ K) (hCB2 : 1 ≤ secondBesselConstant) (hCn : 0 ≤ Cn) (hCM : 0 ≤ CM) (he0 : 0 ≤ eSum D Ce) (he : eSum D Ce ≤ 1) :
    ‖(gaG D : ℂ) * ∑' p : UnitaryVolumeMass.scalG D u u, D.s.pval p.1‖ ≤
      Real.exp ((K + Cb + Real.log secondBesselConstant + 2 * Cn + CM + 1) * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L) *
        (D.duS u : ℝ) ^ 2 / D.what₂.Dstar := by
  have hD : StandingNumericalData D h.C0 := hH.1
  have hg := gamma_factor_pos D hD.2.2.2.2.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.2.2.2.2.1
  have := nongeneric_object_bound_of_estimates large₂ h Y μsec hsec hH h8 h7b O h1 h24 hB zero_le_one hK hCB2 hCn hCM he0 he
  rw [hS, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hg.le hS0), sq]
  rwa [one_mul] at this

end Assembly

section P29cFamily

variable {eps : ℝ} (Fm : FamP eps) (g : UniformConstantsAndStatements.Given)

theorem scaled_constant_pos (Fm : FamP eps) : 0 < sC' Fm := by
  obtain ⟨x, -, hx, -, ⟨i⟩⟩ := Fm.toFamCore.exists_pt 0
  have := (Fm.params _ hx i).CkLow_pos
  rw [Fm.params_CkLow] at this
  exact this

def NGOneF (C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => UniformConstantsAndStatements.Hyp (Fm.D x i) (Fm.L x i) (g.wth C' Cl) →
    ∀ u u', NGOneAt (Fm.D x i) (Fm.L x i) u u' C

theorem first_packet_bound_of_nongeneric_unit {cL c C : ℝ} (hc : c < cL) (h4 : UniformConstantsAndStatements.admF4 Fm g) (h9 : UniformConstantsAndStatements.admF9 Fm g cL)
    (hN : NGOneF Fm g C) : UniformConstantsAndStatements.ConclusionF1 Fm g c (C + 1) := by
  obtain ⟨x4, H4⟩ := h4
  obtain ⟨x9, H9⟩ := h9
  obtain ⟨xN, HN⟩ := hN
  obtain ⟨xk, _, Hk⟩ := ev_k Fm (max 3 (3 / (cL - c)))
  obtain ⟨xm, _, Hm⟩ := ev_m Fm (sCl Fm / sC' Fm)
  refine ownEv_intro Fm (max (max x4 x9) (max xN (max xk xm))) fun x hx hx1 i => ?_
  have g4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have g9 : x9 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have gN : xN ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have gk : xk ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have gm : xm ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  intro hH
  have hD : StandingNumericalData (Fm.D x i) g.C0 := hH.1
  have h0 := hD.2.2.2.2.2.2.2.2.2.2.1
  have h1 := hD.2.2.2.2.2.2.2.2.2.2.2.1
  have hk := Hk x gk i
  have hk3 : (3 : ℝ) ≤ ((Fm.D x i).R.k : ℝ) := le_trans (le_max_left _ _) hk
  have hkc : 3 / (cL - c) ≤ ((Fm.D x i).R.k : ℝ) := le_trans (le_max_right _ _) hk
  have hcc : 0 < cL - c := by linarith
  have hlog : 1 ≤ Real.log ((Fm.D x i).R.k : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hk' : 3 ≤ (cL - c) * ((Fm.D x i).R.k : ℝ) * Real.log ((Fm.D x i).R.k : ℝ) := by
    have a1 : 3 ≤ (cL - c) * ((Fm.D x i).R.k : ℝ) := by
      rw [div_le_iff₀ hcc] at hkc; linarith
    nlinarith
  have hL1 : 1 ≤ (Fm.L x i).sc.L := by
    rw [sc_L Fm hx1]
    exact Real.one_le_rpow (one_lt_of Fm hx1).le (eps_pos Fm).le
  have hm2 : (2 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by exact_mod_cast (Fm.D x i).R.two_le_m
  have hL : 3 ≤ ((Fm.D x i).R.m : ℝ) ^ 5 * (Fm.L x i).sc.L := by
    have : (32 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) ^ 5 := by
      calc (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hm2 5
    nlinarith
  have hmm : sCl Fm ≤ sC' Fm * ((Fm.D x i).R.m : ℝ) := by
    have := Hm x gm i
    rw [div_le_iff₀ (scaled_constant_pos Fm)] at this
    linarith
  have hprem := loop_hypothesis_of_scale_le (Fm.D x i) (Fm.L x i) hH.2.1 hmm hk3
  exact first_packet_bound_of_unit_bounds (Fm.D x i) (Fm.L x i) h0 h1 (H4 x g4 i hH) (H9 x g9 i hH hprem) (HN x gN i hH) hk' hL

theorem first_packet_unfolded_of_nongeneric_unit (a : UniformConstantsAndStatements.AdmC) {c C : ℝ} (hc : c < a.cL) (hN : NGOneF Fm g C) :
    UniformConstantsAndStatements.FirstFiltrationHypotheses Fm g a → UniformConstantsAndStatements.ConclusionF1 Fm g c (C + 1) :=
  fun hA => first_packet_bound_of_nongeneric_unit Fm g hc hA.2.1 hA.2.2.2.2.2.2.2 hN

theorem theorem_B_second_bound_family {C : ℝ} (hC : 64 ≤ C) : UniformConstantsAndStatements.FamilyWeightedBoundSecond Fm C := fun _ _ => theorem_B_second_bound_of_large _ hC

def NGOneBdF (C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => UniformConstantsAndStatements.Hyp (Fm.D x i) (Fm.L x i) (g.wth C' Cl) → ∀ u u' : (Fm.D x i).what₂.Word,
    gaG (Fm.D x i) * (∑' p : ngOne (Fm.D x i) u u', (Fm.D x i).s.pval p.1).re ≤
      (2 : ℝ) ^ (-(((Fm.D x i).R.k : ℝ) - 2 * ((Fm.D x i).R.rS : ℝ) - 5)) *
        Real.exp (C * ((Fm.D x i).R.m : ℝ) ^ 5 * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.L) *
        (((Fm.D x i).duS u : ℝ) * ((Fm.D x i).duS u' : ℝ)) / (Fm.D x i).what₂.Dstar

def SecondPacketFamilyInequality (C : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => UniformConstantsAndStatements.Hyp (Fm.D x i) (Fm.L x i) (g.wth C' Cl) → ∀ u : (Fm.D x i).what₂.Word,
    ‖(gaG (Fm.D x i) : ℂ) * ∑' p : UnitaryVolumeMass.scalG (Fm.D x i) u u, (Fm.D x i).s.pval p.1‖ ≤
      Real.exp (C * ((Fm.D x i).R.m : ℝ) ^ 5 * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.L) *
        ((Fm.D x i).duS u : ℝ) ^ 2 / (Fm.D x i).what₂.Dstar

theorem pair_values_abs_summable_eventually (hP : PX.PairAbsF Fm) :
    OwnEv Fm fun C' Cl x i => UniformConstantsAndStatements.Hyp (Fm.D x i) (Fm.L x i) (g.wth C' Cl) → PX.PairAbs (Fm.D x i) :=
  hP g.C0 g.Cg g.cb g.Cu g.cT g.CT

theorem NGOneF_of_pairAbs {C : ℝ} (hP : PX.PairAbsF Fm) (hb : NGOneBdF Fm g C) : NGOneF Fm g C :=
  ((pair_values_abs_summable_eventually Fm g hP).and hb).mono fun _ _ _ _ h hH u u' =>
    NGOneAt_of_pairAbs _ _ (h.1 hH u u') (h.2 hH u u')

theorem first_packet_bound_of_pair_abs {cL c C : ℝ} (hc : c < cL) (h4 : UniformConstantsAndStatements.admF4 Fm g) (h9 : UniformConstantsAndStatements.admF9 Fm g cL)
    (hP : PX.PairAbsF Fm) (hb : NGOneBdF Fm g C) : UniformConstantsAndStatements.ConclusionF1 Fm g c (C + 1) :=
  first_packet_bound_of_nongeneric_unit Fm g hc h4 h9 (NGOneF_of_pairAbs Fm g hP hb)

theorem second_packet_bound_of_pair_abs {C : ℝ} (hP : PX.PairAbsF Fm) (hb : SecondPacketFamilyInequality Fm g C) : UniformConstantsAndStatements.ConclusionF2 Fm g C :=
  ((pair_values_abs_summable_eventually Fm g hP).and hb).mono fun _ _ _ _ h hH =>
    second_packet_bound_of_summable _ _ (fun u => h.1 hH u u) (h.2 hH)

def FirstPacketRemainder (a : UniformConstantsAndStatements.AdmC) (C : ℝ) : Prop := UniformConstantsAndStatements.FirstFiltrationHypotheses Fm g a → NGOneF Fm g C

def SecondPacketRemainder (a : UniformConstantsAndStatements.AdmC) (C : ℝ) : Prop := UniformConstantsAndStatements.SecondFiltrationHypotheses Fm g a → SecondPacketFamilyInequality Fm g C

theorem first_packet_unfolded_of_remainder (a : UniformConstantsAndStatements.AdmC) {c C : ℝ} (hc : c < a.cL) (hR : FirstPacketRemainder Fm g a C) :
    UniformConstantsAndStatements.FirstFiltrationHypotheses Fm g a → UniformConstantsAndStatements.ConclusionF1 Fm g c (C + 1) :=
  fun hA => first_packet_unfolded_of_nongeneric_unit Fm g a hc (hR hA) hA

theorem second_packet_unfolded_of_remainder (a : UniformConstantsAndStatements.AdmC) {C : ℝ} (hP : PX.PairAbsF Fm) (hR : SecondPacketRemainder Fm g a C) :
    UniformConstantsAndStatements.SecondFiltrationHypotheses Fm g a → UniformConstantsAndStatements.ConclusionF2 Fm g C :=
  fun hA => second_packet_bound_of_pair_abs Fm g hP (hR hA)

theorem first_packet_of_remainder (a : UniformConstantsAndStatements.AdmC) {c C : ℝ} (hc : c < a.cL) (hR : FirstPacketRemainder Fm g a C) :
    UniformConstantsAndStatements.PeriodFamilyStatement Fm g a c (C + 1) := first_packet_unfolded_of_remainder Fm g a hc hR

theorem second_packet_of_remainder (a : UniformConstantsAndStatements.AdmC) {C : ℝ} (hP : PX.PairAbsF Fm) (hR : SecondPacketRemainder Fm g a C) :
    UniformConstantsAndStatements.DeterminantValueFamily Fm g a C := second_packet_unfolded_of_remainder Fm g a hP hR

end P29cFamily

theorem closed_first_packet_of_remainder (𝒞 : FamClass)
    (h : ∀ (g : UniformConstantsAndStatements.Given) (CNG secondBesselConstant CM Ce cL : ℝ), 0 < cL → ∃ Aw Ch : ℝ, ∀ Cg Cb Cgw Cbw : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      Closed 𝒞 fun Fm _ => FirstPacketRemainder Fm g ⟨CNG, Ch, Cg, Cb, secondBesselConstant, Aw, Cgw, Cbw, CM, Ce, 0, cL⟩ C) :
    UniformConstantsAndStatements.UniformClosedFormStatement 𝒞 := by
  intro g CNG secondBesselConstant CM Ce cL hcL
  obtain ⟨Aw, Ch, H⟩ := h g CNG secondBesselConstant CM Ce cL hcL
  refine ⟨Aw, Ch, fun Cg Cb Cgw Cbw => ?_⟩
  obtain ⟨C, hC, hcl⟩ := H Cg Cb Cgw Cbw
  refine ⟨cL / 2, by linarith, C + 1, by linarith, hcl.imp fun Fm _ _ hR => ?_⟩
  exact first_packet_of_remainder Fm g _ (show cL / 2 < cL by linarith) hR

end Formalism.MainNotions.BridgeLemma

end
