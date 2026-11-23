import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusProjectedBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HS

variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

theorem q_hs_nonneg (A : H →L[ℂ] G) : 0 ≤ hsNormSq A := by
  rw [FrobeniusProjectedBounds.hsNormSq_eq]
  positivity

theorem q_hs_add_le (A B : H →L[ℂ] G) : hsNormSq (A + B) ≤ 2 * hsNormSq A + 2 * hsNormSq B := by
  rw [FrobeniusProjectedBounds.hsNormSq_eq, FrobeniusProjectedBounds.hsNormSq_eq, FrobeniusProjectedBounds.hsNormSq_eq, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.add_apply]
  have h := norm_add_le (A (stdOrthonormalBasis ℂ H i)) (B (stdOrthonormalBasis ℂ H i))
  nlinarith [norm_nonneg (A (stdOrthonormalBasis ℂ H i) + B (stdOrthonormalBasis ℂ H i)),
    norm_nonneg (A (stdOrthonormalBasis ℂ H i)), norm_nonneg (B (stdOrthonormalBasis ℂ H i)),
    sq_nonneg (‖A (stdOrthonormalBasis ℂ H i)‖ - ‖B (stdOrthonormalBasis ℂ H i)‖)]

end HS

section Sizes

variable (D : D7) (large₂ : SizeData₂ D)

theorem q_five_le_k : (5 : ℝ) ≤ D.R.k := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  have h : 5 ≤ D.R.k := by omega
  exact_mod_cast h

theorem q_one_le_L : 1 ≤ large₂.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le

theorem q_one_le_b : 1 ≤ large₂.sc.b := by
  unfold Scale.b
  exact Real.one_le_exp (by linarith [q_one_le_L D large₂])

theorem q_f_le_k : (D.R.f : ℝ) ≤ D.R.k := by
  unfold Ranks.f
  exact_mod_cast D.R.f_le_k

theorem q_one_le_f : (1 : ℝ) ≤ D.R.f := by
  have h1 := D.R.m_le_f
  have h2 := D.R.two_le_m
  unfold Ranks.f
  have h : 1 ≤ 2 * D.R.ord := by omega
  exact_mod_cast h

theorem q_M_ge : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hf := q_one_le_f D
  have hL := q_one_le_L D large₂
  have h5 : (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm 5
    norm_num at this
    linarith
  calc (32 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := h5
    _ = (D.R.m : ℝ) ^ 5 * 1 * 1 := by ring
    _ ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by gcongr

theorem q_g_ge {g : ℝ} (h : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ g) : 10 * (D.R.f : ℝ) ≤ g := by
  have hk := q_five_le_k D
  have hb := q_one_le_b D large₂
  have hf := q_f_le_k D
  have hy : (5 : ℝ) ≤ D.R.k * large₂.sc.b := by nlinarith
  have h7 : (10 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 7 := by
    calc (10 : ℝ) ≤ 5 ^ 7 := by norm_num
      _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 7 := pow_le_pow_left₀ (by norm_num) hy 7
  have h8 : 10 * ((D.R.k : ℝ) * large₂.sc.b) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have : ((D.R.k : ℝ) * large₂.sc.b) ^ 8 = ((D.R.k : ℝ) * large₂.sc.b) ^ 7 * ((D.R.k : ℝ) * large₂.sc.b) := by ring
    rw [this]
    nlinarith
  nlinarith

theorem typed_places_factor_bounds {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : FrobeniusProjectedBounds.Hyp D large₂ C' Cl Cg cb Cu cT CT C0) :
    0 ≤ f3G D ∧ f3G D ≤ 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hg1, _, hg2, _⟩ := hH.1
  have e := typed_factor_split_of_data D hH.2.1
  unfold HostFactorProductPowerIdentity at e
  rw [e, Fin.prod_univ_two]
  have hf := q_one_le_f D
  have a1 := q_g_ge D large₂ hg1
  have a2 := q_g_ge D large₂ hg2
  have p1 : (0 : ℝ) < D.host.g 0 := by linarith
  have p2 : (0 : ℝ) < D.host.g 1 := by linarith
  refine ⟨by positivity, ?_⟩
  have b1 : 1 + 3 / (D.host.g 0 : ℝ) ≤ Real.exp (3 / (D.host.g 0 : ℝ)) := by
    have := Real.add_one_le_exp (3 / (D.host.g 0 : ℝ)); linarith
  have b2 : 1 + 3 / (D.host.g 1 : ℝ) ≤ Real.exp (3 / (D.host.g 1 : ℝ)) := by
    have := Real.add_one_le_exp (3 / (D.host.g 1 : ℝ)); linarith
  have b3 : (1 + 3 / (D.host.g 0 : ℝ)) * (1 + 3 / (D.host.g 1 : ℝ)) ≤
      Real.exp (3 / (D.host.g 0 : ℝ) + 3 / (D.host.g 1 : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul b1 b2 (by positivity) (Real.exp_pos _).le
  have c1 : (D.R.f : ℝ) * (3 / (D.host.g 0 : ℝ)) ≤ 3 / 10 := by
    rw [mul_div_assoc', div_le_div_iff₀ p1 (by norm_num)]; linarith
  have c2 : (D.R.f : ℝ) * (3 / (D.host.g 1 : ℝ)) ≤ 3 / 10 := by
    rw [mul_div_assoc', div_le_div_iff₀ p2 (by norm_num)]; linarith
  calc ((1 + 3 / (D.host.g 0 : ℝ)) * (1 + 3 / (D.host.g 1 : ℝ))) ^ D.R.f
      ≤ (Real.exp (3 / (D.host.g 0 : ℝ) + 3 / (D.host.g 1 : ℝ))) ^ D.R.f :=
        pow_le_pow_left₀ (by positivity) b3 _
    _ = Real.exp ((D.R.f : ℝ) * (3 / (D.host.g 0 : ℝ) + 3 / (D.host.g 1 : ℝ))) := by
        rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log 2) := by
        apply Real.exp_le_exp.2
        have := Real.log_two_gt_d9
        rw [mul_add]; linarith
    _ = 2 := Real.exp_log (by norm_num)

theorem q_gaG_pos {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : FrobeniusProjectedBounds.Hyp D large₂ C' Cl Cg cb Cu cT CT C0) : 0 < gaG D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hg1, _, hg2, _⟩ := hH.1
  rw [gaG_eq D hH.2.1.2.2.2.2.2.2.2.2.2.2.1 hH.2.1.2.2.2.2.2.2.2.2.2.2.2.1]
  have hf := q_one_le_f D
  have a1 := q_g_ge D large₂ hg1
  have a2 := q_g_ge D large₂ hg2
  have key : ∀ g : ℝ, 10 * (D.R.f : ℝ) ≤ g → 0 < ∏ i ∈ Finset.Icc 1 D.R.k, (g ^ i - 1) := by
    intro g hg
    refine Finset.prod_pos fun i hi => ?_
    have h1 : (1 : ℝ) < g := by linarith
    have hi' : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
    have := one_lt_pow₀ h1 hi'
    linarith
  exact mul_pos (pow_pos (key _ a1) _) (pow_pos (key _ a2) _)

theorem q_Gam_eq : FrobeniusProjectedBounds.Gam D = Real.exp (large₂.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by
  unfold FrobeniusProjectedBounds.Gam
  rw [← large₂.Gam_eq D.u₀, Real.exp_log (lt_trans one_pos (D.mem D.u₀).A.one_lt_gammaP)]

theorem q_Dst_pos : 0 < FrobeniusProjectedBounds.Dst D := by
  unfold FrobeniusProjectedBounds.Dst
  rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos

theorem q_const {M mx CN CE CG a1 a2 a3 f3 : ℝ} (hM : 32 ≤ M) (hCN : CN ≤ mx) (hCE : CE ≤ mx) (hmx : 0 ≤ mx)
    (hCG : mx + 1 ≤ CG) (h1 : a1 ≤ 1) (_h2 : 0 ≤ a2) (h2' : a2 ≤ 1) (h3' : 0 ≤ a3) (h3 : a3 ≤ 1) (_hf : 0 ≤ f3) (hf' : f3 ≤ 2) :
    2 * (a1 + a2 * Real.exp (CN * M)) + 2 * (f3 * (a3 + Real.exp (CE * M))) ≤ Real.exp (CG * M) := by
  have hM0 : 0 ≤ M := by linarith
  have hE1 : 1 ≤ Real.exp (mx * M) := Real.one_le_exp (mul_nonneg hmx hM0)
  have hN : Real.exp (CN * M) ≤ Real.exp (mx * M) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCN hM0)
  have hEE : Real.exp (CE * M) ≤ Real.exp (mx * M) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCE hM0)
  have hG : Real.exp (mx * M) * Real.exp M ≤ Real.exp (CG * M) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexpM : 33 ≤ Real.exp M := by
    have := Real.add_one_le_exp M
    linarith
  have hpN := Real.exp_pos (CN * M)
  have hpE := Real.exp_pos (CE * M)
  have h1' : a2 * Real.exp (CN * M) ≤ Real.exp (mx * M) := by nlinarith
  have hs0 : 0 ≤ a3 + Real.exp (CE * M) := by linarith
  have h2' : f3 * (a3 + Real.exp (CE * M)) ≤ 2 * (1 + Real.exp (mx * M)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hf') hs0]
  have h33 : 33 * Real.exp (mx * M) ≤ Real.exp (mx * M) * Real.exp M := by nlinarith
  linarith

end Sizes

section B

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {C' Cl Cg cb Cu cT CT C0 : ℝ}

theorem q_split (hH : FrobeniusProjectedBounds.Hyp D large₂ C' Cl Cg cb Cu cT CT C0) (h1 : FrobeniusProjectedBounds.adm1 D large₂ C' Cl Cg cb Cu cT CT C0)
    (ha : FrobeniusProjectedBounds.Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0) (u : D.what₂.Word) :
    Kmat D.s u u - FrobeniusProjectedBounds.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u) =
      KOf D.s u u (famNG D.s) + KOf D.s u u (famG D.s) := by
  classical
  obtain ⟨hE, _⟩ := h1 hH u u
  obtain ⟨c1, c2, c3, _, c5, _, _, _⟩ := ha hH u
  have hs : Summable (fun t => D.s.aTerm u u t) := hE.summable
  set a : D.s.Term u u → (D.s.Cu u →L[ℂ] D.s.Cu u) := fun t => D.s.aTerm u u t with ha'
  have i1 : ({t | D.s.inS t} : Set (D.s.Term u u)).indicator a = ({t | D.s.isId t} : Set (D.s.Term u u)).indicator a := by
    funext t
    by_cases hi : D.s.isId t
    · simp [Set.indicator, hi, c2 t hi]
    · by_cases hS : D.s.inS t
      · have hr : ¬ D.s.relevant t := fun hr => hi (c3 t hS hr)
        simp [Set.indicator, hi, hS, ha', c5 t hr]
      · simp [Set.indicator, hi, hS]
  have s1 : HasSum (({t | D.s.isId t} : Set (D.s.Term u u)).indicator a) (ContinuousLinearMap.id ℂ (D.s.Cu u)) := by
    rw [← i1]
    exact (hasSum_subtype_iff_indicator (s := {t | D.s.inS t})).1 c1
  have sS : ∀ S : Set (D.s.Term u u), HasSum (S.indicator a) (KOf D.s u u S) := fun S =>
    (hasSum_subtype_iff_indicator (s := S)).1 (hs.subtype S).hasSum
  have s2 := sS {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}
  have s3 := sS (famNG D.s)
  have s4 := sS (famG D.s)
  have e : (fun t => ({t | D.s.isId t} : Set (D.s.Term u u)).indicator a t +
      ({t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} : Set (D.s.Term u u)).indicator a t +
      (famNG D.s : Set (D.s.Term u u)).indicator a t + (famG D.s : Set (D.s.Term u u)).indicator a t) = a := by
    funext t
    by_cases hi : D.s.isId t
    · simp [Set.indicator, famNG, famG, hi]
    · by_cases hG : D.s.Gterm t = 0
      · simp [Set.indicator, famNG, famG, hi, hG]
      · by_cases hg : D.s.generic t
        · simp [Set.indicator, famNG, famG, hi, hG, hg]
        · simp [Set.indicator, famNG, famG, hi, hG, hg]
  have tot := ((s1.add s2).add s3).add s4
  rw [e] at tot
  have := hE.unique tot
  rw [this]
  unfold FrobeniusProjectedBounds.Kpp
  abel

theorem q_gen_le {cL CE : ℝ} (hH : FrobeniusProjectedBounds.Hyp D large₂ C' Cl Cg cb Cu cT CT C0)
    (h2 : FrobeniusProjectedBounds.adm2 D large₂ C' Cl Cg cb Cu cT CT C0) (h4 : FrobeniusProjectedBounds.ArchimedeanSignatureMatching D large₂ C' Cl Cg cb Cu cT CT C0 cL)
    (h6 : FrobeniusProjectedBounds.adm6 D large₂ C' Cl Cg cb Cu cT CT C0 CE) (ha : FrobeniusProjectedBounds.Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0)
    (u : D.what₂.Word) :
    hsNormSq (KOf D.s u u (famG D.s)) ≤ f3G D *
      (Real.exp (-(cL * FrobeniusProjectedBounds.kR D * FrobeniusProjectedBounds.fR D * Real.log (FrobeniusProjectedBounds.kR D))) * (FrobeniusProjectedBounds.du D u * FrobeniusProjectedBounds.du D u) / FrobeniusProjectedBounds.Dst D +
        Real.exp (CE * FrobeniusProjectedBounds.mR D ^ 5 * FrobeniusProjectedBounds.fR D * large₂.sc.L) * FrobeniusProjectedBounds.du D u ^ 2 / FrobeniusProjectedBounds.Dst D) := by
  classical
  obtain ⟨_, _, _, _, _, _, _, c8⟩ := ha hH u
  have hg := q_gaG_pos D large₂ hH
  obtain ⟨hf0, _⟩ := typed_places_factor_bounds D large₂ hH
  set v : D.s.Pair u u → ℂ := fun p => D.s.pval p with hv
  set P : Set (D.s.Pair u u) := pairsIn D.s (famG D.s) with hP
  set Lp : Set (D.s.Pair u u) := {p | p ∈ P ∧ loopP D.s p} with hLp
  set Sc : Set (D.s.Pair u u) := {p | FrobeniusProjectedBounds.scalG p} with hSc
  set BL := Real.exp (-(cL * FrobeniusProjectedBounds.kR D * FrobeniusProjectedBounds.fR D * Real.log (FrobeniusProjectedBounds.kR D))) *
    (FrobeniusProjectedBounds.du D u * FrobeniusProjectedBounds.du D u) / FrobeniusProjectedBounds.Dst D with hBL
  set BE := Real.exp (CE * FrobeniusProjectedBounds.mR D ^ 5 * FrobeniusProjectedBounds.fR D * large₂.sc.L) * FrobeniusProjectedBounds.du D u ^ 2 / FrobeniusProjectedBounds.Dst D with hBE

  have hU : P = Lp ∪ Sc := by
    ext p
    constructor
    · intro hp
      by_cases hs : scalarP D.s p
      · exact Or.inr ⟨hp, hs⟩
      · refine Or.inl ⟨hp, hp.1.2.1, hp.2.2.1, ?_⟩
        have h1 := c8 p hp.1.2.1 hp.2.2.1
        by_cases h2 : 2 ≤ D.s.s0 p
        · exact Or.inl h2
        · have h3 : D.s.s0 p = 1 := by omega
          exact Or.inr ⟨hp.1.2.2, hp.2.2.2, h3, fun hsc => hs ⟨hp.1.2.2, hp.2.2.2, h3, hsc⟩⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hDj : Disjoint Lp Sc := by
    rw [Set.disjoint_left]
    rintro p ⟨_, _, _, h⟩ ⟨_, _, _, h1, hsc⟩
    rcases h with h | h
    · omega
    · exact h.2.2.2 hsc

  have hLfin : ∀ S : Finset Lp, ∑ p ∈ S, ‖v p.1‖ ≤ BL / gaG D := by
    intro S
    have h := h4 hH u u (S.map (Function.Embedding.subtype _)) (by
      intro p hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_map.1 hp
      exact q.2.2)
    rw [Finset.sum_map] at h
    rw [le_div_iff₀ hg, mul_comm]
    exact h
  have nL : Summable (fun p : Lp => ‖v p.1‖) := summable_of_sum_le (fun _ => norm_nonneg _) hLfin
  have tL : ∑' p : Lp, ‖v p.1‖ ≤ BL / gaG D := nL.tsum_le_of_sum_le hLfin
  have sL : Summable (fun p : Lp => v p.1) := nL.of_norm

  obtain ⟨sS, bS⟩ := h6 hH u
  have nS : Summable (fun p : Sc => ‖v p.1‖) := summable_norm_iff.2 sS

  have nP : Summable (fun p : P => ‖v p.1‖) := by
    have a1 := (summable_subtype_iff_indicator (s := Lp) (f := fun p => ‖v p‖)).1 nL
    have a2 := (summable_subtype_iff_indicator (s := Sc) (f := fun p => ‖v p‖)).1 nS
    refine (summable_subtype_iff_indicator (s := P) (f := fun p => ‖v p‖)).2 ?_
    rw [hU, Set.indicator_union_of_disjoint hDj]
    exact a1.add a2
  have tP : ∑' p : P, v p.1 = ∑' p : Lp, v p.1 + ∑' p : Sc, v p.1 := by
    have a1 := (hasSum_subtype_iff_indicator (s := Lp) (f := v)).1 sL.hasSum
    have a2 := (hasSum_subtype_iff_indicator (s := Sc) (f := v)).1 sS.hasSum
    have a3 := a1.add a2
    have e : (fun p => Lp.indicator v p + Sc.indicator v p) = P.indicator v := by
      rw [hU, Set.indicator_union_of_disjoint hDj]
    rw [e] at a3
    exact ((hasSum_subtype_iff_indicator (s := P) (f := v)).2 a3).tsum_eq
  have main := h2 hH u u (famG D.s) (Or.inl rfl) (fun t ht => ht.2.1) nP
  have r1 : gaG D * (∑' p : Lp, v p.1).re ≤ BL := by
    have b1 : (∑' p : Lp, v p.1).re ≤ BL / gaG D :=
      le_trans (Complex.re_le_norm _) (le_trans (norm_tsum_le_tsum_norm nL) tL)
    calc gaG D * (∑' p : Lp, v p.1).re ≤ gaG D * (BL / gaG D) := mul_le_mul_of_nonneg_left b1 hg.le
      _ = BL := by field_simp
  have r2 : gaG D * (∑' p : Sc, v p.1).re ≤ BE := by
    have b1 : ‖(gaG D : ℂ) * ∑' p : Sc, v p.1‖ = gaG D * ‖∑' p : Sc, v p.1‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
    have b2 : gaG D * ‖∑' p : Sc, v p.1‖ ≤ BE := by rw [← b1]; exact bS
    exact le_trans (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hg.le) b2
  calc hsNormSq (KOf D.s u u (famG D.s)) ≤ f3G D * gaG D * (∑' p : P, v p.1).re := main
    _ = f3G D * (gaG D * (∑' p : Lp, v p.1).re + gaG D * (∑' p : Sc, v p.1).re) := by
        rw [tP, Complex.add_re]; ring
    _ ≤ f3G D * (BL + BE) := mul_le_mul_of_nonneg_left (add_le_add r1 r2) hf0

theorem theorem_S_equal_words (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 cL cN CN CE : ℝ) :
    FrobeniusProjectedBounds.HodgeTateFromSandwich D large₂ X C' Cl Cg cb Cu cT CT C0 cL cN CN CE := by
  rintro ⟨hcL, hcN, hCN, hCE, hCG⟩ ⟨h1, h2, h4, h5, h6⟩ ha hH u
  rw [q_split hH h1 ha u]
  have g1 := h5 hH u u
  have g2 := q_gen_le hH h2 h4 h6 ha u
  obtain ⟨hf0, hf2⟩ := typed_places_factor_bounds D large₂ hH
  have hD := q_Dst_pos D
  set Q := FrobeniusProjectedBounds.du D u ^ 2 / FrobeniusProjectedBounds.Dst D with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set M := (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L with hM
  have hk := q_five_le_k D
  have hlog : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_nonneg (by linarith)
  have hfp : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  set a1 := Real.exp (-(cN * FrobeniusProjectedBounds.kR D * FrobeniusProjectedBounds.fR D * Real.log (FrobeniusProjectedBounds.kR D))) with ha1
  set a2 := (2 : ℝ) ^ (-(FrobeniusProjectedBounds.kR D - 2 * FrobeniusProjectedBounds.rR D - 5)) with ha2
  set a3 := Real.exp (-(cL * FrobeniusProjectedBounds.kR D * FrobeniusProjectedBounds.fR D * Real.log (FrobeniusProjectedBounds.kR D))) with ha3
  have b1 : a1 ≤ 1 := by
    rw [ha1, Real.exp_le_one_iff]
    unfold FrobeniusProjectedBounds.kR FrobeniusProjectedBounds.fR
    have : 0 ≤ cN * (D.R.k : ℝ) * D.R.f * Real.log (D.R.k : ℝ) := by positivity
    linarith
  have b3 : a3 ≤ 1 := by
    rw [ha3, Real.exp_le_one_iff]
    unfold FrobeniusProjectedBounds.kR FrobeniusProjectedBounds.fR
    have : 0 ≤ cL * (D.R.k : ℝ) * D.R.f * Real.log (D.R.k : ℝ) := by positivity
    linarith
  have b2 : a2 ≤ 1 := by
    rw [ha2]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    unfold FrobeniusProjectedBounds.kR FrobeniusProjectedBounds.rR
    have hn : 2 * D.R.rS + 5 ≤ D.R.k := by
      obtain ⟨t, ht⟩ := D.R.m_even
      have h3 := D.R.m_add_three_le_k
      have h4 := D.R.two_le_m
      simp only [Ranks.rS]
      omega
    have : (2 : ℝ) * D.R.rS + 5 ≤ D.R.k := by exact_mod_cast hn
    linarith
  have b2' : 0 ≤ a2 := by rw [ha2]; positivity
  have key := q_const (M := M) (mx := max CE CN) (CN := CN) (CE := CE) (CG := large₂.CGam) (a1 := a1) (a2 := a2) (a3 := a3)
    (f3 := f3G D) (q_M_ge D large₂) (le_max_right _ _) (le_max_left _ _) (le_trans hCE (le_max_left _ _)) hCG b1 b2' b2
    (Real.exp_pos _).le b3 hf0 hf2
  have eN : Real.exp (CN * FrobeniusProjectedBounds.mR D ^ 5 * FrobeniusProjectedBounds.fR D * large₂.sc.L) = Real.exp (CN * M) := by
    unfold FrobeniusProjectedBounds.mR FrobeniusProjectedBounds.fR; rw [hM]; congr 1; ring
  have eE : Real.exp (CE * FrobeniusProjectedBounds.mR D ^ 5 * FrobeniusProjectedBounds.fR D * large₂.sc.L) = Real.exp (CE * M) := by
    unfold FrobeniusProjectedBounds.mR FrobeniusProjectedBounds.fR; rw [hM]; congr 1; ring
  have eG : FrobeniusProjectedBounds.Gam D = Real.exp (large₂.CGam * M) := by
    rw [q_Gam_eq D large₂, hM]; congr 1; ring
  rw [eN] at g1
  rw [eE] at g2
  have g1' : hsNormSq (KOf D.s u u (famNG D.s)) ≤ (a1 + a2 * Real.exp (CN * M)) * Q := by
    refine le_trans g1 (le_of_eq ?_)
    rw [hQ]; ring
  have g2' : hsNormSq (KOf D.s u u (famG D.s)) ≤ (f3G D * (a3 + Real.exp (CE * M))) * Q := by
    refine le_trans g2 (le_of_eq ?_)
    rw [hQ]; ring
  calc hsNormSq (KOf D.s u u (famNG D.s) + KOf D.s u u (famG D.s))
      ≤ 2 * hsNormSq (KOf D.s u u (famNG D.s)) + 2 * hsNormSq (KOf D.s u u (famG D.s)) := q_hs_add_le _ _
    _ ≤ (2 * (a1 + a2 * Real.exp (CN * M)) + 2 * (f3G D * (a3 + Real.exp (CE * M)))) * Q := by nlinarith
    _ ≤ Real.exp (large₂.CGam * M) * Q := mul_le_mul_of_nonneg_right key hQ0
    _ = FrobeniusProjectedBounds.Gam D * FrobeniusProjectedBounds.du D u ^ 2 / FrobeniusProjectedBounds.Dst D := by rw [eG, hQ]; ring

theorem unprojected_bound_of_K2 (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) :
    FrobeniusProjectedBounds.ConditionalUnprojectedFrobeniusBound D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro h3 hb hH u
  have k2 := h3 hH u
  have k0 := hb hH u
  have hw := (hH.2.1.2.2.2.2.2.2.2.2.2.1 u).2
  have e : KD D u u - ContinuousLinearMap.id ℂ (D.s.Cu u) =
      (Kmat D.s u u - FrobeniusProjectedBounds.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + FrobeniusProjectedBounds.Kpp D u u := by
    unfold KD; abel
  unfold hsDiagAllD
  rw [e]
  refine le_trans (q_hs_add_le _ _) ?_
  have hG : 0 < FrobeniusProjectedBounds.Gam D := lt_trans one_pos (D.mem D.u₀).A.one_lt_gammaP
  have hD := q_Dst_pos D
  have hd : (0 : ℝ) ≤ FrobeniusProjectedBounds.du D u := Nat.cast_nonneg _
  rw [D.GamP_eq u] at hw
  have hz : (D.mem D.u₀).A.GamP ^ (-2 : ℤ) = ((D.mem D.u₀).A.GamP ^ 2)⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [hz] at hw
  have key : FrobeniusProjectedBounds.Gam D * FrobeniusProjectedBounds.du D u ^ 2 / FrobeniusProjectedBounds.Dst D ≤ C0 / FrobeniusProjectedBounds.Gam D * FrobeniusProjectedBounds.du D u := by
    have h1 : FrobeniusProjectedBounds.du D u / FrobeniusProjectedBounds.Dst D ≤ (FrobeniusProjectedBounds.Gam D ^ 2)⁻¹ * C0 := by
      rw [div_le_iff₀ hD]
      calc FrobeniusProjectedBounds.du D u ≤ ((D.mem D.u₀).A.GamP ^ 2)⁻¹ * D.what₂.Dstar * C0 := hw
        _ = (FrobeniusProjectedBounds.Gam D ^ 2)⁻¹ * C0 * FrobeniusProjectedBounds.Dst D := by unfold FrobeniusProjectedBounds.Gam FrobeniusProjectedBounds.Dst; ring
    calc FrobeniusProjectedBounds.Gam D * FrobeniusProjectedBounds.du D u ^ 2 / FrobeniusProjectedBounds.Dst D
        = FrobeniusProjectedBounds.Gam D * FrobeniusProjectedBounds.du D u * (FrobeniusProjectedBounds.du D u / FrobeniusProjectedBounds.Dst D) := by ring
      _ ≤ FrobeniusProjectedBounds.Gam D * FrobeniusProjectedBounds.du D u * ((FrobeniusProjectedBounds.Gam D ^ 2)⁻¹ * C0) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hG.le hd)
      _ = C0 / FrobeniusProjectedBounds.Gam D * FrobeniusProjectedBounds.du D u := by field_simp
  unfold FrobeniusProjectedBounds.eF
  have e2 : (2 * C0 / FrobeniusProjectedBounds.Gam D + 2 * Real.exp (-(FrobeniusProjectedBounds.kR D * FrobeniusProjectedBounds.fR D * Real.log (FrobeniusProjectedBounds.kR D)))) * FrobeniusProjectedBounds.du D u =
      2 * (C0 / FrobeniusProjectedBounds.Gam D * FrobeniusProjectedBounds.du D u) +
        2 * (FrobeniusProjectedBounds.du D u * Real.exp (-(FrobeniusProjectedBounds.kR D * FrobeniusProjectedBounds.fR D * Real.log (FrobeniusProjectedBounds.kR D)))) := by ring
  rw [e2]
  linarith

end B

section Fam

variable {eps : ℝ} (Fm : FamP eps)

theorem unprojected_bound_family (Cg cb Cu cT CT C0 : ℝ) : FrobeniusProjectedBounds.ConditionalFamilyUnprojectedFrobenius Fm Cg cb Cu cT CT C0 := by
  intro h3 h2
  obtain ⟨x1, h1⟩ := h3
  obtain ⟨x2, h2'⟩ := h2
  refine ⟨max x1 x2, fun x hx i => ?_⟩
  exact unprojected_bound_of_K2 (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 (h1 x (le_of_max_le_left hx) i)
    (h2' x (le_of_max_le_right hx) i)

end Fam

section FlagsGen

open Formalism.MainNotions.S.Lat Module

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem r_Xa_mono {T : E} (F : FlagG S r T) {i j : ℕ} (h : i ≤ j) : F.Xa i ≤ F.Xa j := by
  unfold FlagG.Xa
  refine Submodule.span_mono (Set.image_mono fun x hx => ?_)
  simp only [Set.mem_setOf_eq] at hx ⊢
  omega

theorem r_e_mem {T : E} (F : FlagG S r T) (a : Fin r) {j : ℕ} (h : a.1 < j) : F.e a ∈ F.Xa j := by
  unfold FlagG.Xa
  exact Submodule.subset_span ⟨a, h, rfl⟩

theorem r_Xa_le_X {T : E} (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (Set.image_subset_range _ _)

theorem r_Xa_r {T : E} (F : FlagG S r T) : F.Xa r = F.X := by
  unfold FlagG.Xa FlagG.X
  have h : {i : Fin r | i.1 < r} = Set.univ := Set.eq_univ_of_forall fun i => i.2
  rw [h, Set.image_univ]

def InSF {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  (∀ a : Fin r, F'.fl.e a - F.fl.e a ∈ Xflag F a.val) ∧ F'.fl.z - F.fl.z ∈ Xsp F

theorem r_sameFlag_of_inS {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} (h : InSF F F') :
    FrobeniusProjectedBounds.SameFlag F F' := by
  have h1 : ∀ j, F'.fl.Xa j ≤ F.fl.Xa j := by
    intro j
    unfold FlagG.Xa
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    simp only [Set.mem_setOf_eq] at ha
    have hd : F'.fl.e a - F.fl.e a ∈ F.fl.Xa j := r_Xa_mono F.fl (le_of_lt ha) (h.1 a)
    have he : F.fl.e a ∈ F.fl.Xa j := r_e_mem F.fl a ha
    have hs : F'.fl.e a = (F'.fl.e a - F.fl.e a) + F.fl.e a := by abel
    rw [hs]
    exact add_mem hd he
  have h2 : ∀ j, F.fl.Xa j ≤ F'.fl.Xa j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      unfold FlagG.Xa
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      simp only [Set.mem_setOf_eq] at ha
      have hd : F'.fl.e a - F.fl.e a ∈ F'.fl.Xa j := r_Xa_mono F'.fl (le_of_lt ha) (ih a.val ha (h.1 a))
      have he : F'.fl.e a ∈ F'.fl.Xa j := r_e_mem F'.fl a ha
      have hs : F.fl.e a = F'.fl.e a - (F'.fl.e a - F.fl.e a) := by abel
      rw [hs]
      exact sub_mem he hd
  have key : ∀ j, F'.fl.Xa j = F.fl.Xa j := fun j => le_antisymm (h1 j) (h2 j)
  have hX : F'.fl.X = F.fl.X := by rw [← r_Xa_r F'.fl, ← r_Xa_r F.fl, key]
  unfold FrobeniusProjectedBounds.SameFlag
  refine ⟨fun j => key j, ?_⟩
  show F'.fl.Xplus = F.fl.Xplus
  unfold FlagG.Xplus
  rw [hX]
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have hs : F'.fl.z = (F'.fl.z - F.fl.z) + F.fl.z := by abel
    rw [hs]
    exact add_mem (Submodule.mem_sup_left h.2) (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have hs : F.fl.z = F'.fl.z - (F'.fl.z - F.fl.z) := by abel
    rw [hs]
    exact sub_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) (Submodule.mem_sup_left h.2)

theorem r_fvec_mem {T : E} (F : FlagG S r T) (b : Fin (r + 1)) : F.fvec b ∈ F.Xplus := by
  unfold FlagG.Xplus
  refine Fin.lastCases ?_ (fun a => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self F.z)
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)

theorem r_e_perp {T : E} (F : FlagG S r T) (a : Fin r) {y : S.V} (hy : y ∈ F.Xplus) : S.hT (F.e a) y = 0 := by
  have hle : F.Xplus ≤ LinearMap.ker (S.hT (F.e a)) := by
    unfold FlagG.Xplus FlagG.X
    rw [sup_le_iff, Submodule.span_le, Submodule.span_le]
    constructor
    · rintro _ ⟨b, rfl⟩
      exact LinearMap.mem_ker.mpr (F.e_iso a b)
    · rintro _ rfl
      exact LinearMap.mem_ker.mpr (F.z_orth a)
  exact LinearMap.mem_ker.mp (hle hy)

theorem r_Dl_zero {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (h : F'.Xplus = F.Xplus) (hr : 0 < r) (l : ℕ)
    (hl : 0 < l) : Dl F F' l = 0 := by
  unfold Dl leadMinorE
  split_ifs with hle
  · refine Matrix.det_eq_zero_of_row_eq_zero (⟨0, hl⟩ : Fin l) (fun b => ?_)
    have e0 : Fin.castLE hle (⟨0, hl⟩ : Fin l) = Fin.castSucc (⟨0, hr⟩ : Fin r) := by ext; rfl
    rw [Matrix.submatrix_apply, e0]
    unfold Zhat brS
    have e1 : F.fvec (Fin.castSucc (⟨0, hr⟩ : Fin r)) = F.e ⟨0, hr⟩ := by
      unfold FlagG.fvec; rw [Fin.snoc_castSucc]
    rw [e1]
    exact r_e_perp F _ (h ▸ r_fvec_mem F' _)
  · rfl

theorem r_G_zero {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (h : FrobeniusProjectedBounds.SameFlag F F') (hr : 0 < r) :
    Gval F F' = 0 := by
  unfold FrobeniusProjectedBounds.SameFlag at h
  have hP : F'.fl.Xplus = F.fl.Xplus := h.2
  show Gflag F.fl F'.fl = 0
  unfold Gflag
  rw [r_Dl_zero F.fl F'.fl hP hr (r + 1) (by omega), r_Dl_zero F.fl F'.fl hP hr r hr]
  simp

theorem r_z_orth {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  change x ∈ Submodule.span E (Set.range F.fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F.fl.z_orth a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem r_Xa_succ {T : E} (F : FlagG S r T) (a : Fin r) :
    F.Xa (a.val + 1) ≤ F.Xa a.val ⊔ Submodule.span E {F.e a} := by
  unfold FlagG.Xa
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  simp only [Set.mem_setOf_eq] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, h, rfl⟩)
  · have hia : i = a := Fin.ext h
    subst hia
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

def Shape {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (c : Fin r → E) (ζ : E) : Prop :=
  (∀ a, c a ≠ 0) ∧ (∀ a : Fin r, F'.fl.e a - c a • F.fl.e a ∈ Xflag F a.val) ∧ F'.fl.z - ζ • F.fl.z ∈ Xsp F

theorem r_shape_of_sameFlag {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} (h : FrobeniusProjectedBounds.SameFlag F F') :
    ∃ c ζ, Shape F F' c ζ := by
  unfold FrobeniusProjectedBounds.SameFlag at h
  obtain ⟨hX, hP⟩ := h
  have hX' : ∀ j, F'.fl.Xa j = F.fl.Xa j := hX
  have hP' : F'.fl.Xplus = F.fl.Xplus := hP
  have hmem : ∀ a : Fin r, ∃ c : E, F'.fl.e a - c • F.fl.e a ∈ Xflag F a.val := by
    intro a
    have h1 : F'.fl.e a ∈ F.fl.Xa (a.val + 1) := by
      rw [← hX' (a.val + 1)]
      exact r_e_mem F'.fl a (Nat.lt_succ_self a.val)
    have h2 := r_Xa_succ F.fl a h1
    obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp h2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨c, ?_⟩
    rw [← hyw]
    simpa using hy
  choose c hc using hmem
  have hz' : F'.fl.z ∈ F.fl.Xplus := by
    rw [← hP']
    unfold FlagG.Xplus
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  unfold FlagG.Xplus at hz'
  obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp hz'
  obtain ⟨ζ, rfl⟩ := Submodule.mem_span_singleton.mp hw
  refine ⟨c, ζ, fun a hca => ?_, hc, ?_⟩
  · have h0 : F'.fl.e a ∈ F'.fl.Xa a.val := by
      have := hc a
      rw [hca, zero_smul, sub_zero] at this
      rw [hX' a.val]
      exact this
    unfold FlagG.Xa at h0
    exact F'.fl.e_indep.notMem_span_image (s := {i : Fin r | i.1 < a.1}) (x := a) (by simp) h0
  · rw [← hyw]
    simpa using hy

theorem r_inS_of_shape_one {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'} {c : Fin r → E} {ζ : E}
    (h : Shape F F' c ζ) (hc : ∀ a, c a = 1) (hζ : ζ = 1) : InSF F F' := by
  obtain ⟨_, he, hz⟩ := h
  refine ⟨fun a => ?_, ?_⟩
  · simpa [hc a] using he a
  · simpa [hζ] using hz

end FlagsGen

section A

open Formalism.MainNotions.S.Lat Module

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {C' Cl Cg cb Cu cT CT C0 : ℝ}

theorem r_rS_pos (hH : FrobeniusProjectedBounds.Hyp D large₂ C' Cl Cg cb Cu cT CT C0) : 0 < D.R.rS := by
  obtain ⟨_, _, _, _, h5, _⟩ := hH.1
  by_contra h0
  have h1 : D.R.rS = 0 := by omega
  rw [h1] at h5
  simp only [Nat.cast_zero, Real.sqrt_zero] at h5
  have hf : (2 : ℝ) ≤ D.R.f := by
    have h : 2 ≤ D.R.f := by
      simp only [Ranks.f, Ranks.n]
      have := D.R.ord_pos
      omega
    exact_mod_cast h
  have := Real.log_pos (show (1 : ℝ) < D.R.f by linarith)
  linarith

theorem r_inS_iff {u : D.what₂.Word} (t : D.s.Term u u) : D.s.inS t ↔ InSF (X.fl t) (X.fl' t) := X.inS_iff t

theorem r_inS_of_isId (X : TermTie D) {u : D.what₂.Word} (t : D.s.Term u u) (h : D.s.isId t) : D.s.inS t := by
  rw [X.inS_iff t]
  obtain ⟨n, hn, he, hz⟩ := (X.isId_iff t).1 h
  obtain ⟨_, h1, h2⟩ := hn
  refine ⟨fun a => ?_, ?_⟩
  · rw [← he a]
    exact h1 a.val _ (r_e_mem (X.fl t).fl a (Nat.lt_succ_self _))
  · have e : (X.fl' t).fl.z - (X.fl t).fl.z =
        (n (X.fl t).fl.z - (X.fl t).fl.z) - (n (X.fl t).fl.z - (X.fl' t).fl.z) := by abel
    rw [e]
    exact sub_mem (h2 _ (r_z_orth (X.fl t))) hz

theorem r_Gterm_zero {u : D.what₂.Word} (t : D.s.Term u u) (h : Gval (X.fl t) (X.fl' t) = 0) : D.s.Gterm t = 0 := by
  have := X.G_eq t
  rw [h] at this
  exact (map_eq_zero (algebraMap D.host.F D.host.E)).1 this

theorem r_Gval_ne {u u' : D.what₂.Word} (t : D.s.Term u u') (h : D.s.Gterm t ≠ 0) : Gval (X.fl t) (X.fl' t) ≠ 0 := by
  rw [← X.G_eq t]
  exact (map_ne_zero (algebraMap D.host.F D.host.E)).2 h

theorem one_le_s_zero_of_nonzero (X : TermTie D) {u u' : D.what₂.Word} (p : D.s.Pair u u') (h1 : D.s.Gterm (D.s.pfst p) ≠ 0) :
    1 ≤ D.s.s0 p := by
  rw [X.s0_eq p]
  unfold Lat.s0
  have hr := LatticeGluingRadicals.a_rankHp_k (X.abelian₂ (D.s.pfst p)) (X.fixed (D.s.pfst p)).1 (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p))
    (X.fixed (D.s.pfst p)).2.2.1.2 (X.lift' (D.s.pfst p)).2 (r_Gval_ne _ h1) D.R.k (LatticeGluingRadicals.p_rankV D)
  have hle : Th (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p) ≤
      Hp (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) := by
    rintro x hx
    obtain ⟨pr, hpr, rfl⟩ := Submodule.mem_map.1 hx
    exact hpr.1.1.1
  have h2 := Submodule.finrank_mono hle
  have h3 := D.R.m_add_three_le_k
  omega

def FlagRigid (D : D7) (X : TermTie D) : Prop :=
  ∀ (u : D.what₂.Word) (t : D.s.Term u u), FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t) → D.s.relevant t → D.s.isId t

def RelScal (D : D7) (X : TermTie D) : Prop :=
  ∀ (u : D.what₂.Word) (t : D.s.Term u u) (c : Fin D.R.rS → D.host.E) (ζ : D.host.E),
    Shape (X.fl t) (X.fl' t) c ζ → D.s.relevant t → ∀ a, c a = ζ

def ZetaOne (D : D7) (X : TermTie D) : Prop :=
  ∀ (u : D.what₂.Word) (t : D.s.Term u u) (c : Fin D.R.rS → D.host.E) (ζ : D.host.E),
    Shape (X.fl t) (X.fl' t) c ζ → ζ = 1

def UnipExt (D : D7) (X : TermTie D) : Prop :=
  ∀ (u : D.what₂.Word) (t : D.s.Term u u), InSF (X.fl t) (X.fl' t) → D.s.isId t

theorem flagRigid_of (h1 : RelScal D X) (h2 : ZetaOne D X) (h3 : UnipExt D X) : FlagRigid D X := by
  intro u t hS hrel
  obtain ⟨c, ζ, hsh⟩ := r_shape_of_sameFlag hS
  have hζ : ζ = 1 := h2 u t c ζ hsh
  have hc : ∀ a, c a = 1 := fun a => by rw [h1 u t c ζ hsh hrel a, hζ]
  exact h3 u t (r_inS_of_shape_one hsh hc hζ)

theorem pair_terms_of_flag_rigidity (hR : FrobeniusProjectedBounds.Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → FlagRigid D X) :
    FrobeniusProjectedBounds.IntegralityFromMetric D large₂ X C' Cl Cg cb Cu cT CT C0 := by
  classical
  rintro ⟨h1, h8, h9⟩ hH u
  have hr := r_rS_pos hH
  have c2 : ∀ t : D.s.Term u u, D.s.isId t → D.s.inS t := fun t h => r_inS_of_isId X t h
  have cS : ∀ t : D.s.Term u u, D.s.inS t → FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t) :=
    fun t h => r_sameFlag_of_inS ((X.inS_iff t).1 h)
  have c4 := hR hH u
  have c3 : ∀ t : D.s.Term u u, D.s.inS t → D.s.relevant t → D.s.isId t := fun t h => c4 t (cS t h)
  have c5 := h8 hH u u
  set a : D.s.Term u u → (D.s.Cu u →L[ℂ] D.s.Cu u) := fun t => D.s.aTerm u u t with ha'
  refine ⟨?_, c2, c3, c4, c5, fun t h => r_Gterm_zero (X := X) t (r_G_zero _ _ (cS t h) hr), ?_,
    fun p g1 _ => one_le_s_zero_of_nonzero X p g1⟩
  · have i1 : ({t | D.s.inS t} : Set (D.s.Term u u)).indicator a =
        ({t | D.s.isId t} : Set (D.s.Term u u)).indicator a := by
      funext t
      by_cases hi : D.s.isId t
      · simp [Set.indicator, hi, c2 t hi]
      · by_cases hS : D.s.inS t
        · have hr : ¬ D.s.relevant t := fun hr => hi (c3 t hS hr)
          simp [Set.indicator, hi, hS, ha', c5 t hr]
        · simp [Set.indicator, hi, hS]
    refine (hasSum_subtype_iff_indicator (s := {t | D.s.inS t}) (f := a)).2 ?_
    rw [i1]
    exact (hasSum_subtype_iff_indicator (s := {t | D.s.isId t}) (f := a)).1 (h9 hH u)
  · unfold FrobeniusProjectedBounds.Kpp KOf
    have e := tsum_subtype {t : D.s.Term u u | D.s.relevant t ∧ D.s.Gterm t = 0 ∧
      ¬ FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t)} a
    have e' := tsum_subtype {t : D.s.Term u u | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} a
    refine e.trans (Eq.trans ?_ e'.symm)
    congr 1
    funext t
    by_cases hrel : D.s.relevant t
    · have hiff : FrobeniusProjectedBounds.SameFlag (X.fl t) (X.fl' t) ↔ D.s.isId t :=
        ⟨fun h => c4 t h hrel, fun h => cS t (c2 t h)⟩
      simp [Set.indicator, hrel, hiff]
    · have h0 : a t = 0 := c5 t hrel
      simp [Set.indicator, hrel, h0]

end A

end Formalism.MainNotions.BridgeLemma

end
