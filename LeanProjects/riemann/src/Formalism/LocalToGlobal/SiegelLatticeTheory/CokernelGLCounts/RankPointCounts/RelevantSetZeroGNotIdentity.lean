import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1b

variable {D : D7} {X : HidaSetting D}

theorem fixedFlag_level_ne_zero (D : D7) (u : D.what₂.Word) : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero

theorem relevantSet_zeroG_not_identity {Y : Full X} {u : D.what₂.Word} {t : GTu Y u} (ht : t ∈ relSet Y u) :
    t.relevant ∧ t.G = 0 ∧ ¬ t.isId := by
  obtain ⟨⟨hG, hid⟩, hr⟩ := ht
  refine ⟨hr, ?_, hid⟩
  have h : Gt t = 0 := hG
  unfold Gt at h
  by_contra hne
  rw [if_neg hne] at h
  exact one_ne_zero h

theorem exists_nfFull_of_relevant_of_G_eq_zero (Y : Full X) {u : D.what₂.Word} (t : GTu Y u) (hr : t.relevant) (hG : t.G = 0) :
    ∃ (j : ℕ) (hj : j ≤ D.R.rS) (c : D.host.E),
      Formalism.HermitianLatticeCounting.S6.NFFull (nfF (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)) (nfF (frq X t.rep).fl (nf_T_ne D u)) j hj c := by
  obtain ⟨hrel, hG0⟩ := relRepC D X Y u u t hr hG
  obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hpos : 0 < (σ ((Tu D u : ℕ) : D.host.E)).re := by
    rw [map_natCast, Complex.natCast_re]
    exact_mod_cast tie_Tu_pos D u
  refine Formalism.HermitianLatticeCounting.Final.S6.normalForm D.host.E (hS D).V σ (nfH (hS D)) D.R.rS _ _ (fun x => p_starConj D σ x)
    hpos hpos (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ) (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ)
    (nf_rel D.host.F (tie_trace D.sp.cm) _ _ _ _ hrel) ?_
  rw [nf_G]
  exact hG0

theorem index_eq_normalForm {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) {j : ℕ} {hj : j ≤ D.R.rS} {c : D.host.E}
    (hN : Formalism.HermitianLatticeCounting.S6.NFFull (nfF (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)) (nfF (frq X t.rep).fl (nf_T_ne D u)) j hj c) :
    jT t = j := by
  have hfin := hN.1.2.1
  rw [nf_II] at hfin
  unfold jT
  rw [hfin]
  omega

theorem realAbs_zero_eq_one (rd : ℝ) (τ : D.host.E →+* ℂ) (x : D.host.E) (hx : x = 1) :
    absReal rd τ D.R.rS 0 x = 1 := by
  subst hx
  simp [absReal, frameExp]

theorem delta_pos_le_height_sq (hPF : PFHost D) (large₂ : SizeData₂ D) {CH C : ℝ} (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C)
    {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) (ht : t ∈ relSet Y u) :
    0 < k2Del D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
  obtain ⟨hr, hG, -⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  have hjT := index_eq_normalForm t hN
  have hD : Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j ≠ 0 := (nf_gen _ _ _ _ j hj c hN).2.2.2.1
  have hlab : labT t (jT t) = Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j := by
    unfold labT
    rw [if_pos le_rfl, hjT]
  have hdel : k2Del D (jT t) (labT t) =
      ∏ τ : D.what₂.Tau, absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) ^ 2 := by
    unfold k2Del
    exact hPF _ _
  have hrd := pf_rd_pos D
  have hpos : ∀ τ, 0 < absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) := by
    intro τ
    unfold absReal
    rw [hlab]
    exact mul_pos (norm_pos_iff.2 ((map_ne_zero _).2 hD)) (Real.rpow_pos_of_pos hrd _)
  refine ⟨by rw [hdel]; exact Finset.prod_pos fun τ _ => pow_pos (hpos τ) 2, ?_⟩
  rw [hdel]
  have hb := two_le_scale_b D large₂
  have hH1 : 1 ≤ H1C large₂ CH := by
    unfold H1C
    exact Real.one_le_rpow (by linarith) (by positivity)
  unfold k2S
  rw [← Finset.prod_pow]
  refine Formalism.HermitianLatticeCounting.Final.S6.normSgBound D.what₂.Tau D.R.rS D.R.f _ _ (H1C large₂ CH) _ (szf_card_Tau D)
    (by linarith) (two_pow_le_height_bound _ CH C _ _ _ hb (two_rank_add_two_eq_m D) hCH hC) (fun τ => (hpos τ).le) (fun τ => ?_) (fun τ => ?_)
  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · rcases Nat.eq_zero_or_pos (jT t) with h0 | h0
    · have hl0 : labT t (jT t) = 1 := by
        rw [hlab, ← hjT, h0]
        unfold Dl leadMinorE
        simp
      have h1 : absReal D.host.rdE (embS D τ) D.R.rS (jT t) (labT t (jT t)) = 1 := by
        rw [h0] at hl0 ⊢
        exact realAbs_zero_eq_one _ _ _ hl0
      rw [h1]
      have h2 : (1 : ℝ) ≤ (2 * H1C large₂ CH) ^ (2 * D.R.rS) := one_le_pow₀ (by linarith)
      have h3 : (1 : ℝ) / (2 * H1C large₂ CH) ^ (2 * D.R.rS) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h2
      exact h3.trans ((Finset.le_fold_max _).2 (Or.inl le_rfl))
    · have hmem : jT t ∈ k2ends D (jT t) (labT t) := by
        unfold k2ends
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h0, le_rfl⟩, by rw [hlab]; exact hD⟩
      exact (Finset.le_fold_max _).2 (Or.inr ⟨jT t, hmem, le_rfl⟩)

theorem localNorm_le_height_sq (hPF : PFHost D) (large₂ : SizeData₂ D) {CH C : ℝ} (hCH : 0 ≤ CH) (hC : 2 * (CH + 1) ≤ C)
    {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) (l : ℕ) (hl : l ∈ k2ends D (jT t) (labT t)) :
    ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) ≤
      Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
  have hb := two_le_scale_b D large₂
  have hH1 : 1 ≤ H1C large₂ CH := by
    unfold H1C
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hrd := pf_rd_pos D
  rw [hPF]
  unfold k2S
  rw [← Finset.prod_pow]
  refine Formalism.HermitianLatticeCounting.Final.S6.normSgBound D.what₂.Tau D.R.rS D.R.f _ _ (H1C large₂ CH) _ (szf_card_Tau D)
    (by linarith) (two_pow_le_height_bound _ CH C _ _ _ hb (two_rank_add_two_eq_m D) hCH hC) (fun τ => ?_) (fun τ => ?_) (fun τ => ?_)
  · unfold absReal
    positivity
  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · exact (Finset.le_fold_max _).2 (Or.inr ⟨l, hl, le_rfl⟩)

end ZsC1b

theorem DelC_holds : DelC := by
  intro Cg cb Cw cT CT C0 CH hCH
  refine ⟨2 * (CH + 1), fun C hC => ⟨0, 0, fun C' Cl _ _ D large₂ X Y u hH _ t ht => ?_⟩⟩
  exact delta_pos_le_height_sq (PFHost_of_data D hH.1.2.1) large₂ hCH hC t ht

theorem NDlC_holds :
    ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
        ∀ t ∈ relSet Y u, ∀ l ∈ k2ends D (jT t) (labT t),
          ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) ≤
            Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
  intro Cg cb Cw cT CT C0 CH hCH
  refine ⟨2 * (CH + 1), fun C hC => ⟨0, 0, fun C' Cl _ _ D large₂ X Y u hH _ t _ l hl => ?_⟩⟩
  exact localNorm_le_height_sq (PFHost_of_data D hH.1.2.1) large₂ hCH hC t l hl

end Formalism.L2.SG.KappaOffDiagonal
