import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsFibres
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsSiz
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lab

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def pairCountExponentShift (D : D7) (c Ch : ℝ) : ℝ :=
  c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f + 4 * (max (Ch - c) 0 * (D.R.m : ℝ) ^ 2 * D.R.f * ((D.R.rS : ℝ) + 1))

def pairCountExponent (D : D7) (c : ℝ) (s : ℕ) : ℝ := c * ((s : ℝ) + D.R.m) * D.R.m + c * cF D.R.f

theorem rows_gg_eq (D : D7) : gg D = (gS D : ℝ) := by unfold gg gS; push_cast; ring

theorem rows_Tr_pos (D : D7) (w : D.what₂.Word) : 0 < Tr D w := by
  unfold Tr; exact_mod_cast (D.mem w).A.T_prime.pos

theorem rows_NT_pos (D : D7) (w : D.what₂.Word) : 0 < NT D w := by
  unfold NT; exact pow_pos (rows_Tr_pos D w) _

def wordPairGramGood (X : TermTie D) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (c : ℝ) (Z : GramM D) : Prop :=
  ∃ t : D.s.Term u u', D.s.Gterm t ≠ 0 ∧ D.s.relevant t ∧ ZEquiv (termGramMatrix X t) Z ∧
    ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
      ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ HHZ D large₂.sc.b c (termGramMatrix X t)

open Classical in

def termReducedGramMatrix {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (t : D.s.Term u u') : GramM D :=
  if h : D.s.Gterm t ≠ 0 ∧ D.s.relevant t then Classical.choose (rows_reduced_exists Y hH hHH t h.1 h.2) else 0

theorem rows_Zr_spec {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) :
    ZEquiv (termGramMatrix X t) (termReducedGramMatrix Y hH hHH t) ∧ wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y hH hHH t) := by
  have h := Classical.choose_spec (rows_reduced_exists Y hH hHH t hG hrel)
  have e : termReducedGramMatrix Y hH hHH t = Classical.choose (rows_reduced_exists Y hH hHH t hG hrel) := by
    unfold termReducedGramMatrix; rw [dif_pos ⟨hG, hrel⟩]
  rw [e]
  exact ⟨h.1, t, hG, hrel, h.1, h.2⟩

theorem rows_Gz_pos (hT : TermPtsTie X Y) (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) (τ : D.what₂.Tau) : 0 < Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ := by
  obtain ⟨h1, _, _, _⟩ := hT t hG hrel
  obtain ⟨hz, hz', hTz, hTz', hR⟩ := h1 τ
  rw [← d_Gf_eq Y hrd t τ]
  exact lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS _ _ hz hz' (hTz ▸ rows_Tr_pos D u) (hTz' ▸ rows_Tr_pos D u') _ hR.1)
    (Ne.symm hR.2.2)

theorem two_le_gg_of_count_hypotheses {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) : 2 ≤ gg D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, h14, _⟩ := hH.1
  have hb := d_two_le_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have h0 : (2 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have : (2 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
    calc (2 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := this
      _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
  have g1 : (2 : ℝ) ≤ D.host.g 0 := h0.trans h12
  have g2 : (2 : ℝ) ≤ D.host.g 1 := h0.trans h14
  unfold gg
  nlinarith

theorem gramProductG0_pos {C' Cl Cg cb Cu cT CT C0 c : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hT : TermPtsTie X Y)
    {Z : GramM D} (hZ : wordPairGramGood X u u' large₂ c Z) : 0 < wordPairGramProduct D u u' Z := by
  obtain ⟨t, hG, hrel, hE, _⟩ := hZ
  rw [gramProductG0_equiv_invariant hE]
  unfold wordPairGramProduct
  have hg : 0 < (gS D : ℝ) := by rw [← rows_gg_eq]; linarith [two_le_gg_of_count_hypotheses hH]
  exact mul_pos (Finset.prod_pos fun τ _ => rows_Gz_pos Y hT (d_rdE_pos hH) t hG hrel τ) (by positivity)

theorem rows_one_le_HHZ (D : D7) (large₂ : SizeData₂ D) {c : ℝ} (hc : 0 ≤ c) (Z : GramM D) : 1 ≤ HHZ D large₂.sc.b c Z := by
  unfold HHZ
  have hb := d_two_le_b D large₂
  have h1 : 1 ≤ (large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) :=
    Real.one_le_rpow (Real.one_le_rpow (by linarith) (by positivity)) (by positivity)
  have h2 : 1 ≤ sizeZ D large₂.sc.b c Z ^ 4 := one_le_pow₀ (rows_one_le_sizeZ _ _ _)
  nlinarith

theorem gramProductG0_le_height {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hT : TermPtsTie X Y)
    {Z : GramM D} (hZ : wordPairGramGood X u u' large₂ c Z) : wordPairGramProduct D u u' Z ≤ HHZ D large₂.sc.b c Z := by
  obtain ⟨t, hG, hrel, hE, _⟩ := hZ
  rw [gramProductG0_equiv_invariant hE, rows_HHZ_inv hE]
  have hR : RelZ D (ZhatL (lf D Y.F0) (X.fl' t)) := by
    have h := X.pt_cell t hG hrel
    rw [Y.fl_eq t] at h
    exact ⟨_, h⟩
  obtain ⟨_, h2, _⟩ := hHH hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero (X.abelian₂ t) (Y.isRows.1 _ (Y.Lam_mem t)) (X.fl' t)
    (rows_isTermF Y t hG) hR
  rw [← Y.fl_eq t] at h2
  have hg := two_le_gg_of_count_hypotheses hH.1
  rw [rows_gg_eq] at hg
  have hp : ∀ τ, 0 < Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ := fun τ => rows_Gz_pos Y hT (d_rdE_pos hH.1) t hG hrel τ
  have h3 : ∏ τ, Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ ≤ HHZ D large₂.sc.b c (termGramMatrix X t) :=
    le_trans (Finset.prod_le_prod (fun τ _ => (hp τ).le) fun τ _ => le_max_right _ _) h2
  unfold wordPairGramProduct
  have h4 : ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f) ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  calc (∏ τ, Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)
      ≤ (∏ τ, Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) * 1 :=
        mul_le_mul_of_nonneg_left h4 (Finset.prod_nonneg fun τ _ => (hp τ).le)
    _ ≤ _ := by rw [mul_one]; exact h3

theorem rows_massS_nonneg (D : D7) (j : ℕ) : 0 ≤ massS D j := by
  unfold massS massU; exact d_mass_nonneg _ _

theorem rows_XiS_nonneg (D : D7) (w : D.what₂.Word) {HH c : ℝ} (hHH : 0 ≤ HH) (hc : 0 ≤ c) (s : ℕ) : 0 ≤ XiS D w HH c s := by
  unfold XiS Xi
  have hN := (rows_NT_pos D w).le
  split_ifs
  · exact div_nonneg (mul_nonneg (rows_massS_nonneg D _) (rows_massS_nonneg D _)) (rows_massS_nonneg D _)
  · positivity
  · exact le_rfl

theorem rows_Xi_le (D : D7) (w : D.what₂.Word) {HH P2 σ c : ℝ} (hHH : 0 ≤ HH) (hP2 : 0 ≤ P2) (hσ : 1 ≤ σ) (hc : 0 ≤ c)
    (h : HH ≤ P2 * σ ^ 4) (s : ℕ) : XiS D w HH c s ≤ XiS D w P2 c s * σ ^ (4 * (c * D.R.k)) := by
  have hσ0 : 0 < σ := by linarith
  have h1 : 1 ≤ σ ^ (4 * (c * D.R.k)) := Real.one_le_rpow hσ (by positivity)
  have hN := (rows_NT_pos D w).le
  unfold XiS Xi
  split_ifs
  · exact le_mul_of_one_le_right
      (div_nonneg (mul_nonneg (rows_massS_nonneg D _) (rows_massS_nonneg D _)) (rows_massS_nonneg D _)) h1
  · have e : (HH * NT D w) ^ (c * D.R.k) ≤ (P2 * NT D w) ^ (c * D.R.k) * σ ^ (4 * (c * D.R.k)) := by
      calc (HH * NT D w) ^ (c * D.R.k) ≤ ((P2 * NT D w) * σ ^ 4) ^ (c * (D.R.k : ℝ)) := by
            apply Real.rpow_le_rpow (by positivity) _ (by positivity)
            calc HH * NT D w ≤ (P2 * σ ^ 4) * NT D w := mul_le_mul_of_nonneg_right h hN
              _ = (P2 * NT D w) * σ ^ 4 := by ring
        _ = (P2 * NT D w) ^ (c * D.R.k) * σ ^ (4 * (c * D.R.k)) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast σ 4, ← Real.rpow_mul hσ0.le]
            norm_num
    calc (c * D.R.k) ^ (D.R.k * D.R.f) * (HH * NT D w) ^ (c * D.R.k)
        ≤ (c * D.R.k) ^ (D.R.k * D.R.f) * ((P2 * NT D w) ^ (c * D.R.k) * σ ^ (4 * (c * D.R.k))) :=
          mul_le_mul_of_nonneg_left e (by positivity)
      _ = _ := by ring
  · simp

theorem rows_c3B_nonneg (D : D7) (large₂ : SizeData₂ D) (w : D.what₂.Word) {c : ℝ} (hc : 0 ≤ c) (Z' Z'' : GramM D) (s : ℕ) {De : ℝ}
    (hDe : 0 ≤ De) : 0 ≤ wordSublatticeTripleBound D large₂ w c Z' Z'' s De := by
  unfold wordSublatticeTripleBound
  have h1 := rows_one_le_HHZ D large₂ hc Z'
  have h2 := rows_one_le_HHZ D large₂ hc Z''
  have hN := rows_NT_pos D w
  have hX := rows_XiS_nonneg D w (HH := HHZ D large₂.sc.b c Z' * HHZ D large₂.sc.b c Z'') (by nlinarith) hc s
  have h3 : 0 ≤ HHZ D large₂.sc.b c Z' * HHZ D large₂.sc.b c Z'' := by nlinarith
  positivity

end Lab

end Formalism.MainNotions.BridgeLemma₂

end
