import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyThickCardLeCyclicOrder
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.DataParams

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (tops)

noncomputable section
namespace GlobalTheory.LvT.WtSign

theorem m_pos (R : Ranks) : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m

theorem k_pred_lt (R : Ranks) : R.k - 1 < R.k := by have := R.m_add_three_le_k; omega

def uLast {R : Ranks} (P : HCParam R) : ℚ := P.u ⟨R.k - 1, k_pred_lt R⟩

def eFirst {R : Ranks} (P : HCParam R) : ℚ := P.e ⟨0, m_pos R⟩

def SignLaw {R : Ranks} {ι : Type} (hc : ι → HCParam R) (top : ι → Prop) : Prop :=
  (∀ τ, top τ → uLast (hc τ) ≤ -(((R.k : ℚ) - 1) / 2)) ∧ ∀ τ, (R.k : ℚ) / 2 ≤ eFirst (hc τ)

theorem e_ge {R : Ranks} (P : HCParam R) (i : ℕ) (hi : i < R.m) :
    eFirst P + (i : ℚ) * ((R.t : ℚ) + 3) ≤ P.e ⟨i, hi⟩ := by
  induction i with
  | zero => simp [eFirst]
  | succ i ih =>
    have h1 := ih (by omega)
    have h2 := P.gap_eb ⟨i, by omega⟩ hi
    have h3 := P.gap_be ⟨i + 1, hi⟩
    push_cast
    simp only at h2
    linarith

theorem sExp_nonneg {R : Ranks} (P : HCParam R) (h : (R.k : ℚ) / 2 ≤ eFirst P) (i : ℕ) (hi : i < R.m) :
    0 ≤ sExp R (P.e ⟨i, hi⟩) (i + 1) := by
  have h1 := e_ge P i hi
  have h2 : (0 : ℚ) ≤ (i : ℚ) * (R.t : ℚ) := by positivity
  have h3 : (0 : ℚ) ≤ (i : ℚ) := by positivity
  simp only [sExp, Ranks.N, Nat.add_sub_cancel]
  push_cast
  nlinarith

theorem eFirst_ge_of_uLast_le {R : Ranks} (P : HCParam R) (h : uLast P ≤ -(((R.k : ℚ) - 1) / 2)) :
    (R.k : ℚ) / 2 ≤ eFirst P := by
  have h1 := P.u_last_gt (by have := k_pred_lt R; omega) (m_pos R)
  have h2 := P.gap_be ⟨0, m_pos R⟩
  have h3 : (0 : ℚ) ≤ R.t := by positivity
  unfold uLast at h
  unfold eFirst
  linarith

theorem eFirst_ge_of_uLast_nonpos {R : Ranks} (P : HCParam R) (h : uLast P ≤ 0) : (R.k : ℚ) / 2 ≤ eFirst P := by
  have h1 := P.u_last_gt (by have := k_pred_lt R; omega) (m_pos R)
  have h2 := P.gap_be ⟨0, m_pos R⟩
  have h5 : (R.k : ℚ) ≤ R.t := by
    have := R.rank_add_five_le
    exact_mod_cast (by omega : R.k ≤ R.t)
  unfold uLast at h
  unfold eFirst
  linarith

theorem eFirst_ge_of_b_le {R : Ranks} (P : HCParam R)
    (h : P.b ⟨R.m - 1, by have := m_pos R; omega⟩ ≤ 2 * P.b ⟨0, m_pos R⟩) : (R.k : ℚ) / 2 ≤ eFirst P := by
  have hm := R.two_le_m
  have h1 := e_ge P (R.m - 2) (by omega)
  have h2 := P.gap_eb ⟨R.m - 2, by omega⟩ (by simp only; omega)
  have e : (⟨R.m - 2 + 1, by omega⟩ : Fin R.m) = ⟨R.m - 1, by omega⟩ := Fin.ext (by simp only; omega)
  simp only [e] at h2
  have h3 := P.gap_be ⟨0, m_pos R⟩
  have h4 : (0 : ℚ) ≤ ((R.m - 2 : ℕ) : ℚ) * ((R.t : ℚ) + 3) := by positivity
  have h5 : (R.k : ℚ) ≤ R.t := by
    have := R.rank_add_five_le
    exact_mod_cast (by omega : R.k ≤ R.t)
  have h6 : (0 : ℚ) ≤ R.t := by positivity
  unfold eFirst at h1 ⊢
  linarith

variable {D : D7} {u : D.what₂.Word}

theorem bTop_cast (X : Ch D u) (τ : D.what₂.Tau) :
    (X.fm.bTop τ : ℚ) = -uLast (D.hc τ) - ((D.R.k : ℚ) - 1) / 2 := by
  have hk := k_pred_lt D.R
  have hN : D.R.N 0 = D.R.k := by simp [Ranks.N]
  have h := X.fm.lam_eq 0 (Nat.zero_le _) τ ⟨D.R.N 0 - 1, by omega⟩
  rw [dif_pos (show D.R.N 0 - 1 < D.R.k by omega)] at h
  have e : (⟨D.R.N 0 - 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hk⟩ := Fin.ext (by simp only; omega)
  simp only [e, hcToWeightQ, rhoVec] at h
  rw [D.hcW_last u τ (by omega), Nat.cast_sub (by omega)] at h
  unfold MemberForms.bTop DomWeight.detShift uLast
  rw [dif_pos (D.R.N_pos 0)]
  push_cast at h ⊢
  rw [h, show (D.R.N 0 : ℚ) = D.R.k by exact_mod_cast hN]
  ring

theorem sDiv_cast (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    (X.C.sDiv i τ : ℚ) = sExp D.R ((D.hc τ).e ⟨i, hi⟩) (i + 1) := by
  rw [X.C.sDiv_eq i hi τ, D.hcW_e]

theorem wtSigns_iff (X : Ch D u) : TwColumn.WtSigns X ↔ SignLaw D.hc (· ∈ tops D) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ hτ => ?_, fun τ => ?_⟩
    · have h : (0 : ℚ) ≤ (X.fm.bTop τ : ℚ) := by exact_mod_cast h1 τ hτ
      rw [bTop_cast] at h
      linarith
    · have h : (0 : ℚ) ≤ (X.C.sDiv 0 τ : ℚ) := by exact_mod_cast h2 0 (m_pos _) τ
      rw [sDiv_cast X 0 (m_pos _)] at h
      simp only [sExp, Ranks.N, Nat.add_sub_cancel, zero_mul, add_zero] at h
      unfold eFirst
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ hτ => ?_, fun i hi τ => ?_⟩
    · have h : (0 : ℚ) ≤ (X.fm.bTop τ : ℚ) := by
        rw [bTop_cast]
        linarith [h1 τ hτ]
      exact_mod_cast h
    · have h : (0 : ℚ) ≤ (X.C.sDiv i τ : ℚ) := by
        rw [sDiv_cast X i hi]
        exact sExp_nonneg _ (h2 τ) i hi
      exact_mod_cast h

theorem mem_tops (τ : D.what₂.Tau) : τ ∈ tops D ↔ (D.eTau τ : D.R.GG) ∈ D.host.topPlaces := by
  simp [tops, topsOf]

theorem b'_pos (s : Scale) : 0 < s.b' := by
  have := s.one_lt_alt
  unfold Scale.b' Scale.a Scale.b Scale.X'
  positivity

theorem w''_le_b (s : Scale) (n : ℕ) (hn : 0 < n) : s.w'' n ≤ s.b := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have hb : 0 < s.b := Real.exp_pos _
  have hX : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold Scale.w'' Scale.b' Scale.a
  rw [div_div, div_le_iff₀ (by positivity)]
  have h1 : 1 ≤ s.X' * n := one_le_mul_of_one_le_of_one_le hX hn'
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_pos hx hb).le
  nlinarith

theorem uLast_le (L : SizeData₂ D) (τ : D.what₂.Tau) (hτ : τ ∈ tops D) :
    uLast (D.hc τ) ≤ -(((D.R.k : ℚ) - 1) / 2) := by
  have h1 := (mem_tops τ).1 hτ
  unfold Host.topPlaces at h1
  obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
  have h2 := (L.top_u τ ⟨t, ht⟩ (by have := k_pred_lt D.R; omega) e.symm).2
  have h3 := L.bT_ge ⟨t, ht⟩
  have h4 := b'_pos L.sc
  have h5 : ((uLast (D.hc τ) : ℚ) : ℝ) ≤ ((-(((D.R.k : ℚ) - 1) / 2) : ℚ) : ℝ) := by
    unfold uLast
    rw [h2]
    push_cast
    linarith
  exact_mod_cast h5

theorem w''_le_eFirst (L : SizeData₂ D) (τ : D.what₂.Tau) (hτ : τ ∉ tops D) :
    L.sc.w'' D.R.n ≤ ((eFirst (D.hc τ) : ℚ) : ℝ) := by
  have e : wj D 1 τ = ((eFirst (D.hc τ) : ℚ) : ℝ) := by
    unfold wj eFirst
    rw [dif_pos (show 1 - 1 < D.R.m from m_pos _)]
  rw [← e]
  by_cases h : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
  · exact (w''_le_b L.sc _ (by unfold Ranks.n; positivity)).trans (L.win_thick 1 le_rfl (m_pos _) τ h).1
  · exact (L.win_thin 1 le_rfl (m_pos _) τ ⟨(D.eTau τ).2, fun h' => hτ ((mem_tops τ).2 h'), h⟩).1

theorem signLaw_of_le (L : SizeData₂ D) (h : (D.R.k : ℝ) ≤ 2 * L.sc.w'' D.R.n) : SignLaw D.hc (· ∈ tops D) := by
  refine ⟨uLast_le L, fun τ => ?_⟩
  by_cases hτ : τ ∈ tops D
  · exact eFirst_ge_of_uLast_le _ (uLast_le L τ hτ)
  · have h1 := w''_le_eFirst L τ hτ
    have h2 : (((D.R.k : ℚ) / 2 : ℚ) : ℝ) ≤ ((eFirst (D.hc τ) : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h2

theorem wtSigns_of_le (L : SizeData₂ D) (h : (D.R.k : ℝ) ≤ 2 * L.sc.w'' D.R.n) (X : Ch D u) : TwColumn.WtSigns X :=
  (wtSigns_iff X).2 (signLaw_of_le L h)

theorem wtSigns_of_par : ∀ (D : D7) (L : SizeData₂ D), Formalism.MainNotions.GL3Columns.WTPar D L →
    ∀ (u : D.what₂.Word) (X : Ch D u), TwColumn.WtSigns X := fun D L h _ X =>
  wtSigns_of_le L (by
    have h1 := h.k4
    have h2 : (0 : ℝ) ≤ D.R.k := by positivity
    linarith) X

theorem wtSigns_of_sizeBm (L : SizeData₂ D) (h : Formalism.MainNotions.SizeBm L) (X : Ch D u) : TwColumn.WtSigns X :=
  (wtSigns_iff X).2 ⟨uLast_le L, fun τ => eFirst_ge_of_b_le _ (by exact_mod_cast h τ (m_pos _))⟩

theorem wtSigns_of_sizesAt (L : SizeData₂ D) (h : Formalism.MainNotions.SizesAt L) (X : Ch D u) : TwColumn.WtSigns X :=
  wtSigns_of_sizeBm L h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 X

theorem wtSigns_of_params (L : SizeData₂ D) (P : ParameterChoice' D L) (X : Ch D u) : TwColumn.WtSigns X :=
  (wtSigns_iff X).2 ⟨uLast_le L, fun τ => eFirst_ge_of_b_le _ (P.bm_le τ (m_pos _))⟩

section Chosen

open GlobalTheory.Mem.Num

theorem signLaw_of_inAt (C : Formalism.MainNotions.Inhab.FC) (s : Scale) {R : Ranks} (H : Host R) (a b : R.A → ℤ) (δ : ℕ → Bool)
    (hb : ∀ t ∈ H.TT, 0 ≤ b t) {ι : Type} (g : ι → R.GG) (hc : ι → HCParam R)
    (h : ∀ τ, ∃ h : (inAt C s H a b δ (g τ)).OK R, hc τ = (inAt C s H a b δ (g τ)).hc R h) :
    SignLaw hc fun τ => g τ ∈ H.topPlaces := by
  have hk := R.m_add_three_le_k
  have hu : ∀ τ, uLast (hc τ) = ((inAt C s H a b δ (g τ)).Uk : ℚ) + 1 / 2 := fun τ => by
    obtain ⟨h1, h2⟩ := h τ
    rw [h2]
    show (((inAt C s H a b δ (g τ)).uZ R (R.k - 1) : ℤ) : ℚ) + 1 / 2 = _
    unfold HCIn.uZ
    rw [if_neg (by omega), if_pos (by omega)]
  refine ⟨fun τ hτ => ?_, fun τ => eFirst_ge_of_uLast_nonpos _ ?_⟩
  · obtain ⟨t, ht, e⟩ := Chosen.top_ex H hτ
    have h1 : (0 : ℚ) ≤ (b t : ℚ) := by exact_mod_cast hb t ht
    obtain ⟨c, hc2⟩ := R.k_even
    have h2 : R.k / 2 = c := by omega
    have h3 : (R.k : ℚ) = c + c := by exact_mod_cast hc2
    have h4 : (inAt C s H a b δ (g τ)).Uk = -b t - (c : ℤ) := by
      simp only [inAt, if_pos hτ, h2]
      rw [e, Chosen.iota_inv]
    rw [hu, h4, h3]
    push_cast
    linarith
  · have h1 : ((inAt C s H a b δ (g τ)).Uk : ℚ) ≤ -1 := by exact_mod_cast (h τ).1.2.2.2.1
    rw [hu]
    linarith

theorem wtSigns_of_dChosen {C : Formalism.MainNotions.Inhab.FC} {s : Scale} {a b : D.R.A → ℤ} (h : DChosen C s D a b)
    (X : Ch D u) : TwColumn.WtSigns X := by
  have hb : ∀ t ∈ D.host.TT, 0 ≤ b t := fun t ht => by
    have h1 := (b'_pos s).le.trans (h.wt t ht).2.1
    exact_mod_cast h1
  have h1 := signLaw_of_inAt C s D.host a b (Formalism.MainNotions.wordBits D D.u₀) hb (fun τ => (D.eTau τ : D.R.GG)) D.hc
    fun τ => by rw [← D.hcW_base]; exact h.hc D.u₀ τ
  exact (wtSigns_iff X).2 ⟨fun τ hτ => h1.1 τ ((mem_tops τ).1 hτ), h1.2⟩

theorem wtSigns_of_lChosen {C : Formalism.MainNotions.Inhab.FC} {L : SizeData₂ D} (h : LChosen C L) (X : Ch D u) : TwColumn.WtSigns X :=
  wtSigns_of_dChosen h.d X

end Chosen

open GlobalTheory.Mem

def BaseSigns (B : Base) : Prop := SignLaw B.hc (· ∈ B.wts.tops)

theorem wtSigns_assemble_iff (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (u : B.Word) (X : Ch (assemble B C W V S N G) u) :
    TwColumn.WtSigns X ↔ BaseSigns B := by
  have e : ∀ τ, τ ∈ tops (assemble B C W V S N G) ↔ τ ∈ B.wts.tops := fun τ =>
    (mem_tops (D := assemble B C W V S N G) τ).trans (B.mem_wts_tops τ).symm
  exact (wtSigns_iff (D := assemble B C W V S N G) X).trans
    (and_congr (forall_congr' fun τ => imp_congr (e τ) Iff.rfl) Iff.rfl)

open GlobalTheory.Mem.Num in

theorem baseSigns_of_inAt (B : Base) (C : Formalism.MainNotions.Inhab.FC) (s : Scale) (a b : B.R.A → ℤ) (δ : ℕ → Bool)
    (hb : ∀ t ∈ B.host.TT, 0 ≤ b t)
    (h : ∀ τ : Tau B.R, ∃ h : (inAt C s B.host a b δ (τ : B.R.GG)).OK B.R,
      B.hc τ = (inAt C s B.host a b δ (τ : B.R.GG)).hc B.R h) : BaseSigns B := by
  have h1 := signLaw_of_inAt C s B.host a b δ hb (fun τ : Tau B.R => (τ : B.R.GG)) B.hc h
  exact ⟨fun τ hτ => h1.1 τ ((B.mem_wts_tops τ).1 hτ), h1.2⟩

def shift {R : Ranks} (P : HCParam R) (z : ℤ) : HCParam R where
  u i := P.u i + z
  v i := P.v i + z
  b j := P.b j - z
  e j := P.e j - z
  u_gt_v i := by linarith [P.u_gt_v i]
  v_gt_u i := by linarith [P.v_gt_u i]
  u_last_gt h h' := by linarith [P.u_last_gt h h']
  gap_be j := by linarith [P.gap_be j]
  gap_eb j h := by linarith [P.gap_eb j h]
  e_int j := (P.e_int j).elim fun y hy => ⟨y - z, by rw [hy]; push_cast; ring⟩
  u_half i := (P.u_half i).elim fun y hy => ⟨y + z, by rw [hy]; push_cast; ring⟩
  v_int i := (P.v_int i).elim fun y hy => ⟨y + z, by rw [hy]; push_cast; ring⟩
  b_int j := (P.b_int j).elim fun y hy => ⟨y - z, by rw [hy]; push_cast; ring⟩

theorem exists_shift_not {R : Ranks} (P : HCParam R) :
    ∃ z : ℤ, -(((R.k : ℚ) - 1) / 2) < uLast (shift P z) ∧ eFirst (shift P z) < (R.k : ℚ) / 2 := by
  obtain ⟨z, hz⟩ := exists_int_gt (max (eFirst P) (1 - uLast P))
  have h1 := (le_max_left _ _).trans_lt hz
  have h2 := (le_max_right _ _).trans_lt hz
  have h3 : (0 : ℚ) ≤ R.k := by positivity
  refine ⟨z, ?_, ?_⟩
  · show _ < uLast P + z
    linarith
  · show eFirst P - z < _
    linarith

end GlobalTheory.LvT.WtSign
