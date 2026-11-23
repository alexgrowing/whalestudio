import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt

noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Diag

def OneOn (S : Set ℝ) (gen : Bool) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (if gen then (Y.tO u u).genSet else (Y.tO u u).ngSet)) ≤
        gamL D large₂.sc.L C * ddC X Y u u

def OneAllOn (S : Set ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).nzSet) ≤ gamL D large₂.sc.L C * ddC X Y u u

def OneAll : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C : ℝ, 0 ≤ C ∧ ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (L : ℝ) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
      HD D L C' Cl Cg cb Cu cT CT → ConcTie X Y → (Y.tO u u).AbsConv →
      (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).nzSet) ≤ gamL D L C * ddC X Y u u

def SDiagOn (S : Set ℝ) (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C0 ∈ S, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), 1 ≤ large₂.CGam → TrueS D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → TFrameAt D →
      ∀ u, SDiagAt D u (gamL D large₂.sc.L CD) c

def GamRange (D : D7) (L : ℝ) : Prop :=
  (D.R.m : ℝ) ^ 5 * D.R.f * L ≤ Real.log (AdmissibleBoundsFromSource.Gam D) ∧ 8 * Real.log (AdmissibleBoundsFromSource.Gam D) ≤ D.R.k

def SDiagAtLed (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (L : ℝ), (∃ large₂ : SizeData₂ D, large₂.sc.L = L) → GamRange D L → TrueS D → HD D L C' Cl Cg cb Cu cT CT →
      ∀ u, SDiagAt D u (gamL D L CD) c

def SDiagG (c : ℝ) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ CD : ℝ, 1 ≤ CD ∧ ∃ thr : ℝ, ∀ C' Cl : ℝ, thr ≤ C' → thr ≤ Cl →
    ∀ (D : D7) (L : ℝ), GamRange D L → TrueS D → HD D L C' Cl Cg cb Cu cT CT → ∀ u, SDiagAt D u (gamL D L CD) c

theorem pow_five_mul_f_pos (D : D7) : (0 : ℝ) < (D.R.m : ℝ) ^ 5 * D.R.f := by
  have hf : 0 < D.R.f := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    unfold Ranks.f; omega
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  positivity

theorem gamRange_iff {D : D7} (large₂ : SizeData₂ D) :
    GamRange D large₂.sc.L ↔ 1 ≤ large₂.CGam ∧ 8 * large₂.CGam * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ D.R.k := by
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hp : (0 : ℝ) < (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := mul_pos (pow_five_mul_f_pos D) (by linarith)
  have hG : Real.log (AdmissibleBoundsFromSource.Gam D) = large₂.CGam * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by
    unfold AdmissibleBoundsFromSource.Gam; rw [large₂.Gam_eq D.u₀]; ring
  unfold GamRange
  rw [hG, le_mul_iff_one_le_left hp, mul_assoc 8]

theorem gammaRange_of_sizeHypotheses {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (h1 : 1 ≤ large₂.CGam)
    (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : GamRange D large₂.sc.L := by
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hp : (0 : ℝ) < (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := mul_pos (pow_five_mul_f_pos D) (by linarith)
  have h8 : 8 * large₂.CGam ≤ C' := h.1
  have hk : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := h.2.1
  refine (gamRange_iff large₂).2 ⟨h1, ?_⟩
  have := mul_le_mul_of_nonneg_right h8 hp.le
  linarith

theorem dataNW_of_window {D : D7} {C0 : ℝ} (h3 : 1 ≤ C0) (hd : StandingNumericalData D C0) : GlobalTheory.Core.Deg.DataNW D := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, w, r⟩ := hd
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, fun u => ?_, r⟩
  have hG : (0 : ℝ) < (D.mem u).A.GamP := lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hD : 0 < D.what₂.Dstar := D.Dstar_eq u ▸ (D.mem u).A.Dstar_pos
  have h0 : (0 : ℝ) < (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 :=
    div_pos (mul_pos (zpow_pos hG _) hD) (by linarith)
  have := lt_of_lt_of_le h0 (w u).1
  exact_mod_cast this

theorem hd_of_window {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (tf : TFrameAt D) : HD D large₂.sc.L C' Cl Cg cb Cu cT CT :=
  ⟨GlobalTheory.Core.Deg.hypL_of h.1, dataNW_of_window h.2.2 h.2.1, tf⟩

theorem sDiagG_of_sDiag {c : ℝ} (h : SDiag c) : SDiagG c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, a, b, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, max a b, fun C' Cl p q D L _ t hd =>
    H C' Cl (le_trans (le_max_left _ _) p) (le_trans (le_max_right _ _) q) D L t hd⟩

theorem sDiagAtLed_of_sDiagG {c : ℝ} (h : SDiagG c) : SDiagAtLed c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, thr, fun C' Cl p q D L _ g t hd => H C' Cl p q D L g t hd⟩

theorem sDiagOn_of_sDiagAtLed {c : ℝ} (h : SDiagAtLed c) (S : Set ℝ) : SDiagOn S c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, thr, fun C0 _ C' Cl p q D large₂ g t h0 tf =>
    H C' Cl p q D large₂.sc.L ⟨large₂, rfl⟩ (gammaRange_of_sizeHypotheses g h0.1) t (hd_of_window h0 tf)⟩

theorem sDiagOn_of_sDiag {c : ℝ} (h : SDiag c) (S : Set ℝ) : SDiagOn S c :=
  sDiagOn_of_sDiagAtLed (sDiagAtLed_of_sDiagG (sDiagG_of_sDiag h)) S

theorem SDiagOn.mono {S S' : Set ℝ} {c : ℝ} (hS : S ⊆ S') (h : SDiagOn S' c) : SDiagOn S c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, thr, fun C0 h0 => H C0 (hS h0)⟩

theorem OneOn.mono {S S' : Set ℝ} {gen : Bool} (hS : S ⊆ S') (h : OneOn S' gen) : OneOn S gen := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨C, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨C, hC, thr, fun C0 h0 => H C0 (hS h0)⟩

theorem OneAllOn.mono {S S' : Set ℝ} (hS : S ⊆ S') (h : OneAllOn S') : OneAllOn S := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨C, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨C, hC, thr, fun C0 h0 => H C0 (hS h0)⟩

theorem oneAllOn_of_oneAll (h : OneAll) (S : Set ℝ) : OneAllOn S := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨C, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨C, hC, thr, fun C0 _ C' Cl p q D large₂ X Y u t h0 ct ac =>
    H C' Cl p q D large₂.sc.L X Y u t (hd_of_window h0 ct.2.2.2.2.2.2.2) ct ac⟩

theorem oneOn_of_oneLed {gen : Bool} (h : OneLed gen) (S : Set ℝ) : OneOn S gen := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨C, hC, a, b, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨C, hC, max a b, fun C0 _ C' Cl p q D large₂ X Y u t h0 ct ac =>
    H C' Cl (le_trans (le_max_left _ _) p) (le_trans (le_max_right _ _) q) D large₂ X Y u t h0.1
      (dataNW_of_window h0.2.2 h0.2.1) ct ac⟩

example (D : D7) (L : ℝ) (h : GamRange D L) : 8 * ((D.R.m : ℝ) ^ 5 * D.R.f * L) ≤ D.R.k := by
  have := h.1; have := h.2; linarith

example (D : D7) : ∃ L₀ : ℝ, ∀ L, L₀ < L → ¬ GamRange D L := by
  refine ⟨Real.log (AdmissibleBoundsFromSource.Gam D) / ((D.R.m : ℝ) ^ 5 * D.R.f), fun L hL h => ?_⟩
  rw [div_lt_iff₀ (pow_five_mul_f_pos D)] at hL
  have := h.1
  linarith

example (D : D7) (h : 8 * Real.log (AdmissibleBoundsFromSource.Gam D) ≤ D.R.k) : ∃ L : ℝ, 0 < L ∧ GamRange D L := by
  refine ⟨Real.log (AdmissibleBoundsFromSource.Gam D) / ((D.R.m : ℝ) ^ 5 * D.R.f), div_pos (Real.log_pos (D.mem D.u₀).A.one_lt_gammaP) (pow_five_mul_f_pos D), ?_, h⟩
  rw [mul_div_cancel₀ _ (pow_five_mul_f_pos D).ne']

example (S : Set ℝ) (c : ℝ) (h : SDiagOn (S ∩ Set.Ici 1) c) : SDiagOn S c := by
  intro Cg cb Cu cT CT h1 h2
  obtain ⟨CD, hC, thr, H⟩ := h Cg cb Cu cT CT h1 h2
  exact ⟨CD, hC, thr, fun C0 h0 C' Cl p q D large₂ g t hh => H C0 ⟨h0, hh.2.2⟩ C' Cl p q D large₂ g t hh⟩
end GlobalTheory.Core.Diag
