import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcLgpLe

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def nc_Size (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  (∀ s, (al ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) s : ℝ) ≤ (2 * L.sc.a) ^ 2) ∧
  (∀ s, (lsz (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
    ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j s : ℝ) ≤ (2 * L.sc.a) ^ 4)

theorem nc_a_ge : (1 : ℝ) ≤ L.sc.a := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hL : 0 ≤ L.sc.L := by
    simp only [Formalism.BasicNotions.Scale.L]
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ L.sc.b := by
    simp only [Formalism.BasicNotions.Scale.b]
    exact Real.one_le_exp hL
  simp only [Formalism.BasicNotions.Scale.a]
  exact one_le_mul_of_one_le_of_one_le hx.le hb

theorem nc_de (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (hT : GatTies D)
    (hL : Formalism.MainNotions.G.LatTied hT X Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D)
    (h1 : 9 ≤ K.dl1) (h2 : 9 ≤ K.dl2) (hlog : 1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a))
    (hS : nc_Size D L Y u w hg t0 j) : nc_De D L X Y K u w hg t0 j := by
  have hp : 2 ≤ D.what₂.places.resChar w := hg.1.two_le
  have hA : (1 : ℝ) ≤ 2 * L.sc.a := by have := nc_a_ge (L := L); linarith
  have hmt := (hL u w hg)
  have ht : (Y.Fl u w hg).t = D.R.t := hmt.2.1
  have hk := hT.gat_k u w hg
  have hjm : j ≤ D.R.m := (Finset.mem_Icc.1 hj).2
  have hN1 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold NN Ranks.N
    rw [ht]
    have : (D.gat u w hg).P.m + 1 + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
      rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjm) _
    exact_mod_cast this
  have hN0 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t (j - 1) : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold NN Ranks.N
    rw [ht]
    have : (D.gat u w hg).P.m + 1 + (j - 1) * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
      rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    exact_mod_cast this
  have hde := nc_de_le (D.what₂.places.resChar w) (Y.Fl u w hg).t _ _ _ j hp (2 * L.sc.a) (D.R.N D.R.m : ℝ) hA hlog
    hN1 hN0 hS.1 hS.2
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hNv : (Formalism.MainNotions.G.Nv X (D.what₂.places.resChar w) t0 : ℝ) = ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card := by
    unfold Formalism.MainNotions.G.Nv
    rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.card_image_of_injective _ hinj]
  have hnP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := by
    unfold Formalism.MainNotions.G.nP
    rw [if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]
  unfold nc_De Formalism.MainNotions.G.dl Formalism.MainNotions.G.Nm
  rw [hNv, hnP]
  have hl0 : 0 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) := by linarith
  have hc1 : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) * (D.R.N D.R.m : ℝ) ^ 2 *
      Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) := by positivity
  have hc2 : (0 : ℝ) ≤ (((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card : ℝ) *
      Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) ^ 2 := by positivity
  nlinarith

end Formalism.MainNotions.FormalGroupSystem.Pf
