import Formalism.SharpRestriction.InertJacobiLevels.BTop2

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

structure LedHyp (D : D7) (sc : Scale) (aT bT : D.host.TT → ℤ) (η Cc Ct CGam : ℝ) (j0 : ℕ) : Prop where
  aT_win : ∀ t, sc.a ≤ (aT t : ℝ) ∧ (aT t : ℝ) ≤ sc.a + sc.a / ((D.R.k : ℝ) * sc.x ^ (Scale.A / 2))
  bT_ge : ∀ t, sc.b' ≤ (bT t : ℝ)
  top_u : ∀ τ (t : D.host.TT) (h0 : 0 < D.R.k), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (((D.hc τ).u ⟨0, h0⟩ : ℚ) : ℝ) = aT t + ((D.R.k : ℝ) - 1) / 2 ∧
    (((D.hc τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) = -(bT t : ℝ) - ((D.R.k : ℝ) - 1) / 2
  top_b : ∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) - (bT t : ℝ) > ((D.R.k : ℝ) - 1) / 2 + 3
  b_le : ∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ sc.b ^ 2
  untw : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0
  logFiveDepth_le : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0
  weightLength_ge_depth : 10 * j0 + 20 ≤ D.host.Lw
  split_tie : ⌊sc.x ^ (sc.ez / 5)⌋₊ ≤ D.host.splitBound
  o_tie : (D.R.o : ℝ) ≤ sc.x ^ (sc.eps / 100)
  QS_tie : (D.host.QS : ℝ) ≤ 4 * D.R.n * sc.x ^ (sc.eps / 100)
  secondTorsion_card_pos : 0 < D.host.T2.card
  secondTorsion_card_le : D.host.T2.card ≤ D.R.n
  win_thick : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
    sc.b ≤ wj D j τ ∧ wj D j τ ≤ sc.b + η + 1
  win_top : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (bT t : ℝ) + sc.b' / sc.x ≤ wj D j τ ∧ wj D j τ ≤ (bT t : ℝ) + sc.b' / sc.x + η
  win_thin : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) →
    sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ sc.w'' D.R.n + η
  cloud_gap : ∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
    (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ Cc * ((D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
  cloud_v : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
    (((D.hc τ).v i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  cloud_u : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
    0 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  be_close : ∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η
  eta_pos : 0 < η
  Del_pos : 0 < (D.s.Del : ℝ)
  t_win : 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ sc.x ^ Ct
  CGam_pos : 0 < CGam
  Gam_eq : ∀ u, Real.log (D.mem u).A.GamP = CGam * (D.R.m : ℝ) ^ 5 * D.R.f * sc.L

def baseL {D : D7} {sc : Scale} {aT bT : D.host.TT → ℤ} {η Cc Ct CGam : ℝ} {j0 : ℕ}
    (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S0 : Finset D.what₂.places.Pl) (E0 : D.what₂.Word → ℕ → D.what₂.places.Pl → ℝ)
    (hE0 : ∀ u j w, w ∉ S0 → E0 u j w = 0) : SizeData₂ D where
  sc := sc
  aT := aT
  aT_win := h.aT_win
  bT := bT
  bT_ge := h.bT_ge
  top_u := h.top_u
  top_b := h.top_b
  supp := S0
  gain := fun _ _ => 0
  F := fun _ _ => 0
  E := E0
  tau := fun _ => 0
  io := fun _ => 0
  gain_supp := fun _ _ _ => rfl
  F_supp := fun _ _ _ => rfl
  E_supp := hE0
  tau_supp := fun _ _ => rfl
  io_supp := fun _ _ => rfl
  gain_g := fun _ _ _ => rfl
  b_le := h.b_le
  untwisted := fun w hw j h1 h2 => ⟨h.untw w hw j h1 h2, rfl⟩
  not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
  drop := ∅
  drop_alt := fun _ => Set.notMem_empty _
  F_conj := fun _ _ => rfl
  F_above := by intros; rfl
  j0 := j0
  logFiveDepth_le := h.logFiveDepth_le
  weightLength_ge_depth := h.weightLength_ge_depth
  logDerivativeAtOne := dlogL D 1
  logDerivative_at_one_eq := rfl
  split_tie := h.split_tie
  o_tie := h.o_tie
  QS_tie := h.QS_tie
  NuLat := Nu
  de2 := (D.host.T2.card : ℝ) / D.R.n
  thickDensity_pos := by
    have h1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
    have h2 : (0 : ℝ) < D.host.T2.card := by exact_mod_cast h.secondTorsion_card_pos
    positivity
  thickDensity_le_one := by
    have h1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast (show 1 ≤ D.R.n from D.R.ord_pos)
    rw [div_le_one (by linarith)]
    exact_mod_cast h.secondTorsion_card_le
  typeDensity_eq_card_div := rfl
  LaG := 0
  Sc := (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  etaSz := η
  Cc := Cc
  win_thick := h.win_thick
  win_top := h.win_top
  win_thin := h.win_thin
  cloud_gap := h.cloud_gap
  cloud_v := h.cloud_v
  cloud_u := h.cloud_u
  be_close := h.be_close
  Sc_pos := by
    have h1 : (0 : ℝ) < D.R.k := by
      have := D.R.two_le_m; have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 0 < D.R.k)
    have := h.Del_pos
    positivity
  Sc_eq := rfl
  etaSz_pos := h.eta_pos
  TTw := fun _ => Finset.univ
  TTw_full := fun _ _ => rfl
  Ct := Ct
  t_win := h.t_win
  CGam := CGam
  CGam_pos := h.CGam_pos
  Gam_eq := h.Gam_eq
  wPart := fun _ _ _ _ => 1
  wPart_ge := fun _ _ _ _ => le_rfl
  lenMN := fun _ _ => 0

end Formalism.MainNotions.Inhab

end
