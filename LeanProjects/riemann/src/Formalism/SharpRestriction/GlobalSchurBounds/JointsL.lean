import Formalism.SharpRestriction.GlobalSchurBounds.JointsF
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions

theorem jnt_logXu (D : D7) (hDu : StandardLattice.FactDuStar D) (hDs : StandardLattice.FactDstar D) (u : D.what₂.Word) :
    Real.log (D.mem u).A.Xu = StandardLattice.logXuD D u := by
  unfold ColumnsAtT.Xu StandardLattice.logXuD StandardLattice.logXu
  rw [Real.log_rpow (div_pos (D.mem u).A.Dstar_pos (by exact_mod_cast (D.mem u).A.duStar_pos)),
    D.Dstar_eq u, hDs, hDu u]

theorem count_at_of (D : D7) (L : SizeData₂ D) (C0 C Δ : ℝ)
    (h5c : StandardLattice.TorusPairsWithVariant D L.sc C0 C) (h5v : StandardLattice.VandermondeVariationBound D L.sc C0 C)
    (hB : StandardLattice.DataB D L.sc C0 Δ (fun j ρ => wj D (j + 1) ρ))
    (hDu : StandardLattice.FactDuStar D) (hDs : StandardLattice.FactDstar D)
    (hΓ : ∀ u, Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ 1) :
    Lnk.Count_at L (max C 0 + 2) := by
  have hv : Real.pi ≤ D.host.v := hB.1
  have hx := L.sc.one_lt_alt
  have hk3 : (3 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 3 ≤ D.R.k)
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := D.R.toFrame.ord_pos
      omega
    exact_mod_cast this
  have hfk : 1 ≤ (D.R.f : ℝ) * D.R.k := by nlinarith
  have hfk0 : 0 < (D.R.f : ℝ) * D.R.k := by linarith
  have hm0 : 0 ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx.le L.sc.eps_pos.le
  have hLa : L.sc.L ≤ L.La := by
    have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
    have hrd1 : 1 ≤ D.host.rdE := by rw [hrd]; linarith [Real.pi_gt_three]
    have he : 0 < Real.exp L.sc.L := Real.exp_pos _
    have h1 : Real.exp L.sc.L ≤ L.sc.x * Real.exp L.sc.L * D.host.rdE := by
      have h2 : Real.exp L.sc.L ≤ L.sc.x * Real.exp L.sc.L := by nlinarith
      nlinarith
    have h3 := Real.log_le_log he h1
    rw [Real.log_exp] at h3
    exact h3
  have hlogk : 1 ≤ Real.log D.R.k := by
    have h1 : Real.exp 1 ≤ (D.R.k : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hCm : C ≤ max C 0 := le_max_left _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hXpos : ∀ u, 0 < (D.mem u).A.Xu := fun u =>
    Real.rpow_pos_of_pos (div_pos (D.mem u).A.Dstar_pos (by exact_mod_cast (D.mem u).A.duStar_pos)) _
  have hexp : ∀ u, Real.exp (StandardLattice.logXuD D u) = (D.mem u).A.Xu := fun u => by
    rw [← jnt_logXu D hDu hDs u, Real.exp_log (hXpos u)]
  have hGpos : ∀ u, 0 < (D.mem u).A.GamP := fun u => lt_trans one_pos (D.mem u).A.one_lt_gammaP
  have hTs : ∀ u, (D.mem u).A.Tstar =
      (D.mem u).A.Xu * (D.mem u).A.GamP ^ (-(2 : ℝ) / ((D.R.f : ℝ) * D.R.k)) := fun u => rfl
  have hTspos : ∀ u, 0 < (D.mem u).A.Tstar := fun u => by
    rw [hTs]; exact mul_pos (hXpos u) (Real.rpow_pos_of_pos (hGpos u) _)
  have hlogTs : ∀ u, Real.log (D.mem u).A.Tstar = StandardLattice.logXuD D u +
      -(2 : ℝ) / ((D.R.f : ℝ) * D.R.k) * Real.log (D.mem u).A.GamP := fun u => by
    rw [hTs, Real.log_mul (hXpos u).ne' (Real.rpow_pos_of_pos (hGpos u) _).ne',
      Real.log_rpow (hGpos u), jnt_logXu D hDu hDs u]
  have hwin : ∀ u, Real.log (D.mem u).A.Tstar ≤ Real.log ((D.mem u).A.T : ℝ) ∧
      Real.log ((D.mem u).A.T : ℝ) ≤ Real.log (D.mem u).A.Tstar + 1 := fun u => by
    obtain ⟨h1, h2⟩ := D.T_win u
    have hT : 0 < ((D.mem u).A.T : ℝ) := lt_of_lt_of_le (hTspos u) h1
    refine ⟨Real.log_le_log (hTspos u) h1, ?_⟩
    have h3 := Real.log_le_log hT h2
    have h4 : 0 < 1 + 1 / ((D.R.f : ℝ) * D.R.k) := by positivity
    rw [Real.log_mul h4.ne' (hTspos u).ne'] at h3
    have h5 : Real.log (1 + 1 / ((D.R.f : ℝ) * D.R.k)) ≤ 1 := by
      have h6 := Real.log_le_sub_one_of_pos h4
      have h7 : 1 / ((D.R.f : ℝ) * D.R.k) ≤ 1 := by
        rw [div_le_one hfk0]; exact hfk
      linarith
    linarith
  intro u
  obtain ⟨hw1, hw2⟩ := D.T_win u
  obtain ⟨-, hup, hlow⟩ := h5c Δ _ hB (D.mem u).A.GamP (D.mem u).A.one_lt_gammaP.le u
    (by rw [hexp]; exact hw1)
    (by rw [hexp]; calc _ ≤ _ := hw2
          _ = _ := by rw [hTs]; ring)
  refine ⟨?_, ?_, ?_⟩
  · unfold StandardLattice.lowB at hlow
    rw [Fin.sum_univ_two] at hlow
    have hIcc : SizeData₂.lifts D = Finset.Ico (0 + 1) (D.R.m + 1) := by
      unfold SizeData₂.lifts
      ext j
      simp
    have hg0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
    have hg1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
    rw [hIcc, ← Finset.sum_Ico_add' (fun j => (1 / (D.R.f : ℝ)) *
      ∑ τ : D.what₂.Tau, Real.log (wj D j τ * D.host.v / Real.pi)) 0 D.R.m 1, ← Finset.range_eq_Ico]
    unfold Lnk.lgG
    rw [Real.log_mul hg0 hg1]
    have hk0 : (0 : ℝ) < D.R.k := by linarith
    have hA : L.sc.L + (D.R.m : ℝ) ^ 2 * L.sc.L / D.R.k ≤ L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k := by
      have : (D.R.m : ℝ) ^ 2 * L.sc.L / D.R.k ≤ (D.R.m : ℝ) ^ 2 * L.La / D.R.k :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLa (by positivity)) hk0.le
      linarith
    have hA0 : 0 ≤ L.sc.L + (D.R.m : ℝ) ^ 2 * L.sc.L / D.R.k := by positivity
    have hA1 : L.La ≤ L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k := by
      have : 0 ≤ (D.R.m : ℝ) ^ 2 * L.La / D.R.k :=
        div_nonneg (mul_nonneg (by positivity) (by linarith)) hk0.le
      linarith
    have h1 : C * (L.sc.L + (D.R.m : ℝ) ^ 2 * L.sc.L / D.R.k) ≤
        max C 0 * (L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k) :=
      (mul_le_mul_of_nonneg_right hCm hA0).trans (mul_le_mul_of_nonneg_left hA hC0)
    have h2 : 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ 2 := by
      have := hΓ u
      rw [mul_div_assoc]
      linarith
    have h3 : (max C 0 + 2) * (L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k) =
        max C 0 * (L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k) +
          2 * (L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k) := by ring
    rw [h3]
    linarith
  · have hmL : 0 ≤ (D.R.m : ℝ) * L.sc.L := by positivity
    calc Real.log ((D.mem u).A.T : ℝ) ≤ C * D.R.m * L.sc.L := hup
      _ = C * ((D.R.m : ℝ) * L.sc.L) := by ring
      _ ≤ (max C 0 + 2) * ((D.R.m : ℝ) * L.sc.L) := mul_le_mul_of_nonneg_right (by linarith) hmL
      _ = (max C 0 + 2) * D.R.m * L.sc.L := by ring
  · intro u'
    have hvv := (h5v Δ _ hB).2 u u'
    have hG : (D.mem u).A.GamP = (D.mem u').A.GamP := (D.GamP_eq u).trans (D.GamP_eq u').symm
    obtain ⟨a1, a2⟩ := hwin u
    obtain ⟨b1, b2⟩ := hwin u'
    rw [hlogTs] at a1 a2 b1 b2
    rw [hG] at a1 a2
    obtain ⟨c1, c2⟩ := abs_le.mp hvv
    have h1 : C * Real.log D.R.k ≤ max C 0 * Real.log D.R.k :=
      mul_le_mul_of_nonneg_right hCm (by linarith)
    have h3 : (max C 0 + 2) * Real.log D.R.k = max C 0 * Real.log D.R.k + 2 * Real.log D.R.k := by ring
    rw [h3, abs_le]
    constructor <;> linarith

theorem countF_of {eps : ℝ} (Fm : FamP eps) (C0 : ℝ) (h : StandardLattice.PartFiveFamilyBounds Fm)
    (hB : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
      ∃ Δ : ℝ, StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc C0 Δ (fun j ρ => wj (Fm.D x i) (j + 1) ρ))
    (hΓ : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      Real.log ((Fm.D x i).mem u).A.GamP / (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.k) ≤ 1) :
    Lnk.CountF Fm := by
  obtain ⟨C, x0, h⟩ := h C0
  obtain ⟨x1', hB⟩ := hB
  obtain ⟨x2, hΓ⟩ := hΓ
  refine ⟨max C 0 + 2, max (max x0 x1') (max x2 (Fm.x1 + 1)), by positivity, fun x hx i => ?_⟩
  have hxa : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x1' ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxd : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  obtain ⟨Δ, hDB⟩ := hB x hxb hxd i
  obtain ⟨-, h5c, h5v⟩ := h x hxa hxd i
  exact count_at_of _ _ C0 C Δ h5c h5v hDB (StandardLattice.factDuStar_fam Fm x hxd i)
    (StandardLattice.factDstar_fam Fm x hxd i) (hΓ x hxc hxd i)

theorem logGam_le {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x)
    (u : (Fm.D x i).what₂.Word) :
    Real.log ((Fm.D x i).mem u).A.GamP / (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.k) ≤ 1 := by
  obtain ⟨-, -, -, ⟨-, hG, -⟩, -⟩ := Fm.sizes x hx i
  have hk3 : (3 : ℝ) ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 3 ≤ (Fm.D x i).R.k)
  have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have : 1 ≤ (Fm.D x i).R.f := by
      unfold Ranks.f Ranks.n
      have := (Fm.D x i).R.toFrame.ord_pos
      omega
    exact_mod_cast this
  rw [div_le_one (by nlinarith), (Fm.L x i).Gam_eq u]
  nlinarith

theorem Xpp_eq (s : Scale) (n : ℕ) (hn : 0 < n) : s.X'' n = s.x * n * s.X' := by
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hb : 0 < s.b := Real.exp_pos _
  have hX : 0 < s.X' := Real.exp_pos _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Scale.X'' Scale.w'' Scale.b' Scale.a
  field_simp

theorem mL_le_Xpp (R : Ranks) (s : Scale) : (R.m : ℝ) * s.L ≤ 2 * s.X'' R.n := by
  have hx1 := s.one_lt_alt
  have hn : 0 < R.n := by unfold Ranks.n; positivity
  have hn' : (1 : ℝ) ≤ R.n := by exact_mod_cast hn
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hL : s.L ≤ s.x := by
    have : s.x ^ s.eps ≤ s.x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [s.eps_lt])
    rwa [Real.rpow_one] at this
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg (by linarith) _
  have hm : (R.m : ℝ) ≤ 2 * R.n := by
    have h2 : R.m ≤ 2 * R.n := by unfold Ranks.n; exact R.m_le_f
    exact_mod_cast h2
  rw [Xpp_eq s R.n hn]
  have h3 : (R.m : ℝ) * s.L ≤ 2 * R.n * s.x := mul_le_mul hm hL hL0 (by linarith)
  have h4 : s.x * R.n ≤ s.x * R.n * s.X' := le_mul_of_one_le_right (by nlinarith) hX
  linarith

theorem muTu_of_countF {eps : ℝ} (Fm : FamP eps) (h : Lnk.CountF Fm) : J.MuTu Fm := by
  obtain ⟨C, x0, hC, h⟩ := h
  refine ⟨2 * C, x0, fun x hx i u => ?_⟩
  have h1 := (h x hx i u).2.1
  have h2 := mL_le_Xpp (Fm.D x i).R (Fm.L x i).sc
  calc _ ≤ C * (Fm.D x i).R.m * (Fm.L x i).sc.L := h1
    _ = C * (((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L) := by ring
    _ ≤ C * (2 * (Fm.L x i).sc.X'' (Fm.D x i).R.n) := mul_le_mul_of_nonneg_left h2 hC
    _ = 2 * C * (Fm.L x i).sc.X'' (Fm.D x i).R.n := by ring

theorem exists_le_rpow (θ : ℝ) (hθ : 0 < θ) (C : ℝ) : ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x, x0 ≤ x → C ≤ x ^ θ := by
  refine ⟨(max C 1) ^ (1 / θ), Real.one_le_rpow (le_max_right _ _) (by positivity), fun x hx => ?_⟩
  have h0 : 0 ≤ (max C 1) ^ (1 / θ) := Real.rpow_nonneg (le_trans zero_le_one (le_max_right _ _)) _
  have h1 := Real.rpow_le_rpow h0 hx hθ.le
  rw [← Real.rpow_mul (le_trans zero_le_one (le_max_right _ _)), one_div, inv_mul_cancel₀ hθ.ne',
    Real.rpow_one] at h1
  exact le_trans (le_max_left _ _) h1

theorem sizeTu_of_countF {eps : ℝ} (heps : 0 < eps) (Fm : FamP eps) (h : Lnk.CountF Fm) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, SizeTu (Fm.L x i) := by
  obtain ⟨C, x0, -, h⟩ := h
  obtain ⟨x1', -, h1⟩ := exists_le_rpow (eps / 100) (by positivity) C
  refine ⟨max x0 x1', fun x hx hxx i u => ?_⟩
  have h2 := (h x (le_trans (le_max_left _ _) hx) i u).2.1
  have h3 := h1 x (le_trans (le_max_right _ _) hx)
  have hL0 : 0 ≤ (Fm.L x i).sc.L :=
    Real.rpow_nonneg (le_trans zero_le_one (Fm.L x i).sc.one_lt_alt.le) _
  have hm0 : 0 ≤ ((Fm.D x i).R.m : ℝ) := Nat.cast_nonneg _
  unfold szTh
  rw [Fm.L_x x i hxx, Fm.L_eps x i]
  calc _ ≤ C * (Fm.D x i).R.m * (Fm.L x i).sc.L := h2
    _ ≤ x ^ (eps / 100) * (Fm.D x i).R.m * (Fm.L x i).sc.L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hm0) hL0

theorem m_large {eps : ℝ} (Fm : FamP eps) (K : ℝ) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, K ≤ ((Fm.D x i).R.m : ℝ) := by
  obtain ⟨x0, hx0, h⟩ := exists_le_rpow (1 / 4) (by norm_num) K
  refine ⟨x0, fun x hx hx1 i => ?_⟩
  obtain ⟨-, ⟨hM, -⟩, -⟩ := Fm.sizes x hx1 i
  have hs := (Fm.L x i).sc
  have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have he0 := (Fm.L x i).sc.eps_pos
  have he1 := (Fm.L x i).sc.eps_lt
  have hx1' : 1 ≤ x := le_trans hx0 hx
  have hxpos : 0 < x := by linarith
  unfold szTh Scale.delta1 at hM
  rw [hxx] at hM
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hxpos.le (by linarith), ← Real.rpow_mul hxpos.le,
    ← Real.rpow_add hxpos] at hM
  refine le_trans (h x hx) (le_trans (Real.rpow_le_rpow_of_exponent_le hx1' ?_) hM)
  linarith

theorem lowB_ge (D : D7) (sc : Scale) (C0 C Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ)
    (hB : StandardLattice.DataB D sc C0 Δ w) :
    16 * (D.R.m : ℝ) * sc.L - max C 0 * (sc.L + 1) ≤ StandardLattice.lowB D sc C w := by
  obtain ⟨hv, -, -, hmk, -, hg, hΔ, -, -, -, -, -, hw, hwb, hb0, -⟩ := hB
  have hx := sc.one_lt_alt
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hbpos : 0 < sc.b := Real.exp_pos _
  have hb : ∀ ρ j, j < D.R.m → 4 ≤ StandardLattice.bN D ρ j := by
    intro ρ j
    induction j with
    | zero =>
      intro _
      have h1 := (hb0 ρ).1
      rw [le_div_iff₀ (by linarith)] at h1
      have h4 : (4 : ℝ) ≤ (D.R.k : ℝ) * (4 * Δ) := by nlinarith
      have h5 : (4 : ℝ) * 1 ≤ (D.R.k : ℝ) * (4 * Δ) * sc.x :=
        mul_le_mul h4 hx.le zero_le_one (by linarith)
      linarith
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := (hw ρ j (by omega)).2.1
      have h3 := hwb ρ j hj
      linarith
  have ht1 : 0 ≤ ∑ j ∈ Finset.range D.R.m,
      (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro ρ _
    apply Real.log_nonneg
    rw [le_div_iff₀ Real.pi_pos]
    have h1 := (hw ρ j (Finset.mem_range.mp hj)).2.1
    have h2 := hb ρ j (Finset.mem_range.mp hj)
    exact mul_le_mul (by linarith) hv Real.pi_pos.le (by linarith)
  have hgi : ∀ i, 8 * sc.L ≤ Real.log (D.host.g i) := by
    intro i
    have h1 := (hg i).1
    have hkb : sc.b ≤ (D.R.k : ℝ) * sc.b := by nlinarith
    have h2 : Real.log (((D.R.k : ℝ) * sc.b) ^ 8) ≤ Real.log (D.host.g i) :=
      Real.log_le_log (pow_pos (mul_pos (by linarith) hbpos) 8) h1
    rw [Real.log_pow] at h2
    have h3 : sc.L ≤ Real.log ((D.R.k : ℝ) * sc.b) := by
      have := Real.log_le_log hbpos hkb
      rwa [show sc.b = Real.exp sc.L from rfl, Real.log_exp] at this
    push_cast at h2
    linarith
  have hLpos : 0 < sc.L := Real.rpow_pos_of_pos (by linarith) _
  have hm0 : 0 ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have ht3 : C * (sc.L + (D.R.m : ℝ) ^ 2 * sc.L / D.R.k) ≤ max C 0 * (sc.L + 1) := by
    have h1 : (D.R.m : ℝ) ^ 2 * sc.L / D.R.k ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hmk
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 2 * sc.L / D.R.k := by positivity
    exact (mul_le_mul_of_nonneg_right (le_max_left C 0) (by linarith)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (le_max_right C 0))
  unfold StandardLattice.lowB
  rw [Fin.sum_univ_two]
  have h6 := mul_le_mul_of_nonneg_left (add_le_add (hgi 0) (hgi 1)) hm0
  linarith

theorem tuGe_of (D : D7) (L : SizeData₂ D) (C0 C Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ)
    (h5c : StandardLattice.TorusPairsWithVariant D L.sc C0 C) (hB : StandardLattice.DataB D L.sc C0 Δ w)
    (hDu : StandardLattice.FactDuStar D) (hDs : StandardLattice.FactDstar D)
    (hΓ : ∀ u, Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ 1)
    (hm : max C 0 * (L.sc.L + 1) + 2 ≤ 31 / 2 * D.R.m * L.sc.L) : L.TuGe := by
  intro u
  have hXpos : 0 < (D.mem u).A.Xu :=
    Real.rpow_pos_of_pos (div_pos (D.mem u).A.Dstar_pos (by exact_mod_cast (D.mem u).A.duStar_pos)) _
  have hexp : Real.exp (StandardLattice.logXuD D u) = (D.mem u).A.Xu := by
    rw [← jnt_logXu D hDu hDs u, Real.exp_log hXpos]
  have hTs : (D.mem u).A.Tstar =
      (D.mem u).A.Xu * (D.mem u).A.GamP ^ (-(2 : ℝ) / ((D.R.f : ℝ) * D.R.k)) := rfl
  obtain ⟨hw1, hw2⟩ := D.T_win u
  obtain ⟨-, -, hlow⟩ := h5c Δ w hB (D.mem u).A.GamP (D.mem u).A.one_lt_gammaP.le u
    (by rw [hexp]; exact hw1)
    (by rw [hexp]; calc _ ≤ _ := hw2
          _ = _ := by rw [hTs]; ring)
  have h1 := lowB_ge D L.sc C0 C Δ w hB
  have h2 : 2 * Real.log (D.mem u).A.GamP / ((D.R.f : ℝ) * D.R.k) ≤ 2 := by
    have := hΓ u
    rw [mul_div_assoc]
    linarith
  have hT : 0 < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  have h3 : L.sc.L * ((D.R.m : ℝ) / 2) ≤ Real.log ((D.mem u).A.T : ℝ) := by linarith
  rw [show L.sc.b = Real.exp L.sc.L from rfl, ← Real.exp_mul]
  exact (Real.le_log_iff_exp_le hT).mp h3

theorem tuSize_of {eps : ℝ} (Fm : FamP eps) (C0 C x0 : ℝ)
    (h : ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, StandardLattice.Conclusion5₂ (Fm.D x i) (Fm.L x i).sc C0 C)
    (hB : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
      ∃ (Δ : ℝ) (w : ℕ → (Fm.D x i).what₂.Tau → ℝ), StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc C0 Δ w)
    (hC : C ≤ Fm.CTu) : TuSize Fm := by
  obtain ⟨x1', hB⟩ := hB
  obtain ⟨x2, hm⟩ := m_large Fm ((4 * max C 0 + 4) / 31)
  refine ⟨max (max x0 x1') (max x2 (Fm.x1 + 1)), fun x hx i => ?_⟩
  have hxa : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x1' ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxd : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  obtain ⟨Δ, w, hDB⟩ := hB x hxb hxd i
  obtain ⟨-, h5c, -⟩ := h x hxa hxd i
  have hL1 : 1 ≤ (Fm.L x i).sc.L :=
    Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hm0 : 0 ≤ ((Fm.D x i).R.m : ℝ) := Nat.cast_nonneg _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hmm := hm x hxc hxd i
  rw [div_le_iff₀ (by norm_num)] at hmm
  have hΓ := fun u => logGam_le Fm x hxd i u
  refine ⟨tuGe_of _ _ C0 C Δ w h5c hDB (StandardLattice.factDuStar_fam Fm x hxd i) (StandardLattice.factDstar_fam Fm x hxd i) hΓ ?_,
    fun u => ?_⟩
  · have h1 : max C 0 * ((Fm.L x i).sc.L + 1) ≤ max C 0 * (2 * (Fm.L x i).sc.L) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    nlinarith
  · have hXpos : 0 < ((Fm.D x i).mem u).A.Xu :=
      Real.rpow_pos_of_pos (div_pos ((Fm.D x i).mem u).A.Dstar_pos
        (by exact_mod_cast ((Fm.D x i).mem u).A.duStar_pos)) _
    have hexp : Real.exp (StandardLattice.logXuD (Fm.D x i) u) = ((Fm.D x i).mem u).A.Xu := by
      rw [← jnt_logXu _ (StandardLattice.factDuStar_fam Fm x hxd i) (StandardLattice.factDstar_fam Fm x hxd i) u,
        Real.exp_log hXpos]
    have hTs : ((Fm.D x i).mem u).A.Tstar = ((Fm.D x i).mem u).A.Xu *
        ((Fm.D x i).mem u).A.GamP ^ (-(2 : ℝ) / (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.k)) := rfl
    obtain ⟨hw1, hw2⟩ := (Fm.D x i).T_win u
    obtain ⟨-, hup, -⟩ := h5c Δ w hDB ((Fm.D x i).mem u).A.GamP ((Fm.D x i).mem u).A.one_lt_gammaP.le u
      (by rw [hexp]; exact hw1)
      (by rw [hexp]; calc _ ≤ _ := hw2
            _ = _ := by rw [hTs]; ring)
    have hmL : 0 ≤ ((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L := by positivity
    calc _ ≤ C * (Fm.D x i).R.m * (Fm.L x i).sc.L := hup
      _ = C * (((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L) := by ring
      _ ≤ Fm.CTu * (((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L) := mul_le_mul_of_nonneg_right hC hmL
      _ = Fm.CTu * (Fm.D x i).R.m * (Fm.L x i).sc.L := by ring

theorem _root_.Formalism.MainNotions.ShortIntervalPrimes.log_height_family_of_gap_data {eps : ℝ} (Fm : FamP eps) (C0 : ℝ) (h : StandardLattice.PartFiveFamilyBounds Fm)
    (hB : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
      ∃ (Δ : ℝ) (w : ℕ → (Fm.D x i).what₂.Tau → ℝ), StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc C0 Δ w) :
    ShortIntervalPrimes.proportionalityInputFamily Fm :=
  ShortIntervalPrimes.log_height_family_of_data Fm C0 h hB (m_large Fm)

namespace JGD

section

open Matrix NumberField

section Sig

variable {n : Type} [Fintype n] [DecidableEq n]

theorem sig_val (J : Matrix n n ℂ) (p q : ℕ) (h : Formalism.UG.HasSignature J p q) (z : n → ℂ) (hz : z ≠ 0) :
    ∃ y : Fin p ⊕ Fin q → ℂ, y ≠ 0 ∧ star z ⬝ᵥ (J *ᵥ z) =
      (∑ i, star (y (Sum.inl i)) * y (Sum.inl i)) - ∑ j, star (y (Sum.inr j)) * y (Sum.inr j) := by
  obtain ⟨e, P, hP⟩ := h
  rw [Formalism.UG.P.cT_conj_eq] at hP
  have hQ : (P.val.submatrix e id)ᴴ * J * (P.val.submatrix e id) =
      Formalism.UG.Jpq p q := by
    have hJ : J = (J.reindex e e).submatrix e e := by
      ext i j; simp
    rw [hJ, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
    simpa using hP
  let y : Fin p ⊕ Fin q → ℂ := (P⁻¹).val *ᵥ (z ∘ e.symm)
  have hPy : P.val *ᵥ y = z ∘ e.symm := by
    show P.val *ᵥ ((P⁻¹).val *ᵥ (z ∘ e.symm)) = _
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hQy : (P.val.submatrix e id) *ᵥ y = z := by
    funext i
    have := congrFun hPy (e i)
    simpa [mulVec, dotProduct] using this
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hz
    rw [← hQy, hy, mulVec_zero]
  · have := Formalism.UG.P.sig_quad J _ hQ y
    rwa [hQy] at this

theorem normSq_sum_pos {m : Type} [Fintype m] (y : m → ℂ) (hy : y ≠ 0) :
    0 < (∑ i, star (y i) * y i).re := by
  have hc : ∀ w : ℂ, star w * w = ((Complex.normSq w : ℝ) : ℂ) := by
    intro w; rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [hc]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

theorem sig_pos (J : Matrix n n ℂ) (p : ℕ) (h : Formalism.UG.HasSignature J p 0) (z : n → ℂ) (hz : z ≠ 0) :
    0 < (star z ⬝ᵥ (J *ᵥ z)).re := by
  obtain ⟨y, hy, hv⟩ := sig_val J p 0 h z hz
  rw [hv]
  have h0 : (fun i : Fin p => y (Sum.inl i)) ≠ 0 := by
    intro h0
    apply hy
    funext k
    rcases k with a | b
    · exact congrFun h0 a
    · exact b.elim0
  have := normSq_sum_pos (fun i : Fin p => y (Sum.inl i)) h0
  simpa using this

theorem sig_neg (J : Matrix n n ℂ) (q : ℕ) (h : Formalism.UG.HasSignature J 0 q) (z : n → ℂ) (hz : z ≠ 0) :
    (star z ⬝ᵥ (J *ᵥ z)).re < 0 := by
  obtain ⟨y, hy, hv⟩ := sig_val J 0 q h z hz
  rw [hv]
  have h0 : (fun j : Fin q => y (Sum.inr j)) ≠ 0 := by
    intro h0
    apply hy
    funext k
    rcases k with a | b
    · exact a.elim0
    · exact congrFun h0 b
  have := normSq_sum_pos (fun j : Fin q => y (Sum.inr j)) h0
  simpa using this

theorem sig_reindex {n' : Type} [Fintype n'] [DecidableEq n'] (J : Matrix n n ℂ) (f : n ≃ n')
    {p q p' q' : ℕ} (hp : p = p') (hq : q = q') (h : Formalism.UG.HasSignature J p q) :
    Formalism.UG.HasSignature (J.reindex f f) p' q' := by
  subst hp hq
  obtain ⟨e, P, hP⟩ := h
  refine ⟨f.symm.trans e, P, ?_⟩
  have : (J.reindex f f).reindex (f.symm.trans e) (f.symm.trans e) = J.reindex e e := by
    ext i j; simp
  rw [this]
  exact hP

end Sig

theorem exists_ext {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (ι' : F →+* ℝ) : ∃ τ : E →+* ℂ, ∀ a, τ (algebraMap F E a) = ((ι' a : ℝ) : ℂ) := by
  letI : Algebra F ℂ := (Complex.ofRealHom.comp ι').toAlgebra
  exact ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, fun a => (IsAlgClosed.lift : E →ₐ[F] ℂ).commutes a⟩

theorem isDef_of_sig {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] {k : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E) (hJ : UnusedSlot33.IsHerm (σ : E →+* E) J)
    (hfix : ∀ a : E, σ a = a → a ∈ (algebraMap F E).range) (hinv : ∀ a, σ (σ a) = a)
    (hconj : ∀ (τ : E →+* ℂ) a, τ (σ a) = starRingEnd ℂ (τ a))
    (hsig : ∀ τ : E →+* ℂ, Formalism.UG.HasSignature (J.map τ) k 0 ∨ Formalism.UG.HasSignature (J.map τ) 0 k) :
    UnusedSlot33.IsDef σ J := by
  intro ι'
  obtain ⟨τ, hτ⟩ := exists_ext (E := E) ι'
  have hJ' : ∀ i j, σ (J j i) = J i j := fun i j => by
    have := congrFun (congrFun hJ i) j
    simpa [UnusedSlot33.cT] using this
  have hfixed : ∀ x : Fin k → E, σ (UnusedSlot33.hform (σ : E →+* E) J x x) = UnusedSlot33.hform (σ : E →+* E) J x x := by
    intro x
    unfold UnusedSlot33.hform
    simp only [map_sum, map_mul, AlgHom.coe_toRingHom, hinv, hJ']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hval : ∀ x : Fin k → E, τ (UnusedSlot33.hform (σ : E →+* E) J x x) =
      star (fun i => τ (x i)) ⬝ᵥ ((J.map τ) *ᵥ (fun i => τ (x i))) := by
    intro x
    unfold UnusedSlot33.hform
    simp only [map_sum, map_mul, AlgHom.coe_toRingHom, hconj, dotProduct, mulVec, Pi.star_apply,
      Matrix.map_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_assoc]
  have hne : ∀ x : Fin k → E, x ≠ 0 → (fun i => τ (x i)) ≠ 0 := by
    intro x hx h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa using this
  rcases hsig τ with h | h
  · left
    intro x hx
    obtain ⟨a, ha⟩ := hfix _ (hfixed x)
    refine ⟨a, ha, ?_⟩
    have h1 := sig_pos _ k h _ (hne x hx)
    rw [← hval x, ← ha, hτ a, Complex.ofReal_re] at h1
    exact h1
  · right
    intro x hx
    obtain ⟨a, ha⟩ := hfix _ (hfixed x)
    refine ⟨a, ha, ?_⟩
    have h1 := sig_neg _ k h _ (hne x hx)
    rw [← hval x, ← ha, hτ a, Complex.ofReal_re] at h1
    exact h1

theorem _root_.Formalism.MainNotions.GlobalTheoryTheory.gram0Def (D : D7) : Gram0Def D := by
  letI := D.host.cmStar
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  refine isDef_of_sig D.sp.cm.sig D.sp.gram0 D.sp.baseGram_isHermitian ?_ ?_ ?_ ?_
  · intro a ha
    exact (D.sp.cm.fixed a).mp ha
  · intro a
    exact star_star a
  · intro τ a
    exact D.sp.cm.cmUnram.2.1 τ a
  · intro τ
    have hs := D.sp.X_sig 0 τ
    have hmap : D.sp.gram0.map τ =
        ((D.sp.X 0).gram.map τ).reindex (finCongr D.sp.rank0) (finCongr D.sp.rank0) := by
      ext i j; rfl
    rw [hmap]
    rcases D.sp.X_def 0 (Nat.zero_le _) τ with h | h
    · left
      rw [h] at hs
      exact sig_reindex _ _ D.sp.rank0 rfl hs
    · right
      rw [h] at hs
      exact sig_reindex _ _ rfl D.sp.rank0 hs

end

end JGD

theorem _root_.Formalism.MainNotions.StandardLattice.column_lemma_family_holds {eps : ℝ} (Fm : FamP eps) (C₄ C₅ : ℝ) (h : UnusedSlot33.ConclusionOnFamily Fm C₄ C₅) :
    StandardLattice.FamilyLevelConditionAdmitted Fm :=
  StandardLattice.column_lemma_family_of_definite Fm C₄ C₅ h (fun _ _ => gram0Def _)

namespace JDB

section

open Formalism.FrobeniusOrbits

theorem db_rk (D : D7) : (3 : ℝ) ≤ D.R.k ∧ (2 : ℝ) ≤ D.R.m ∧ (D.R.k : ℝ) ≤ D.R.t ∧ (D.R.k : ℝ) ≤ D.R.r ∧
    (1 : ℝ) ≤ D.R.n ∧ (D.R.f : ℝ) = 2 * D.R.n ∧ (D.R.m : ℝ) ≤ D.R.k := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  have h3 := D.R.rank_add_five_le
  have hn : 1 ≤ D.R.n := D.R.toFrame.ord_pos
  refine ⟨by exact_mod_cast (by omega : 3 ≤ D.R.k), by exact_mod_cast h2,
    by exact_mod_cast (by omega : D.R.k ≤ D.R.t), ?_, by exact_mod_cast hn, ?_,
    by exact_mod_cast (by omega : D.R.m ≤ D.R.k)⟩
  · have : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  · unfold Ranks.f; push_cast; ring

theorem db_rdE (D : D7) :
    (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) * Real.sqrt (D.host.d : ℝ) ≤ D.host.rdE :=
  D.host.der.rd_ge

theorem db_pi_le_v (D : D7) : Real.pi ≤ D.host.v := by
  have he : (2 : ℝ) ≤ (D.R.e : ℝ) := by exact_mod_cast D.host.two_le_e
  have h1 : (2 : ℝ) ^ (-(D.R.e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)
  have h2 : (2 : ℝ) ^ (2 : ℝ) ≤ (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have h2' : (4 : ℝ) ≤ (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) := by
    have : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    linarith
  have hd : (7 : ℝ) ≤ D.host.d := by
    have := D.host.hyp.2.2.2.1
    exact_mod_cast (by omega : 7 ≤ D.host.d)
  have h3 : (2 : ℝ) ≤ Real.sqrt (D.host.d : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have h4 : 8 ≤ D.host.rdE := by
    have := db_rdE D
    nlinarith
  unfold Host.v
  linarith [Real.pi_le_four]

theorem db_basic {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    1 ≤ L.sc.L ∧ L.sc.L ≤ L.sc.x ∧ 2 ≤ L.sc.b ∧ (D.R.k : ℝ) ≤ L.sc.b ∧ D.host.v ≤ L.sc.b ∧
      1 ≤ Real.log L.sc.x := by
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨-, -, -, -, -, hCond, hQD, -⟩ := S
  have hx1 := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hLx : L.sc.L ≤ L.sc.x := by
    have : L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [L.sc.eps_lt])
    rwa [Real.rpow_one] at this
  have hb2 : 2 ≤ L.sc.b := by
    have h1 : L.sc.L + 1 ≤ Real.exp L.sc.L := Real.add_one_le_exp _
    have h2 : L.sc.b = Real.exp L.sc.L := rfl
    linarith
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hqd : 1 ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hQS : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hc1 : 1 ≤ szCond L := by unfold szCond; nlinarith
  have ht1 : (1 : ℝ) ≤ D.R.t := by linarith
  have hc36 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
  have ht150 : (D.R.t : ℝ) ≤ (D.R.t : ℝ) ^ 150 := le_self_pow₀ ht1 (by norm_num)
  have hc36' : 1 ≤ szCond L ^ 36 := one_le_pow₀ hc1
  have ht150' : 1 ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
  have hCond' : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b := hCond
  have hkb : (D.R.k : ℝ) ≤ L.sc.b := by nlinarith
  have hvb : D.host.v ≤ L.sc.b := by
    obtain ⟨-, -, -, -, -, -, -, hrd⟩ := hQD
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have h1 : D.host.v ≤ szCond L := by
      unfold Host.v szCond
      nlinarith
    nlinarith
  have hlx : 1 ≤ Real.log L.sc.x := by
    have h1 : Real.exp 1 ≤ L.sc.x := by linarith [Real.exp_one_lt_d9]
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  exact ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩

theorem sizes_clause_seventeen {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    Real.pi ≤ D.host.v ∧ Real.log D.host.v ≤ L.sc.L ∧
    (D.R.f : ℝ) ≤ L.sc.x ^ (max 5 (P.CYL + 1)) ∧ (D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k ∧
    (D.R.k : ℝ) ≤ L.sc.x ^ (max 5 (P.CYL + 1)) ∧
    (∀ i : Fin 2, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧
      Real.log (D.host.g i : ℝ) ≤ max 5 (P.CYL + 1) * L.sc.L) ∧
    1 ≤ ((D.s.Del : ℚ) : ℝ) := by
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  obtain ⟨hN, -, hK, hKR, -, -, -, -, -, -, -, -, -, -, -, -, hDel, -, -, -, hG, -⟩ := S
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hth : szTh L = L.sc.eps / 100 := rfl
  have h5 : L.sc.x ^ (5 : ℝ) ≤ L.sc.x ^ (max 5 (P.CYL + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  have hpiv := db_pi_le_v D
  refine ⟨hpiv, ?_, ?_, hKR.2.2.2.2.1, ?_, ?_, ?_⟩
  · have h1 := Real.log_le_log (by linarith [Real.pi_pos]) hvb
    rwa [show L.sc.b = Real.exp L.sc.L from rfl, Real.log_exp] at h1
  · have h1 : (D.R.n : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) := hN.2
    have h2 : L.sc.x ^ (1 : ℝ) * L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) ≤ L.sc.x ^ (5 : ℝ) := by
      rw [← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hth]; linarith)
    rw [Real.rpow_one] at h2
    have h3 : 0 < L.sc.x ^ (2 + 8 * L.sc.eps + szTh L) := Real.rpow_pos_of_pos hx0 _
    rw [hf]
    nlinarith
  · have h1 : (D.R.k : ℝ) ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps + szTh L) := hK.2
    have h2 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps + szTh L) ≤ L.sc.x ^ (5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hth]; linarith)
    linarith
  · intro i
    refine ⟨(hG i i).1, ?_⟩
    obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
    have hY0 : 0 < Y := lt_of_lt_of_le (pow_pos (mul_pos (by linarith) (by linarith)) 8) hY1
    have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le hY0 (hY4 i).1
    have h1 := Real.log_le_log hg0 (hY4 i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at h1
    have h2 := Real.log_two_lt_d9
    have h3 : (P.CYL + 1) * L.sc.L ≤ max 5 (P.CYL + 1) * L.sc.L :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    nlinarith
  · have h1 : (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ ((D.s.Del : ℚ) : ℝ) := hDel.1
    have h2 : (1 : ℝ) ≤ D.R.N D.R.m := by
      have : 1 ≤ D.R.N D.R.m := by
        unfold Ranks.N
        have := D.R.m_add_three_le_k
        omega
      exact_mod_cast this
    have h3 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
    nlinarith

theorem db_vN {D : D7} (ρ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k - 1) :
    StandardLattice.vN D ρ i = (((D.hc ρ).v ⟨i, h⟩ : ℚ) : ℝ) := by
  unfold StandardLattice.vN; rw [dif_pos h]

theorem db_uN {D : D7} (u : D.what₂.Word) (ρ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k) :
    StandardLattice.uN D u ρ i = (((D.hcW u ρ).u ⟨i, h⟩ : ℚ) : ℝ) := by
  unfold StandardLattice.uN; rw [dif_pos h]

theorem db_bN {D : D7} (ρ : D.what₂.Tau) (j : ℕ) (h : j < D.R.m) :
    StandardLattice.bN D ρ j = (((D.hc ρ).b ⟨j, h⟩ : ℚ) : ℝ) := by
  unfold StandardLattice.bN; rw [dif_pos h]

theorem db_wj {D : D7} (ρ : D.what₂.Tau) (j : ℕ) (h : j < D.R.m) :
    wj D (j + 1) ρ = (((D.hc ρ).e ⟨j, h⟩ : ℚ) : ℝ) := by
  have h' : j + 1 - 1 < D.R.m := by simpa using h
  unfold wj
  rw [dif_pos h']
  have : (⟨j + 1 - 1, h'⟩ : Fin D.R.m) = ⟨j, h⟩ := Fin.ext (by simp)
  rw [this]

theorem db_cloud {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) :
    (∀ ρ i, i < D.R.k - 1 → 0 ≤ StandardLattice.vN D ρ i ∧ StandardLattice.vN D ρ i ≤ (D.R.k : ℝ) * (4 * ((D.s.Del : ℚ) : ℝ))) ∧
    (∀ ρ i, i + 1 < D.R.k - 1 → StandardLattice.vN D ρ i - StandardLattice.vN D ρ (i + 1) = 4 * ((D.s.Del : ℚ) : ℝ)) ∧
    (∀ u ρ l, 1 ≤ l → l ≤ D.R.k - 2 →
      StandardLattice.uN D u ρ l = StandardLattice.vN D ρ (l - 1) - 1 / 2 ∨
        StandardLattice.uN D u ρ l = StandardLattice.vN D ρ (l - 1) - 1 / 2 - ((D.s.Del : ℚ) : ℝ)) ∧
    (∀ u ρ, ¬ StandardLattice.IsTop D ρ →
      (D.R.k : ℝ) * (4 * ((D.s.Del : ℚ) : ℝ)) ≤ StandardLattice.uN D u ρ 0 - StandardLattice.vN D ρ 0 ∧
      StandardLattice.uN D u ρ 0 - StandardLattice.vN D ρ 0 ≤ 2 * D.R.k * (4 * ((D.s.Del : ℚ) : ℝ)) ∧
      StandardLattice.uN D u ρ (D.R.k - 1) = StandardLattice.vN D ρ (D.R.k - 2) - 1 / 2) := by
  have hk := D.R.m_add_three_le_k
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ i h
    rw [db_vN ρ i h]
    have h1 := L.cloud_v ρ ⟨i, h⟩
    rw [L.Sc_eq] at h1
    exact h1
  · intro ρ i h
    rw [db_vN ρ i (by omega), db_vN ρ (i + 1) h]
    have h1 := D.s.cloud_gap D.u₀ ρ i h
    rw [D.hcW_v D.u₀ ρ] at h1
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at h2
    exact h2
  · intro u ρ l h1 h2
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have h3 := D.s.u_letter u ρ l' (by omega)
    rw [D.hcW_v u ρ] at h3
    rw [db_uN u ρ (l' + 1) (by omega), Nat.add_sub_cancel, db_vN ρ l' (by omega), h3]
    split_ifs
    · right; push_cast; ring
    · left; push_cast; ring
  · intro u ρ hnt
    have hk0 : 0 < D.R.k := by omega
    have h0 : 0 < D.R.k - 1 := by omega
    have h1 := L.cloud_gap ρ h0 hnt
    have h2 := P.cloud_place_bound ρ h0 hnt
    rw [L.Sc_eq] at h1 h2
    push_cast at h1 h2
    refine ⟨?_, ?_, ?_⟩
    · rw [db_uN u ρ 0 hk0, db_vN ρ 0 h0, D.hcW_first u ρ hk0]
      exact h1.1
    · rw [db_uN u ρ 0 hk0, db_vN ρ 0 h0, D.hcW_first u ρ hk0]
      linarith
    · rw [db_uN u ρ (D.R.k - 1) (by omega), db_vN ρ (D.R.k - 2) (by omega), D.hcW_last u ρ hk0,
        P.uk_extreme ρ (by omega) hnt]
      push_cast
      ring

theorem db_b'pos {D : D7} (L : SizeData₂ D) : 0 < L.sc.b' := by
  have hx0 : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  unfold Scale.b' Scale.a
  exact div_pos (mul_pos hx0 (Real.exp_pos _)) (Real.exp_pos _)

theorem db_w {D : D7} (L : SizeData₂ D) : 0 < L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' := by
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  have hx1 := L.sc.one_lt_alt
  have hb'0 := db_b'pos L
  have hxn : 1 ≤ L.sc.x * D.R.n := by nlinarith
  constructor
  · unfold Scale.w''
    exact div_pos hb'0 (by linarith)
  · unfold Scale.w''
    exact div_le_self hb'0.le hxn

theorem db_b'le {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) : L.sc.b' ≤ L.sc.b := by
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hE1 : 1 ≤ L.sc.x ^ L.sc.eps := hL1
  have hb0 : 0 < L.sc.b := by linarith
  have hη := L.etaSz_pos
  have hSc := L.Sc_pos
  have hb'0 := db_b'pos L
  obtain ⟨-, -, -, hKR, -, -, -, -, -, -, -, -, -, hEta, -⟩ := S
  have h9 : (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * szlA L ≤ L.de2 * D.R.m * L.sc.b :=
    hEta.2.2.2.2.2.2.2.2
  have hd0 := L.thickDensity_pos
  have hd1 := L.thickDensity_le_one
  have hmd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos (by linarith) hd0
  have e1 : (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * szlA L =
      (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * ((D.R.k : ℝ) * L.sc.x ^ L.sc.eps) /
        ((D.R.m : ℝ) * L.de2) := by
    unfold szlA; ring
  rw [e1, div_le_iff₀ hmd] at h9
  have s1 : L.sc.b' * D.R.k ≤ (L.sc.b' + L.Sc) * D.R.k :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have p1 : 0 ≤ (L.sc.b' + L.Sc) * D.R.k := by positivity
  have s2 : (L.sc.b' + L.Sc) * D.R.k ≤ (D.R.r : ℝ) * ((L.sc.b' + L.Sc) * D.R.k) :=
    le_mul_of_one_le_left p1 (by linarith)
  have p2 : 0 ≤ (D.R.r : ℝ) * ((L.sc.b' + L.Sc) * D.R.k) := mul_nonneg (by linarith) p1
  have s3 : (D.R.r : ℝ) * ((L.sc.b' + L.Sc) * D.R.k) ≤
      (D.R.r : ℝ) * ((L.sc.b' + L.Sc) * D.R.k) * Real.log L.sc.x := le_mul_of_one_le_right p2 hlx
  have p3 : 0 ≤ (D.R.r : ℝ) * ((L.sc.b' + L.Sc) * D.R.k) * Real.log L.sc.x :=
    mul_nonneg p2 (by linarith)
  have s4 : (D.R.r : ℝ) * ((L.sc.b' + L.Sc) * D.R.k) * Real.log L.sc.x ≤
      (D.R.r : ℝ) * ((L.sc.b' + L.Sc) * D.R.k) * Real.log L.sc.x * L.sc.x ^ L.sc.eps :=
    le_mul_of_one_le_right p3 hE1
  have e2 : (D.R.r : ℝ) * ((L.sc.b' + L.Sc) * D.R.k) * Real.log L.sc.x * L.sc.x ^ L.sc.eps =
      (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * ((D.R.k : ℝ) * L.sc.x ^ L.sc.eps) := by ring
  have hm2L : (D.R.m : ℝ) ^ 2 * L.sc.L ≤ D.R.k := hKR.2.2.2.2.1
  have hm2k : (D.R.m : ℝ) ^ 2 ≤ D.R.k := by nlinarith [sq_nonneg (D.R.m : ℝ)]
  have hd2 : L.de2 ^ 2 ≤ 1 := by nlinarith
  have u1 : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) = L.de2 ^ 2 * ((D.R.m : ℝ) ^ 2 * L.sc.b) := by
    ring
  have u2 : L.de2 ^ 2 * ((D.R.m : ℝ) ^ 2 * L.sc.b) ≤ 1 * ((D.R.m : ℝ) ^ 2 * L.sc.b) :=
    mul_le_mul_of_nonneg_right hd2 (by positivity)
  have u3 : (D.R.m : ℝ) ^ 2 * L.sc.b ≤ D.R.k * L.sc.b := mul_le_mul_of_nonneg_right hm2k hb0.le
  have fin : L.sc.b' * D.R.k ≤ L.sc.b * D.R.k := by linarith
  exact le_of_mul_le_mul_right fin (by linarith)

theorem eta_size_le_b_div_27 {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) : L.etaSz ≤ L.sc.b / 27 := by
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hE1 : 1 ≤ L.sc.x ^ L.sc.eps := hL1
  have hb0 : 0 < L.sc.b := by linarith
  have hη := L.etaSz_pos
  have hSc := L.Sc_pos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hEta, -⟩ := S
  have h2 : L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := hEta.2.1
  have ht1 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hk27 : (27 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := by
    have : (3 : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hk3 3
    linarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by rw [hf]; linarith
  have h27 : (27 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by
    have a1 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := by nlinarith
    nlinarith
  exact h2.trans (div_le_div_of_nonneg_left hb0.le (by norm_num) h27)

theorem db_xeta {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    (L.sc.x + 1) * L.etaSz ≤ L.sc.w'' D.R.n := by
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hE1 : 1 ≤ L.sc.x ^ L.sc.eps := hL1
  have hb0 : 0 < L.sc.b := by linarith
  have hη := L.etaSz_pos
  have hSc := L.Sc_pos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hEta, -⟩ := S
  have h4 : (D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x := hEta.2.2.2.1
  rw [le_div_iff₀ hx0] at h4
  have ht3 : (3 : ℝ) ≤ D.R.t := by linarith
  have a1 : (L.sc.x + 1) * L.etaSz ≤ 3 * L.etaSz * L.sc.x := by nlinarith
  have a2 : 3 * L.etaSz * L.sc.x ≤ (D.R.t : ℝ) * L.etaSz * L.sc.x := by
    have : 3 * L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := mul_le_mul_of_nonneg_right ht3 hη.le
    exact mul_le_mul_of_nonneg_right this hx0.le
  linarith

theorem db_bT {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    ∀ t, (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hE1 : 1 ≤ L.sc.x ^ L.sc.eps := hL1
  have hb0 : 0 < L.sc.b := by linarith
  have hη := L.etaSz_pos
  have hSc := L.Sc_pos
  have hb'0 := db_b'pos L
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -⟩ := S
  intro t
  have h1 : (L.bT t : ℝ) ≤ L.sc.b' + szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k := hBot t
  have h2 : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k +
      L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤ L.sc.x ^ (-2 : ℝ) := hRho
  have hLaG : 0 < L.LaG := lt_of_lt_of_le (by linarith) hLa.1
  have h3 : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (by linarith)) hLaG.le) (by linarith)
  have h4 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have e1 : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
      4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
  have e2 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k * L.sc.b' := by ring
  rw [e1] at h2
  rw [e2] at h1
  have h5 : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 hb'0.le
  linarith

theorem db_xS {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    L.sc.x * L.Sc ≤ 3 / 4 * L.sc.w'' D.R.n := by
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hE1 : 1 ≤ L.sc.x ^ L.sc.eps := hL1
  have hb0 : 0 < L.sc.b := by linarith
  have hη := L.etaSz_pos
  have hSc := L.Sc_pos
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, hDel, -⟩ := S
  have h4 : (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n := hDel.2.2.2.1
  have hk1 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) ≤ (D.R.k : ℝ) := hK.1
  have hth : szTh L = L.sc.eps / 100 := rfl
  have h2 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hth]; linarith [L.sc.eps_pos])
  rw [Real.rpow_two] at h2
  have h3 : 3 * L.sc.x ≤ D.R.k := by nlinarith
  nlinarith

theorem db_xk {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) : 3 * L.sc.x ≤ D.R.k := by
  obtain ⟨-, -, hK, -⟩ := S
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hk1 : L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) ≤ (D.R.k : ℝ) := hK.1
  have hth : szTh L = L.sc.eps / 100 := rfl
  have h2 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by rw [hth]; linarith [L.sc.eps_pos])
  rw [Real.rpow_two] at h2
  nlinarith

theorem db_win {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) (ρ : D.what₂.Tau) (j : ℕ)
    (hj : j < D.R.m) : L.sc.w'' D.R.n ≤ wj D (j + 1) ρ ∧ wj D (j + 1) ρ ≤ 2 * L.sc.b := by
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  have hb'0 := db_b'pos L
  obtain ⟨hw0, hwb⟩ := db_w L
  have hb'b := db_b'le L S hx
  have hη27 := eta_size_le_b_div_27 L S hx
  have hη := L.etaSz_pos
  have hx0 : 0 < L.sc.x := by linarith
  have h1 : 1 ≤ j + 1 := by omega
  have h2 : j + 1 ≤ D.R.m := by omega
  by_cases htop : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · have htop' := htop
    unfold Host.topPlaces at htop'
    obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp htop'
    obtain ⟨a1, a2⟩ := L.win_top (j + 1) h1 h2 ρ ⟨t, ht⟩ heq.symm
    have hbT := db_bT L S hx ⟨t, ht⟩
    have hbTge := L.bT_ge ⟨t, ht⟩
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 3 := div_le_div_of_nonneg_left hb'0.le (by norm_num) hx
    have hbx0 : 0 ≤ L.sc.b' / L.sc.x := by positivity
    constructor <;> linarith
  · by_cases hth : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨a1, a2⟩ := L.win_thick (j + 1) h1 h2 ρ hth
      constructor <;> linarith
    · obtain ⟨a1, a2⟩ := L.win_thin (j + 1) h1 h2 ρ ⟨(D.eTau ρ).2, htop, hth⟩
      constructor <;> linarith

theorem db_top {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    ∀ u ρ, StandardLattice.IsTop D ρ → StandardLattice.uN D u ρ 0 ≤ 2 * L.sc.a ∧ -L.sc.a ≤ StandardLattice.uN D u ρ (D.R.k - 1) := by
  intro u ρ htop
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  have hkN := D.R.m_add_three_le_k
  have hk0 : 0 < D.R.k := by omega
  have hx1 : 1 ≤ L.sc.x := by linarith
  have htop' : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces := htop
  unfold Host.topPlaces at htop'
  obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp htop'
  obtain ⟨a1, a2⟩ := L.top_u ρ ⟨t, ht⟩ hk0 heq.symm
  rw [db_uN u ρ 0 hk0, db_uN u ρ (D.R.k - 1) (by omega), D.hcW_first u ρ hk0, D.hcW_last u ρ hk0, a1, a2]
  obtain ⟨w1, w2⟩ := L.aT_win ⟨t, ht⟩
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have ha3 : 3 * L.sc.b ≤ L.sc.a := by rw [ha]; nlinarith
  have ha0 : 0 < L.sc.a := by linarith
  have hxa : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow hx1 (by unfold Scale.A; norm_num)
  have hden : 3 ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by nlinarith
  have h3 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 3 :=
    div_le_div_of_nonneg_left ha0.le (by norm_num) hden
  have hbT := db_bT L S hx ⟨t, ht⟩
  have hb'b := db_b'le L S hx
  constructor <;> linarith

theorem db_be {D : D7} (L : SizeData₂ D) (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    StandardLattice.bN D ρ j < wj D (j + 1) ρ ∧ wj D (j + 1) ρ - StandardLattice.bN D ρ j ≤ L.etaSz := by
  rw [db_wj ρ j hj, db_bN ρ j hj]
  have h1 := (D.hc ρ).gap_be ⟨j, hj⟩
  have h2 : (((((D.R.t : ℚ) + 3) / 2 : ℚ)) : ℝ) ≤
      (((D.hc ρ).e ⟨j, hj⟩ - (D.hc ρ).b ⟨j, hj⟩ : ℚ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h3 := L.be_close ρ ⟨j, hj⟩ ⟨j, hj⟩
  push_cast at h3
  have h4 := (abs_le.mp h3).1
  constructor <;> linarith

theorem sizes_clause_thirteen {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    ∀ ρ j, j < D.R.m → 0 < wj D (j + 1) ρ ∧ StandardLattice.bN D ρ j < wj D (j + 1) ρ ∧
      |wj D (j + 1) ρ - StandardLattice.bN D ρ j| ≤ StandardLattice.bN D ρ j / L.sc.x := by
  intro ρ j hj
  obtain ⟨hw0, hwb⟩ := db_w L
  obtain ⟨a1, a2⟩ := db_win L S hx ρ j hj
  obtain ⟨b1, b2⟩ := db_be L ρ j hj
  have hxη := db_xeta L S hx
  have hη := L.etaSz_pos
  have hx0 : 0 < L.sc.x := by linarith
  refine ⟨by linarith, b1, ?_⟩
  rw [abs_of_pos (by linarith), le_div_iff₀ hx0]
  have h1 : (wj D (j + 1) ρ - StandardLattice.bN D ρ j) * L.sc.x ≤ L.etaSz * L.sc.x :=
    mul_le_mul_of_nonneg_right b2 hx0.le
  nlinarith

theorem sizes_clause_fourteen {D : D7} : ∀ (ρ : D.what₂.Tau) j, j + 1 < D.R.m → wj D (j + 1) ρ < StandardLattice.bN D ρ (j + 1) := by
  intro ρ j hj
  have hj0 : j < D.R.m := by omega
  rw [db_wj ρ j hj0, db_bN ρ (j + 1) hj]
  have h1 := (D.hc ρ).gap_eb ⟨j, hj0⟩ hj
  have h2 : (((((D.R.t : ℚ) + 3) / 2 : ℚ)) : ℝ) ≤
      (((D.hc ρ).b ⟨j + 1, hj⟩ - (D.hc ρ).e ⟨j, hj0⟩ : ℚ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  linarith

theorem sizes_clause_fifteen {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    ∀ ρ, (D.R.k : ℝ) * (4 * ((D.s.Del : ℚ) : ℝ)) ≤ StandardLattice.bN D ρ 0 / L.sc.x ∧
      wj D (D.R.m - 1 + 1) ρ ≤ 2 * L.sc.b := by
  intro ρ
  have hm := D.R.two_le_m
  have hx0 : 0 < L.sc.x := by linarith
  refine ⟨?_, (db_win L S hx ρ (D.R.m - 1) (by omega)).2⟩
  rw [← L.Sc_eq, le_div_iff₀ hx0]
  obtain ⟨a1, a2⟩ := db_win L S hx ρ 0 (by omega)
  obtain ⟨b1, b2⟩ := db_be L ρ 0 (by omega)
  have hxη := db_xeta L S hx
  have hxS := db_xS L S hx
  have hη := L.etaSz_pos
  nlinarith

theorem sizes_clause_sixteen {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (S : SizesAt L) (hx : 3 ≤ L.sc.x) (C0 : ℝ)
    (hC0 : 1 ≤ C0) : StandardLattice.GapA D L.sc C0 := by
  intro ρ j hj
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hNodes, -⟩ := S
  have hx1 : 1 ≤ L.sc.x := by linarith
  rw [db_bN ρ (j + 1) hj, db_bN ρ j (by omega)]
  have h1 := (P.nodes_gap ρ j hj).1
  push_cast at h1
  have h2 : L.sc.x ^ szTh L * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ L.etaSz / D.R.m :=
    hNodes.2.2.1
  have h1' : L.etaSz / D.R.m ≤
      (((D.hc ρ).b ⟨j + 1, hj⟩ : ℚ) : ℝ) - (((D.hc ρ).b ⟨j, by omega⟩ : ℚ) : ℝ) := h1
  have hth : 1 ≤ L.sc.x ^ szTh L :=
    Real.one_le_rpow hx1 (by unfold szTh; linarith [L.sc.eps_pos])
  have hL0 : 0 ≤ L.sc.L := by linarith
  have hA : 0 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by positivity
  have key : (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L / C0 ≤
      L.sc.x ^ szTh L * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by
    calc (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L / C0
        ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := div_le_self hA hC0
      _ ≤ L.sc.x ^ szTh L * ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L) :=
          le_mul_of_one_le_left hA hth
      _ = L.sc.x ^ szTh L * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L := by ring
  linarith

theorem dataB_of {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L) (S : SizesAt L) (hx : 3 ≤ L.sc.x) :
    StandardLattice.DataB D L.sc (max 5 (P.CYL + 1)) ((D.s.Del : ℚ) : ℝ) (fun j ρ => wj D (j + 1) ρ) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := sizes_clause_seventeen L P S hx
  obtain ⟨c8, c9, c10, c12⟩ := db_cloud L P
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, db_top L S hx, c12, sizes_clause_thirteen L S hx, sizes_clause_fourteen,
    sizes_clause_fifteen L S hx, sizes_clause_sixteen L P S hx _ (le_trans (by norm_num) (le_max_left _ _))⟩

theorem dataB_fam {eps : ℝ} (Fm : FamP eps) (x : ℝ) (h3 : 3 ≤ x) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc (max 5 (Fm.CYL + 1)) (((Fm.D x i).s.Del : ℚ) : ℝ)
      (fun j ρ => wj (Fm.D x i) (j + 1) ρ) := by
  rw [← Fm.params_CYL x hx i]
  exact dataB_of (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i) (by rw [Fm.L_x x i hx]; exact h3)

theorem gBig_of {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 3 ≤ L.sc.x) : StandardLattice.GBig D := by
  obtain ⟨hk3, hm2, hkt, hkr, hn1, hf, hmk⟩ := db_rk D
  obtain ⟨hL1, hLx, hb2, hkb, hvb, hlx⟩ := db_basic L S hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := S
  refine ⟨0, ?_⟩
  have hg : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g 0 : ℝ) := (hG 0 0).1
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by
    have : D.R.f ≤ D.R.k := by unfold Ranks.f Ranks.n; exact D.R.f_le_k
    exact_mod_cast this
  have hkb1 : 1 ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have h28 : ((D.R.k : ℝ) * L.sc.b) ^ 2 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := pow_le_pow_right₀ hkb1 (by norm_num)
  have h2k : 2 * (D.R.k : ℝ) ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
  have h4 : (2 * (D.R.k : ℝ)) ^ 2 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 2 := pow_le_pow_left₀ (by linarith) h2k 2
  have h1 : (2 : ℝ) * D.R.f * D.R.k + 1 < (D.host.g 0 : ℝ) := by nlinarith
  have h2 : 2 * D.R.f * D.R.k + 1 < D.host.g 0 := by exact_mod_cast h1
  omega

theorem m_ge {D : D7} (L : SizeData₂ D) (S : SizesAt L) : L.sc.x ^ ((1 : ℝ) / 4) ≤ D.R.m := by
  obtain ⟨-, hM, -⟩ := S
  have h1 : L.sc.x ^ (-szTh L) * Real.sqrt (L.sc.x * L.sc.delta1) ≤ (D.R.m : ℝ) := hM.1
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have e0 : L.sc.x * L.sc.delta1 = L.sc.x ^ (1 + -(L.sc.eps / 8)) := by
    unfold Scale.delta1
    rw [Real.rpow_add hx0, Real.rpow_one]
  have e : L.sc.x ^ (-szTh L) * Real.sqrt (L.sc.x * L.sc.delta1) =
      L.sc.x ^ (-szTh L + (1 + -(L.sc.eps / 8)) * (1 / 2)) := by
    rw [e0, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
  rw [e] at h1
  have h2 : L.sc.x ^ ((1 : ℝ) / 4) ≤ L.sc.x ^ (-szTh L + (1 + -(L.sc.eps / 8)) * (1 / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by unfold szTh; linarith [L.sc.eps_lt, L.sc.eps_pos])
  linarith

theorem m_large_fam {eps : ℝ} (Fm : FamP eps) (K : ℝ) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, K ≤ ((Fm.D x i).R.m : ℝ) := by
  refine ⟨(max K 0) ^ 4, fun x hx hx1 i => ?_⟩
  have h1 := m_ge (Fm.L x i) (Fm.sizes x hx1 i)
  rw [Fm.L_x x i hx1] at h1
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have h3 : ((max K 0) ^ 4) ^ ((1 : ℝ) / 4) ≤ x ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have h4 : ((max K 0) ^ 4) ^ ((1 : ℝ) / 4) = max K 0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0]
    norm_num
  linarith [le_max_left K 0]

theorem gBig_fam {eps : ℝ} (Fm : FamP eps) (x : ℝ) (h3 : 3 ≤ x) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    StandardLattice.GBig (Fm.D x i) :=
  gBig_of (Fm.L x i) (Fm.sizes x hx i) (by rw [Fm.L_x x i hx]; exact h3)

end

end JDB

theorem countF_fam {eps : ℝ} (Fm : FamP eps) (h : StandardLattice.PartFiveFamilyBounds Fm) : Lnk.CountF Fm :=
  countF_of Fm (max 5 (Fm.CYL + 1)) h
    ⟨3, fun x h3 hx i => ⟨_, JDB.dataB_fam Fm x h3 hx i⟩⟩
    ⟨0, fun x _ hx i u => logGam_le Fm x hx i u⟩

theorem muTu_fam {eps : ℝ} (Fm : FamP eps) (h : StandardLattice.PartFiveFamilyBounds Fm) : J.MuTu Fm :=
  muTu_of_countF Fm (countF_fam Fm h)

theorem _root_.Formalism.MainNotions.ShortIntervalPrimes.log_height_family_of_part_five {eps : ℝ} (Fm : FamP eps) (h : StandardLattice.PartFiveFamilyBounds Fm) : ShortIntervalPrimes.proportionalityInputFamily Fm :=
  ShortIntervalPrimes.log_height_family_of_gap_data Fm (max 5 (Fm.CYL + 1)) h ⟨3, fun x h3 hx i => ⟨_, _, JDB.dataB_fam Fm x h3 hx i⟩⟩

theorem tuSize_fam {eps : ℝ} (Fm : FamP eps) (C x0 : ℝ)
    (h : ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
      StandardLattice.Conclusion5₂ (Fm.D x i) (Fm.L x i).sc (max 5 (Fm.CYL + 1)) C)
    (hC : C ≤ Fm.CTu) : TuSize Fm :=
  tuSize_of Fm (max 5 (Fm.CYL + 1)) C x0 h ⟨3, fun x h3 hx i => ⟨_, _, JDB.dataB_fam Fm x h3 hx i⟩⟩ hC

theorem _root_.Formalism.MainNotions.flipTwoThree.stabiliser_family_of_column_lemma {eps : ℝ} (Fm : FamP eps) (C₄ C₅ : ℝ) (h : UnusedSlot33.ConclusionOnFamily Fm C₄ C₅)
    (hP : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev) :
    flipTwoThree.admF3 Fm :=
  flipTwoThree.stabiliser_family_of_definite Fm C₄ C₅ h (fun _ _ => gram0Def _) hP ⟨3, fun x h3 hx i => JDB.gBig_fam Fm x h3 hx i⟩

def IncidenceTransportConditions (D : D7) (u : D.what₂.Word) : Prop :=
  product_first_zeroth_parts.UpDownIncidenceInverse D u ∧ product_first_zeroth_parts.admT D u ∧ product_first_zeroth_parts.admB D u ∧ ∃ P : product_first_zeroth_parts.Pend D u, product_first_zeroth_parts.ArchimedeanSignatureMatching P

theorem _root_.Formalism.MainNotions.product_first_zeroth_parts.AdmF_of {eps : ℝ} (Fm : FamP eps) (C22 C₄ C₅ : ℝ) (h22 : TaylorLogMetric.ConclusionOnFamily Fm C22)
    (h59 : UnusedSlot33.ConclusionOnFamily Fm C₄ C₅)
    (hP : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev)
    (hT : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u) :
    product_first_zeroth_parts.AdmF Fm := by
  obtain ⟨x0, hT⟩ := hT
  refine ⟨max x0 (max 3 (Fm.x1 + 1)), fun x hx i u => ?_⟩
  have hxa : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  obtain ⟨h0, hTr, hBs, P, h4⟩ := hT x hxa i u
  obtain ⟨G, g1, g2, g3⟩ := product_first_zeroth_parts.theta_conditions_of_theta_theorem (Fm.D x i) C22 (h22 x i)
  exact ⟨P, G, h0, product_first_zeroth_parts.stabiliser_admissible_of_level _ (Fm.ex x hx1 i).lev u (h59 x hx1 i).2.2.2.2.2.2.2.1 (gram0Def _)
    (hP x hx1 i u) (JDB.gBig_fam Fm x hx3 hx1 i), g1, g2, g3, h4, hTr, hBs⟩

theorem levels_pro_g_along_family {eps : ℝ} (Fm : FamP eps) (C3 : ℝ) (h : StandardLattice.FamilyPartFour Fm C3) (x : ℝ) (hx : Fm.x1 < x)
    (i : Fm.Ix x) : StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev :=
  (h x hx i).2.2.2.1

theorem _root_.Formalism.MainNotions.flipTwoThree.stabiliser_family_of_levels {eps : ℝ} (Fm : FamP eps) (C₄ C₅ C3 : ℝ) (h : UnusedSlot33.ConclusionOnFamily Fm C₄ C₅)
    (h24 : StandardLattice.FamilyPartFour Fm C3) : flipTwoThree.admF3 Fm :=
  flipTwoThree.stabiliser_family_of_column_lemma Fm C₄ C₅ h (levels_pro_g_along_family Fm C3 h24)

theorem _root_.Formalism.MainNotions.product_first_zeroth_parts.AdmF_of_pk {eps : ℝ} (Fm : FamP eps) (C22 C₄ C₅ C3 : ℝ) (h22 : TaylorLogMetric.ConclusionOnFamily Fm C22)
    (h59 : UnusedSlot33.ConclusionOnFamily Fm C₄ C₅) (h24 : StandardLattice.FamilyPartFour Fm C3)
    (hT : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u) :
    product_first_zeroth_parts.AdmF Fm :=
  product_first_zeroth_parts.AdmF_of Fm C22 C₄ C₅ h22 h59 (levels_pro_g_along_family Fm C3 h24) hT

theorem two_lt_level_prime (D : D7) (u : D.what₂.Word) (h : product_first_zeroth_parts.HidaSetting D u) : 2 < (D.mem u).A.T := by
  have h1 := h.1
  have hf : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := D.R.toFrame.ord_pos
    omega
  have hN : 1 ≤ D.R.N D.R.m := by
    unfold Ranks.N
    have := D.R.m_add_three_le_k
    omega
  have h2 : 1 ≤ D.R.f * D.R.N D.R.m := Nat.mul_pos hf hN
  have h3 : 2 * D.R.f * D.R.N D.R.m = 2 * (D.R.f * D.R.N D.R.m) := by ring
  omega

theorem jnt_duS_pos (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (h4f : StandardLattice.Conclusion4f D Lv)
    (hg : StandardLattice.GBig D) (hs : ∀ i, StandardLattice.SplitsF D (D.host.g i)) (hsT : StandardLattice.SplitsF D (D.mem u).A.T)
    (hM : StandardLattice.Mu0Tie D u) (hDu : StandardLattice.FactDuStar D) (hT : 2 < (D.mem u).A.T) : 0 < D.duS u := by
  have h := h4f hg hs u hsT hM
  have h1 : (0 : ℝ) < StandardLattice.duStarU D u := by
    rw [← hDu u]
    exact_mod_cast (D.mem u).A.duStar_pos
  have hT' : (1 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast (by omega : 1 < (D.mem u).A.T)
  have hk : D.R.k ≠ 0 := by
    have := D.R.m_add_three_le_k
    omega
  have h2 : (0 : ℝ) < ((D.mem u).A.T : ℝ) ^ D.R.k - 1 := by
    have := one_lt_pow₀ hT' hk
    linarith
  have h3 : (0 : ℝ) < ((D.duS u : ℕ) : ℝ) := by
    show (0 : ℝ) < ((haveI := (D.mem u).A.Mu0_fd; Module.finrank ℂ (D.mem u).A.Mu0 : ℕ) : ℝ)
    rw [h]
    positivity
  exact_mod_cast h3

theorem jnt_du_pos (D : D7) (u : D.what₂.Word) (h2 : product_first_zeroth_parts.Conclusion2 D u) (hS : 0 < D.duS u)
    (hT : 2 < (D.mem u).A.T) : 0 < (D.mem u).A.du := by
  have h := h2.1
  have hT' : (2 : ℚ) < ((D.mem u).A.T : ℚ) := by exact_mod_cast hT
  have h1 : (0 : ℚ) < 1 - 1 / (((D.mem u).A.T : ℚ) - 1) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have h3 : (0 : ℚ) < ((D.mem u).A.du : ℚ) := by
    rw [h]
    have : (0 : ℚ) < (D.duS u : ℚ) := by exact_mod_cast hS
    positivity
  exact_mod_cast h3

theorem jnt_rank_pos (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (hN : D.NuFull)
    (hSet : product_first_zeroth_parts.HidaSetting D u) (h2 : product_first_zeroth_parts.Conclusion2 D u) (h4f : StandardLattice.Conclusion4f D Lv)
    (hg : StandardLattice.GBig D) (hs : ∀ i, StandardLattice.SplitsF D (D.host.g i)) (hsT : StandardLattice.SplitsF D (D.mem u).A.T)
    (hM : StandardLattice.Mu0Tie D u) (hDu : StandardLattice.FactDuStar D) : 0 < (D.div.Nu u).rank := by
  have hT := two_lt_level_prime D u hSet
  have h1 : (D.div.Nu u).rank = (D.mem u).A.du := hN.rank u
  rw [h1]
  exact jnt_du_pos D u h2 (jnt_duS_pos D Lv u h4f hg hs hsT hM hDu hT) hT

def RankCondF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
    StandardLattice.GBig (Fm.D x i) ∧ (∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j)) ∧
    ∀ u, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).mem u).A.T ∧ StandardLattice.Mu0Tie (Fm.D x i) u

theorem muRank_of {eps : ℝ} (Fm : FamP eps) (crystallineComparison C3 : ℝ) (hN : NuFullF Fm)
    (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hS : SettingEventually Fm) (h24 : StandardLattice.FamilyPartFour Fm C3) (hR : RankCondF Fm) :
    J.MuRank Fm := by
  obtain ⟨a0, hN⟩ := hN
  obtain ⟨a1, h10⟩ := h10
  obtain ⟨a2, hS⟩ := hS
  obtain ⟨a3, hR⟩ := hR
  refine ⟨max (max a0 a1) (max (max a2 a3) (Fm.x1 + 1)), fun x hx i u => ?_⟩
  have b0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have b1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have b2 : a2 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b3 : a3 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b4 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  obtain ⟨hg, hs, hu⟩ := hR x b3 b4 i
  have hSet := hS x b2 b4 i u
  exact jnt_rank_pos (Fm.D x i) (Fm.ex x b4 i).lev u (hN x b0 i) hSet (h10 x b1 i u hSet).2.1
    (h24 x b4 i).2.2.2.2.2.2.2.1 hg hs (hu u).1 (hu u).2 (StandardLattice.factDuStar_fam Fm x b4 i)

theorem gBig_of_dataB (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ)
    (h : StandardLattice.DataB D sc C0 Δ w) : StandardLattice.GBig D := by
  obtain ⟨-, -, -, -, -, hg, -⟩ := h
  have h0 := (hg 0).1
  have hk3 : (3 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 3 ≤ D.R.k)
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by
    have := D.R.f_le_k
    unfold Ranks.f Ranks.n
    exact_mod_cast this
  have hb : (1 : ℝ) ≤ sc.b := by
    have hL : 0 ≤ sc.L := (Real.rpow_pos_of_pos (by linarith [sc.one_lt_alt]) _).le
    exact Real.one_le_exp hL
  have hkb : (D.R.k : ℝ) ≤ (D.R.k : ℝ) * sc.b := le_mul_of_one_le_right (by linarith) hb
  have h1 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * sc.b) ^ 8 := pow_le_pow_left₀ (by linarith) hkb 8
  have hy : (9 : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
  have hy3 : (729 : ℝ) ≤ ((D.R.k : ℝ) ^ 2) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) hy 3
    norm_num at this
    exact this
  have h2 : 729 * (D.R.k : ℝ) ^ 2 ≤ (D.R.k : ℝ) ^ 8 := by
    have : (D.R.k : ℝ) ^ 8 = ((D.R.k : ℝ) ^ 2) ^ 3 * (D.R.k : ℝ) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hy3 (by positivity)
  have h3 : 2 * (D.R.f : ℝ) * D.R.k + 1 < (D.host.g 0 : ℝ) := by
    have : 2 * (D.R.f : ℝ) * D.R.k ≤ 2 * (D.R.k : ℝ) ^ 2 := by nlinarith
    nlinarith
  have h4 : 2 * D.R.f * D.R.k + 1 < D.host.g 0 := by exact_mod_cast h3
  exact ⟨0, by omega⟩

theorem jnt_duS_pos_of_proviso {D : D7} (L : SizeData₂ D) (C0 : ℝ) (hC0 : 0 < C0) (h : ChProviso_at L C0)
    (u : D.what₂.Word) : 0 < D.duS u := by
  rcases Nat.eq_zero_or_pos (D.duS u) with h0 | h0
  · have h1 := (h u).1
    rw [h0] at h1
    have h2 : (0 : ℝ) < C0⁻¹ := inv_pos.mpr hC0
    simp at h1
    linarith
  · exact h0

theorem muRank_of_chosen {eps : ℝ} (Fm : FamP eps) {C0 CH : ℝ} (crystallineComparison : ℝ) (hC0 : 0 < C0)
    (hCh : ChosenE Fm C0 CH) (hN : NuFullF Fm) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hS : SettingEventually Fm) :
    J.MuRank Fm := by
  obtain ⟨C5, c6, Cb, -, -, -, hCh⟩ := hCh
  obtain ⟨a3, hP⟩ := hCh.2.2.2.2.2.1
  obtain ⟨a0, hN⟩ := hN
  obtain ⟨a1, h10⟩ := h10
  obtain ⟨a2, hS⟩ := hS
  refine ⟨max (max a0 a1) (max (max a2 a3) (Fm.x1 + 1)), fun x hx i u => ?_⟩
  have b0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have b1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have b2 : a2 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b3 : a3 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b4 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  have hSet := hS x b2 b4 i u
  have h1 : ((Fm.D x i).div.Nu u).rank = ((Fm.D x i).mem u).A.du := (hN x b0 i).rank u
  rw [h1]
  exact jnt_du_pos _ u (h10 x b1 i u hSet).2.1 (jnt_duS_pos_of_proviso (Fm.L x i) C0 hC0 (hP x b3 i) u)
    (two_lt_level_prime _ u hSet)

def DGamMink (D : D7) (C : ℝ) : Prop :=
  ∃ Mk : ℕ, 0 < Mk ∧ (∀ u, (D.mem u).C.DGam ∣ Mk) ∧
    Real.log (Mk : ℝ) ≤ C * D.R.f * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)

theorem factDGam_of (D : D7) (C : ℝ) (hb : DGamMink D C) : FactDGam D C := by
  obtain ⟨Mk, hMk, h1, h3⟩ := hb
  intro u
  have hle : ((D.mem u).C.DGam : ℝ) ≤ (Mk : ℝ) := by exact_mod_cast Nat.le_of_dvd hMk (h1 u)
  exact (Real.log_le_log (by exact_mod_cast (D.mem u).C.DGam_pos) hle).trans h3

theorem muDGam_of {eps : ℝ} (Fm : FamP eps)
    (h : ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, DGamMink (Fm.D x i) C) : J.MuDGam Fm := by
  obtain ⟨C, x0, h⟩ := h
  exact J.muDGam_of_fact Fm ⟨C, x0, fun x hx i => factDGam_of _ C (h x hx i)⟩

namespace JSL

section

open Formalism.FrobeniusOrbits

def SlopesM_at {D : D7} (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ u, -(C * D.host.TT.card * L.sc.a * L.La * (1 + (D.R.m : ℝ) / D.R.k)) ≤ ((D.fm u).lat 0).mu ∧
    ((D.fm u).lat 0).muMax ≤ C * D.host.TT.card * L.sc.a * L.La

def NumsL (D : D7) (L : SizeData₂ D) (Cn cL : ℝ) : Prop :=
  ∀ u, flipTwoThree.Nums D (flipTwoThree.Tu D u) (D.host.g 0) (D.host.g 1) Cn L.sc.x L.sc.b (cL * L.sc.L) L.sc.b' L.Sc
    L.etaSz

def WtsL (D : D7) (L : SizeData₂ D) (Cn : ℝ) : Prop :=
  ∀ u, flipTwoThree.Wts D u Cn L.sc.x L.sc.b L.sc.b' L.Sc L.etaSz

theorem jnt_le_help {c Cp Q R : ℝ} (hc : c ≤ Cp) (hCp : 0 ≤ Cp) (hQ0 : 0 ≤ Q) (hQR : Q ≤ R) :
    c * Q ≤ Cp * R :=
  (mul_le_mul_of_nonneg_right hc hQ0).trans (mul_le_mul_of_nonneg_left hQR hCp)

theorem jnt_card_tops (D : D7) : (flipTwoThree.tops D).card = D.host.TT.card := by
  classical
  symm
  refine Finset.card_bij (fun (t : D.R.A) _ =>
    D.eTau.symm ⟨D.R.tau1 t, by rw [Formalism.HC.Frame.mem_Psi_iff]; rfl⟩) ?_ ?_ ?_
  · intro t ht
    simp only [flipTwoThree.tops, topsOf, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.apply_symm_apply]
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  · intro s _ t _ hst
    have := congrArg Subtype.val (D.eTau.symm.injective hst)
    exact D.R.toFrame.iota_bijective.1 (congrArg Prod.snd this)
  · intro τ hτ
    simp only [flipTwoThree.tops, topsOf, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hτ
    refine ⟨t, ht, ?_⟩
    apply D.eTau.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext he

theorem jnt_isTop_of_mem (D : D7) {τ : D.what₂.Tau} (h : τ ∈ flipTwoThree.tops D) : flipTwoThree.IsTop D τ := by
  classical
  simp only [flipTwoThree.tops, topsOf, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

theorem jnt_slope_low (nT a La k f m lT lk B Sc Lx C5 Cp cL Cc S1 : ℝ)
    (hnT : 0 ≤ nT) (ha : 0 ≤ a) (hLa0 : 0 ≤ La) (hk0 : 0 < k) (hf0 : 0 ≤ f) (hm0 : 0 ≤ m) (hmk : m ≤ k)
    (hlT0 : 0 ≤ lT) (hlTLa : lT ≤ Cc * m * La) (hlk0 : 0 ≤ lk) (hlk : lk ≤ 5 * La)
    (hB0 : 0 ≤ B) (hSc0 : 0 ≤ Sc) (hScB : Sc ≤ B) (hLx0 : 0 ≤ Lx) (hLxLa : Lx ≤ La)
    (hC5 : C5 ≤ Cp) (hCp : 0 ≤ Cp) (hcL : 0 ≤ cL) (hCc : 0 ≤ Cc)
    (hfkB : f * k * B ≤ nT * a) (hfk2 : f * k ^ 2 ≤ nT * a) (hS1 : S1 ≤ nT * (2 * a / k * lT)) :
    -((2 * Cc + Cp * (12 + Cc + cL)) * nT * a * La * (1 + m / k)) ≤
      -S1 - C5 * nT * a * lk - C5 * f * k * B * lk - C5 * f * Sc * lT - C5 * f * k ^ 2 * (cL * Lx) := by
  have hP0 : 0 ≤ nT * a := mul_nonneg hnT ha
  have hW0 : 0 ≤ nT * a * La := mul_nonneg hP0 hLa0
  have hr0 : 0 ≤ m / k := div_nonneg hm0 hk0.le
  have hfmB : f * m * B ≤ nT * a :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmk hf0) hB0).trans hfkB
  have s1 : S1 ≤ nT * a * La * (2 * Cc) * (m / k) := by
    refine hS1.trans ?_
    calc nT * (2 * a / k * lT) ≤ nT * (2 * a / k * (Cc * m * La)) := by
          apply mul_le_mul_of_nonneg_left _ hnT
          exact mul_le_mul_of_nonneg_left hlTLa (by positivity)
      _ = nT * a * La * (2 * Cc) * (m / k) := by field_simp
  have t2 : C5 * nT * a * lk ≤ Cp * (nT * a * La * 5) := by
    calc C5 * nT * a * lk = C5 * (nT * a * lk) := by ring
      _ ≤ Cp * (nT * a * (5 * La)) :=
          jnt_le_help hC5 hCp (mul_nonneg hP0 hlk0) (mul_le_mul_of_nonneg_left hlk hP0)
      _ = _ := by ring
  have t3 : C5 * f * k * B * lk ≤ Cp * (nT * a * La * 5) := by
    calc C5 * f * k * B * lk = C5 * (f * k * B * lk) := by ring
      _ ≤ Cp * ((nT * a) * (5 * La)) :=
          jnt_le_help hC5 hCp (mul_nonneg (mul_nonneg (mul_nonneg hf0 hk0.le) hB0) hlk0)
            (mul_le_mul hfkB hlk hlk0 hP0)
      _ = _ := by ring
  have q4 : f * Sc * lT ≤ (nT * a) * (Cc * La) := by
    calc f * Sc * lT ≤ f * B * lT :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hScB hf0) hlT0
      _ ≤ f * B * (Cc * m * La) := mul_le_mul_of_nonneg_left hlTLa (mul_nonneg hf0 hB0)
      _ = (f * m * B) * (Cc * La) := by ring
      _ ≤ (nT * a) * (Cc * La) := mul_le_mul_of_nonneg_right hfmB (mul_nonneg hCc hLa0)
  have t4 : C5 * f * Sc * lT ≤ Cp * (nT * a * La * Cc) := by
    calc C5 * f * Sc * lT = C5 * (f * Sc * lT) := by ring
      _ ≤ Cp * ((nT * a) * (Cc * La)) :=
          jnt_le_help hC5 hCp (mul_nonneg (mul_nonneg hf0 hSc0) hlT0) q4
      _ = _ := by ring
  have t5 : C5 * f * k ^ 2 * (cL * Lx) ≤ Cp * (nT * a * La * cL) := by
    calc C5 * f * k ^ 2 * (cL * Lx) = C5 * (f * k ^ 2 * (cL * Lx)) := by ring
      _ ≤ Cp * ((nT * a) * (cL * La)) :=
          jnt_le_help hC5 hCp (mul_nonneg (mul_nonneg hf0 (by positivity)) (mul_nonneg hcL hLx0))
            (mul_le_mul hfk2 (mul_le_mul_of_nonneg_left hLxLa hcL) (mul_nonneg hcL hLx0) hP0)
      _ = _ := by ring
  have n1 := mul_nonneg hCc hW0
  have n2 := mul_nonneg hCp hW0
  have n3 : 0 ≤ Cp * (nT * a * La) * (m / k) * (12 + Cc + cL) :=
    mul_nonneg (mul_nonneg n2 hr0) (by linarith)
  have e : (2 * Cc + Cp * (12 + Cc + cL)) * nT * a * La * (1 + m / k) =
      nT * a * La * (2 * Cc) * (m / k) + Cp * (nT * a * La * 5) + Cp * (nT * a * La * 5) +
        Cp * (nT * a * La * Cc) + Cp * (nT * a * La * cL) +
        (2 * (Cc * (nT * a * La)) + 2 * (Cp * (nT * a * La)) +
          Cp * (nT * a * La) * (m / k) * (12 + Cc + cL)) := by ring
  rw [e]
  linarith

theorem jnt_slope_up (nT a La k f m lT lkv B Lx C6 Cp cL Cc : ℝ)
    (hnT : 0 ≤ nT) (ha : 0 ≤ a) (hLa0 : 0 ≤ La) (hk0 : 0 < k) (hf0 : 0 ≤ f) (hmk : m ≤ k)
    (hlT0 : 0 ≤ lT) (hlTLa : lT ≤ Cc * m * La) (hlkv0 : 0 ≤ lkv) (hlkv : lkv ≤ 6 * La)
    (hB0 : 0 ≤ B) (hLx0 : 0 ≤ Lx) (hLxLa : Lx ≤ La)
    (hC6 : C6 ≤ Cp) (hCp : 0 ≤ Cp) (hcL : 0 ≤ cL) (hCc : 0 ≤ Cc)
    (hfkB : f * k * B ≤ nT * a) (hfk2 : f * k ^ 2 ≤ nT * a) :
    C6 * nT * a * lkv + C6 * f * B * (k * lkv + lT) + C6 * f * k ^ 2 * (cL * Lx) ≤
      (2 * Cc + Cp * (12 + Cc + cL)) * nT * a * La := by
  have hP0 : 0 ≤ nT * a := mul_nonneg hnT ha
  have hW0 : 0 ≤ nT * a * La := mul_nonneg hP0 hLa0
  have hfmB : f * m * B ≤ nT * a :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmk hf0) hB0).trans hfkB
  have t1 : C6 * nT * a * lkv ≤ Cp * (nT * a * La * 6) := by
    calc C6 * nT * a * lkv = C6 * (nT * a * lkv) := by ring
      _ ≤ Cp * (nT * a * (6 * La)) :=
          jnt_le_help hC6 hCp (mul_nonneg hP0 hlkv0) (mul_le_mul_of_nonneg_left hlkv hP0)
      _ = _ := by ring
  have q2 : f * B * (k * lkv + lT) ≤ (nT * a) * (6 * La) + (nT * a) * (Cc * La) := by
    have e1 : f * B * (k * lkv) ≤ (nT * a) * (6 * La) := by
      calc f * B * (k * lkv) = (f * k * B) * lkv := by ring
        _ ≤ (nT * a) * (6 * La) := mul_le_mul hfkB hlkv hlkv0 hP0
    have e2 : f * B * lT ≤ (nT * a) * (Cc * La) := by
      calc f * B * lT ≤ f * B * (Cc * m * La) := mul_le_mul_of_nonneg_left hlTLa (mul_nonneg hf0 hB0)
        _ = (f * m * B) * (Cc * La) := by ring
        _ ≤ (nT * a) * (Cc * La) := mul_le_mul_of_nonneg_right hfmB (mul_nonneg hCc hLa0)
    calc f * B * (k * lkv + lT) = f * B * (k * lkv) + f * B * lT := by ring
      _ ≤ _ := add_le_add e1 e2
  have t2 : C6 * f * B * (k * lkv + lT) ≤ Cp * (nT * a * La * (6 + Cc)) := by
    calc C6 * f * B * (k * lkv + lT) = C6 * (f * B * (k * lkv + lT)) := by ring
      _ ≤ Cp * ((nT * a) * (6 * La) + (nT * a) * (Cc * La)) :=
          jnt_le_help hC6 hCp (mul_nonneg (mul_nonneg hf0 hB0)
            (add_nonneg (mul_nonneg hk0.le hlkv0) hlT0)) q2
      _ = _ := by ring
  have t3 : C6 * f * k ^ 2 * (cL * Lx) ≤ Cp * (nT * a * La * cL) := by
    calc C6 * f * k ^ 2 * (cL * Lx) = C6 * (f * k ^ 2 * (cL * Lx)) := by ring
      _ ≤ Cp * ((nT * a) * (cL * La)) :=
          jnt_le_help hC6 hCp (mul_nonneg (mul_nonneg hf0 (by positivity)) (mul_nonneg hcL hLx0))
            (mul_le_mul hfk2 (mul_le_mul_of_nonneg_left hLxLa hcL) (mul_nonneg hcL hLx0) hP0)
      _ = _ := by ring
  have n1 := mul_nonneg hCc hW0
  have e : (2 * Cc + Cp * (12 + Cc + cL)) * nT * a * La =
      Cp * (nT * a * La * 6) + Cp * (nT * a * La * (6 + Cc)) + Cp * (nT * a * La * cL) +
        2 * (Cc * (nT * a * La)) := by ring
  rw [e]
  linarith

theorem slopesM_at_of (D : D7) (L : SizeData₂ D) (Cn C5 C6 cL Cc : ℝ)
    (h5 : flipTwoThree.Conclusion5 D Cn C5 L.sc.x) (h6 : flipTwoThree.Conclusion6 D Cn C6 L.sc.x)
    (hN : NumsL D L Cn cL) (hW : WtsL D L Cn) (CV : ∀ u, flipTwoThree.ColVal D u)
    (hcL : 0 ≤ cL) (hCc : 0 ≤ Cc)
    (hT : ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ Cc * D.R.m * L.sc.L)
    (hk : Real.log (D.R.k : ℝ) ≤ 5 * Real.log L.sc.x)
    (hfkB : (D.R.f : ℝ) * D.R.k * (L.sc.b' + L.Sc) ≤ D.host.TT.card * L.sc.a)
    (hfk2 : (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 ≤ D.host.TT.card * L.sc.a) :
    SlopesM_at L (2 * Cc + max (max C5 C6) 0 * (12 + Cc + cL)) := by
  intro u
  have hv1 : 1 ≤ D.host.v := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hN u
    exact h
  have hv : D.host.v = D.host.rdE / 2 := rfl
  have hrd : 2 ≤ D.host.rdE := by rw [hv] at hv1; linarith
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := by linarith
  have hLx : 0 < L.sc.L := Real.rpow_pos_of_pos hx _
  have hb : 0 < L.sc.b := Real.exp_pos _
  have ha : 0 < L.sc.a := mul_pos hx hb
  have hb' : 0 < L.sc.b' := div_pos ha (Real.exp_pos _)
  have hSc := L.Sc_pos
  have hkN : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hnT : (0 : ℝ) ≤ D.host.TT.card := Nat.cast_nonneg _
  have hlx : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hlrd : 0 ≤ Real.log D.host.rdE := Real.log_nonneg (by linarith)
  have hLa : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
    unfold SizeData₂.La Scale.a Scale.b
    rw [Real.log_mul (mul_pos hx (Real.exp_pos _)).ne' (by linarith), Real.log_mul hx.ne' (Real.exp_pos _).ne',
      Real.log_exp]
  have hLxLa : L.sc.L ≤ L.La := by rw [hLa]; linarith
  have hLa0 : 0 ≤ L.La := by linarith
  have hlk0 : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_natCast_nonneg _
  have hlk : Real.log (D.R.k : ℝ) ≤ 5 * L.La := by rw [hLa]; linarith
  have hlv : Real.log D.host.v ≤ Real.log D.host.rdE :=
    Real.log_le_log (by linarith) (by rw [hv]; linarith)
  have hlkvE : Real.log ((D.R.k : ℝ) * D.host.v) = Real.log (D.R.k : ℝ) + Real.log D.host.v :=
    Real.log_mul (by linarith) (by linarith)
  have hlkv0 : 0 ≤ Real.log ((D.R.k : ℝ) * D.host.v) := by
    rw [hlkvE]; linarith [Real.log_nonneg hv1]
  have hlkv : Real.log ((D.R.k : ℝ) * D.host.v) ≤ 6 * L.La := by
    rw [hlkvE, hLa]; linarith
  have hlT0 : 0 ≤ Real.log ((D.mem u).A.T : ℝ) := Real.log_natCast_nonneg _
  have hlTLa : Real.log ((D.mem u).A.T : ℝ) ≤ Cc * D.R.m * L.La :=
    (hT u).trans (mul_le_mul_of_nonneg_left hLxLa (mul_nonneg hCc hm0))
  have hCp : 0 ≤ max (max C5 C6) 0 := le_max_right _ _
  have hC5 : C5 ≤ max (max C5 C6) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC6 : C6 ≤ max (max C5 C6) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hB0 : 0 ≤ L.sc.b' + L.Sc := by linarith
  constructor
  · have h := h5 u L.sc.b (cL * L.sc.L) L.sc.b' L.Sc L.etaSz (hN u) (hW u) (CV u)
    have hsum : ∑ t ∈ flipTwoThree.tops D, flipTwoThree.aT D u t / D.R.k * Real.log (flipTwoThree.Tu D u) ≤
        (D.host.TT.card : ℝ) * (2 * L.sc.a / D.R.k * Real.log ((D.mem u).A.T : ℝ)) := by
      have h1 : ∀ t ∈ flipTwoThree.tops D, flipTwoThree.aT D u t / D.R.k * Real.log (flipTwoThree.Tu D u) ≤
          2 * L.sc.a / D.R.k * Real.log ((D.mem u).A.T : ℝ) := by
        intro t ht
        have h2 : flipTwoThree.aT D u t ≤ 2 * L.sc.a := ((hW u t).2.1 (jnt_isTop_of_mem D ht)).2.1
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h2 hk0.le) hlT0
      have h3 := Finset.sum_le_card_nsmul _ _ _ h1
      rwa [jnt_card_tops, nsmul_eq_mul] at h3
    exact le_trans (jnt_slope_low _ _ _ _ _ _ _ _ _ _ _ C5 _ cL Cc _ hnT ha.le hLa0 hk0 hf0 hm0 hmk hlT0
      hlTLa hlk0 hlk hB0 hSc.le (by linarith) hLx.le hLxLa hC5 hCp hcL hCc hfkB hfk2 hsum) h
  · have h := h6 u L.sc.b (cL * L.sc.L) L.sc.b' L.Sc L.etaSz (hN u) (hW u) (CV u)
    exact le_trans h (jnt_slope_up _ _ _ _ _ _ _ _ _ _ C6 _ cL Cc hnT ha.le hLa0 hk0 hf0 hmk hlT0
      hlTLa hlkv0 hlkv hB0 hLx.le hLxLa hC6 hCp hcL hCc hfkB hfk2)

theorem jnt_rpow_le_pow {x y : ℝ} (hx : 1 ≤ x) (K : ℕ) (hy : y ≤ K) : x ^ y ≤ x ^ K := by
  calc x ^ y ≤ x ^ (K : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hy
    _ = x ^ K := Real.rpow_natCast x K

theorem jnt_pow_le_exp (K : ℕ) (e : ℝ) (he : 0 < e) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → x ^ K ≤ Real.exp (x ^ e) := by
  have h1 := (isLittleO_rpow_exp_atTop ((K : ℝ) / e)).bound one_pos
  have h2 := (tendsto_rpow_atTop he).eventually h1
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp (h2.and (Filter.eventually_ge_atTop 0))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨ha, hb⟩ := hx0 x hx
  have he' : e * ((K : ℝ) / e) = K := by field_simp
  rw [← Real.rpow_mul hb, he', Real.rpow_natCast, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hb K), abs_of_pos (Real.exp_pos _)] at ha
  exact ha

theorem jnt_sizes_slopes (D : D7) (L : SizeData₂ D) (hS : SizesAt L) (hx2 : 2 ≤ L.sc.x)
    (hX : L.sc.x ^ 14 ≤ L.sc.X') :
    Real.log (D.R.k : ℝ) ≤ 5 * Real.log L.sc.x ∧
    (D.R.f : ℝ) * D.R.k * (L.sc.b' + L.Sc) ≤ D.host.TT.card * L.sc.a ∧
    (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 ≤ D.host.TT.card * L.sc.a := by
  obtain ⟨hSN, -, hSK, -, -, -, -, hTT, -, -, -, -, -, -, -, -, hDel, -⟩ := hS
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hx : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have ha : 0 < L.sc.a := mul_pos hx hb
  have hXp : 0 < L.sc.X' := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos ha hXp
  have hSc := L.Sc_pos
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 :=
    hSN.2.trans (jnt_rpow_le_pow hx1 3 (by unfold szTh; push_cast; linarith))
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ 5 :=
    hSK.2.trans (jnt_rpow_le_pow hx1 5 (by unfold szTh; push_cast; linarith))
  have hkN : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  have hnpos : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by unfold Ranks.n; positivity
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.toFrame.ord_pos
    exact_mod_cast this
  have hf : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hnT : (1 : ℝ) ≤ D.host.TT.card := by
    have h0 : (0 : ℝ) < D.host.TT.card :=
      lt_of_lt_of_le (mul_pos (mul_pos (Real.rpow_pos_of_pos hx _) hnpos)
        (Real.rpow_pos_of_pos hx _)) hTT.1
    have : 0 < D.host.TT.card := by exact_mod_cast h0
    exact_mod_cast this
  have hx6 : (64 : ℝ) ≤ L.sc.x ^ 6 := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ L.sc.x ^ 6 := pow_le_pow_left₀ (by norm_num) hx2 6
  have hx8 : 0 < L.sc.x ^ 8 := by positivity
  have hx13 : 0 < L.sc.x ^ 13 := by positivity
  have haT : L.sc.a ≤ D.host.TT.card * L.sc.a := le_mul_of_one_le_left ha.le hnT
  refine ⟨?_, ?_, ?_⟩
  · have := Real.log_le_log hk0 hk5
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  · have hScb : L.Sc ≤ L.sc.b' := by
      have h1 : (D.R.k : ℝ) * L.Sc ≤ L.sc.b' / (L.sc.x * D.R.n) := hDel.2.2.2.1
      have h2 : L.sc.b' / (L.sc.x * D.R.n) ≤ L.sc.b' :=
        div_le_self hb'.le (by nlinarith)
      have h3 : L.Sc ≤ (D.R.k : ℝ) * L.Sc := le_mul_of_one_le_left hSc.le (by linarith)
      linarith
    have h2fk : 2 * ((D.R.f : ℝ) * D.R.k) ≤ L.sc.X' := by
      rw [hf]
      calc 2 * (2 * (D.R.n : ℝ) * D.R.k) = 4 * ((D.R.n : ℝ) * D.R.k) := by ring
        _ ≤ 4 * (L.sc.x ^ 3 * L.sc.x ^ 5) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul hn3 hk5 hk0.le (by positivity)
        _ = 4 * L.sc.x ^ 8 := by ring
        _ ≤ L.sc.x ^ 6 * L.sc.x ^ 8 := mul_le_mul_of_nonneg_right (by linarith) hx8.le
        _ = L.sc.x ^ 14 := by ring
        _ ≤ L.sc.X' := hX
    have hfk0 : 0 ≤ (D.R.f : ℝ) * D.R.k := by positivity
    calc (D.R.f : ℝ) * D.R.k * (L.sc.b' + L.Sc) ≤ (D.R.f : ℝ) * D.R.k * (2 * L.sc.b') :=
          mul_le_mul_of_nonneg_left (by linarith) hfk0
      _ = (2 * ((D.R.f : ℝ) * D.R.k)) * L.sc.b' := by ring
      _ ≤ L.sc.X' * L.sc.b' := mul_le_mul_of_nonneg_right h2fk hb'.le
      _ = L.sc.a := by unfold Scale.b'; field_simp
      _ ≤ _ := haT
  · have hXa : L.sc.X' ≤ L.sc.a := by
      have h1 : L.sc.X' ≤ L.sc.b := by
        unfold Scale.X' Scale.b Scale.L
        exact Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
      have h2 : L.sc.b ≤ L.sc.a := le_mul_of_one_le_left hb.le hx1
      linarith
    rw [hf]
    calc 2 * (D.R.n : ℝ) * (D.R.k : ℝ) ^ 2 ≤ 2 * L.sc.x ^ 3 * (L.sc.x ^ 5) ^ 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hn3 (by norm_num))
            (pow_le_pow_left₀ hk0.le hk5 2) (by positivity) (by positivity)
      _ = 2 * L.sc.x ^ 13 := by ring
      _ ≤ L.sc.x * L.sc.x ^ 13 := mul_le_mul_of_nonneg_right hx2 hx13.le
      _ = L.sc.x ^ 14 := by ring
      _ ≤ L.sc.X' := hX
      _ ≤ L.sc.a := hXa
      _ ≤ _ := haT

theorem slopesMF_of {eps : ℝ} (Fm : FamP eps) (Cn cL : ℝ) (hcL : 0 ≤ cL)
    (h5 : flipTwoThree.ConclusionF5 Fm) (h6 : flipTwoThree.ConclusionF6 Fm)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ WtsL (Fm.D x i) (Fm.L x i) Cn ∧
        ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hT : ∃ Cc x0 : ℝ, 0 ≤ Cc ∧ ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
      Real.log (((Fm.D x i).mem u).A.T : ℝ) ≤ Cc * (Fm.D x i).R.m * (Fm.L x i).sc.L) :
    ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, SlopesM_at (Fm.L x i) C := by
  have heps : 0 < eps := by
    obtain ⟨i0⟩ := Fm.Ix_zero
    have := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨xA, hA⟩ := jnt_pow_le_exp 14 (eps / 3) (by positivity)
  obtain ⟨C5, x5, h5⟩ := h5 Cn
  obtain ⟨C6, x6, h6⟩ := h6 Cn
  obtain ⟨xE, hE⟩ := hE
  obtain ⟨Cc, xT, hCc, hT⟩ := hT
  refine ⟨2 * Cc + max (max C5 C6) 0 * (12 + Cc + cL),
    max (max (max x5 x6) (max xE xT)) (max xA (max 2 (Fm.x1 + 1))),
    add_nonneg (by linarith) (mul_nonneg (le_max_right _ _) (by linarith)), fun x hx i => ?_⟩
  have hx5 : x5 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx6 : x6 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hxE : xE ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxT : xT ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hxA : xA ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : 2 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  obtain ⟨hN, hW, hCV⟩ := hE x hxE i
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hX : (Fm.L x i).sc.x ^ 14 ≤ (Fm.L x i).sc.X' := by
    unfold Scale.X'
    rw [hsx, hse]
    exact hA x hxA
  obtain ⟨s1, s2, s3⟩ := jnt_sizes_slopes _ (Fm.L x i) (Fm.sizes x hx1 i) (by rw [hsx]; exact hx2) hX
  have h5' : flipTwoThree.Conclusion5 (Fm.D x i) Cn C5 (Fm.L x i).sc.x := by rw [hsx]; exact h5 x hx5 hx1 i
  have h6' : flipTwoThree.Conclusion6 (Fm.D x i) Cn C6 (Fm.L x i).sc.x := by rw [hsx]; exact h6 x hx6 hx1 i
  exact slopesM_at_of _ _ Cn C5 C6 cL Cc h5' h6' hN hW (fun u => (hCV u).some) hcL hCc
    (hT x hxT i) s1 s2 s3

theorem _root_.Formalism.MainNotions.GlobalTheoryTheory.slopesMF_of_count {eps : ℝ} (Fm : FamP eps) (Cn cL : ℝ) (hcL : 0 ≤ cL)
    (h5 : flipTwoThree.ConclusionF5 Fm) (h6 : flipTwoThree.ConclusionF6 Fm)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ WtsL (Fm.D x i) (Fm.L x i) Cn ∧
        ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hC : Lnk.CountF Fm) : Lnk.SlopesMF Fm := by
  obtain ⟨C, x0, hC0, h⟩ := hC
  exact slopesMF_of Fm Cn cL hcL h5 h6 hE ⟨C, x0, hC0, fun x hx i u => (h x hx i u).2.1⟩

end

end JSL

end Formalism.MainNotions.GlobalTheoryTheory

end
