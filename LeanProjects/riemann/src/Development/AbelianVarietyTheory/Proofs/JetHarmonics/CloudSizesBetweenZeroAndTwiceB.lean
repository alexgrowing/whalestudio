import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem sizes_le_two_mul : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → L.Sc + L.etaSz ≤ 2 * L.sc.b ∧ ∀ j, InR D j → (∀ τ, 0 ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b) ∧ (∀ t, wj D j (plOf D (false, t)) ≤ 2 * L.sc.b') ∧ ∀ z, (numOf D L).w j z = wj D j (plOf D z) := by
  intro D L P hx hkb
  have hk : (5 : ℝ) ≤ D.R.k := by
    have : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    exact_mod_cast this
  have hx0 : 0 < L.sc.x := by linarith
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have hbb : 5 * L.sc.b' ≤ L.sc.b := le_trans (by nlinarith) hkb
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 3 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  have hw0 : 0 < L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' / 3 := by
    unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'.le (by norm_num) (by nlinarith)
  have ht := L.t_win.1
  have he1 : 1 ≤ L.etaSz := le_trans ht P.t_le_eta
  have he : L.etaSz ≤ L.sc.b' / 9 := by
    have h1 := P.teta
    have h2 : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n / 3 :=
      div_le_div_of_nonneg_left hw0.le (by norm_num) hx
    nlinarith
  have hS0 := L.Sc_pos
  have hS : L.Sc ≤ L.sc.b' / 3 := by
    have := P.kS_le
    nlinarith
  have hk0 : (0 : ℝ) < D.R.k := by linarith
  have hLa : 0 < L.LaG := by
    have h1 : 0 < L.LaG * L.sc.b' / D.R.k := by have := P.S_le; linarith
    have h2 : 0 < L.LaG * L.sc.b' := (div_pos_iff_of_pos_right hk0).1 h1
    exact (mul_pos_iff_of_pos_right hb').1 h2
  have hbT : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
    intro t
    have h1 := P.bT_le t
    have h2 := P.rho_le
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h4 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
      have := P.Crho_pos
      have := Real.log_nonneg (show 1 ≤ L.sc.x by linarith)
      positivity
    unfold LevelStarExponents.rhoP at h2
    set A := LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k with hA
    have h5 : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * A := by rw [hA]; ring
    have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = A * L.sc.b' := by rw [hA]; ring
    have h7 : A ≤ 1 / 4 := by linarith
    rw [h6] at h1
    nlinarith
  refine ⟨by linarith, fun j hj => ?_⟩
  have hoff : ∀ τ, (D.eTau τ : D.R.GG) ∉ D.host.thickPlaces →
      0 ≤ wj D j τ ∧ wj D j τ ≤ 2 * L.sc.b' := by
    intro τ hτ
    by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at htop
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 htop
      obtain ⟨h1, h2⟩ := L.win_top j hj.1 hj.2 τ ⟨t, htT⟩ hteq.symm
      have h3 := hbT ⟨t, htT⟩
      have h4 := L.bT_ge ⟨t, htT⟩
      have h5 : 0 ≤ L.sc.b' / L.sc.x := by positivity
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := L.win_thin j hj.1 hj.2 τ ⟨(D.eTau τ).2, htop, hτ⟩
      constructor <;> linarith
  refine ⟨fun τ => ?_, fun t => (hoff _ ?_).2, fun z => ?_⟩
  · by_cases hτ : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨h1, h2⟩ := L.win_thick j hj.1 hj.2 τ hτ
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := hoff τ hτ
      constructor <;> linarith
  · classical
    intro h
    unfold Host.thickPlaces at h
    obtain ⟨s, -, hs⟩ := Finset.mem_image.1 h
    have h1 : (D.eTau (plOf D (false, t)) : D.R.GG) = D.R.tau1 t := by
      simp [plOf]
    rw [h1] at hs
    have h2 := congrArg (fun g : D.R.GG => g.1.1) hs
    simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h2
    exact absurd h2 (by decide)
  · have h1 : 1 ≤ j ∧ j ≤ (numOf D L).R.m := hj
    have h2 : j - 1 < D.R.m := by have := hj.1; have := hj.2; omega
    rw [NumDatum.w, NumDatum.eQ, dif_pos h1, wj, dif_pos h2]
    rfl

end GlobalTheory.RunDepth
