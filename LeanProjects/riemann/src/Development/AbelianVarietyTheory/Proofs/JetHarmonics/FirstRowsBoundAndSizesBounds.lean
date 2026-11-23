import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulRowsScaledWeightLeKappaRows
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KappaRowsEntriesLeSizes
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudSizesBetweenZeroAndTwiceB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FirstRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem sum_ite_le {ι β : Type} [Fintype ι] (φ : ι → β) (hφ : Function.Injective φ) (y : β)
    [∀ t, Decidable (y = φ t)] (g : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (hg : ∀ t, g t ≤ B) :
    (∑ t, if y = φ t then g t else 0) ≤ B := by
  classical
  by_cases h : ∃ t, y = φ t
  · obtain ⟨t, rfl⟩ := h
    rw [Finset.sum_eq_single t]
    · simpa using hg t
    · intro t' _ ht'
      rw [if_neg fun h => ht' (hφ h).symm]
    · simp
  · rw [Finset.sum_eq_zero fun t _ => if_neg fun h' => h ⟨t, h'⟩]
    exact hB

theorem tauEmb_injective (D : D7) : Function.Injective (DV.tauEmb D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conj_tauEmb_injective (D : D7) :
    Function.Injective fun t => ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t) := by
  intro s t h
  apply tauEmb_injective D
  ext x
  have := RingHom.congr_fun h x
  exact (starRingEnd ℂ).injective this

theorem mul_wtA_le {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (i : ℕ)
    (hP : ∀ t, T * (ext0 (w.aP t) i : ℝ) ≤ A) (hM : ∀ t, T * (ext0 (w.aM t) i : ℝ) ≤ B) (τ : D.host.E →+* ℂ) :
    T * wtA w (τ, i) ≤ A + B := by
  classical
  unfold wtA
  push_cast
  rw [Finset.mul_sum]
  simp only [mul_add, mul_ite, mul_zero]
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · convert sum_ite_le (DV.tauEmb D) (tauEmb_injective D) τ _ A hA hP
  · convert sum_ite_le _ (conj_tauEmb_injective D) τ _ B hB hM

theorem b'_pos (s : Scale) : 0 < s.b' := by
  unfold Scale.b' Scale.a Scale.X' Scale.b
  have : 0 < s.x := by linarith [s.one_lt_alt]
  positivity

theorem w''_le (s : Scale) (n : ℕ) (hn : 1 ≤ n) (hx : 3 ≤ s.x) : s.w'' n ≤ s.b' / 3 := by
  unfold Scale.w''
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left (b'_pos s).le (by norm_num) (by nlinarith)

theorem first_rows_and_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  (∀ τ : D.host.E →+* ℂ, (Tp.TO : ℝ) * wtA (lR Tp hK j) (τ, 0) ≤ 3 * L.sc.b) ∧ ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z ∧ (numOf D L).w j z ≤ 2 * L.sc.b := by
  intro D L Pm Tp hK j hj hx hkb
  obtain ⟨-, hsz⟩ := GlobalTheory.RunDepth.sizes_le_two_mul D L Pm hx hkb
  obtain ⟨hw, -, hnum⟩ := hsz j hj
  have hb' := b'_pos L.sc
  have hn : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hw3 := w''_le L.sc D.R.n hn hx
  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hbb : L.sc.b' ≤ L.sc.b := by nlinarith
  have hSc : L.Sc ≤ L.sc.b' / 3 := by nlinarith [Pm.kS_le, L.Sc_pos]
  have heta : L.etaSz ≤ L.sc.b' / 3 := by
    have h1 := Pm.teta
    have h2 := L.t_win.1
    have h3 := L.etaSz_pos
    have h0 : 0 ≤ L.sc.w'' D.R.n := by nlinarith [Pm.kS_le, L.Sc_pos]
    have h4 : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n := div_le_self h0 L.sc.one_lt_alt.le
    nlinarith
  have hScp := L.Sc_pos
  have hetap := L.etaSz_pos
  refine ⟨fun τ => ?_, fun z => ⟨?_, ?_⟩⟩
  · have := mul_wtA_le (lR Tp hK j) (Tp.TO : ℝ) (2 * L.sc.b + L.Sc) L.etaSz (by linarith) hetap.le 0 ?_ ?_ τ
    · linarith
    · intro t
      unfold ext0
      split_ifs with h
      · have h1 := (GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).1 ⟨0, h⟩
        have h2 := (GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t).1 ⟨0, h⟩ (by show 0 < D.R.k - 1; omega)
        have h3 : (Tp.TO : ℝ) * ((lR Tp hK j).aP t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aP t ⟨0, h⟩ : ℝ) := by exact_mod_cast h1
        linarith [(hw t).2]
      · simp only [Nat.cast_zero, mul_zero]; linarith
    · intro t
      unfold ext0
      split_ifs with h
      · have h1 := (GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).2.1 ⟨0, h⟩
        have h2 := (GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t).2.2 ⟨0, h⟩
        have h3 : (Tp.TO : ℝ) * ((lR Tp hK j).aM t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aM t ⟨0, h⟩ : ℝ) := by exact_mod_cast h1
        linarith
      · simp only [Nat.cast_zero, mul_zero]; linarith
  · rw [hnum z]
    set τ := plOf D z
    by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at htop
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
      have h1 := (L.win_top j hj.1 hj.2 τ ⟨t, ht⟩ hte.symm).1
      have h2 := L.bT_ge ⟨t, ht⟩
      have h3 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb'.le (by linarith)
      linarith
    · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have h1 := (L.win_thick j hj.1 hj.2 τ hth).1
        linarith
      · exact (L.win_thin j hj.1 hj.2 τ ⟨(D.eTau τ).2, htop, hth⟩).1
  · rw [hnum z]
    exact (hw _).2

end GlobalTheory.FirstRows
