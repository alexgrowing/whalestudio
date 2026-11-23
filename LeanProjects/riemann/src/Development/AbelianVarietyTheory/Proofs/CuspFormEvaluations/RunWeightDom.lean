import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionary
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaWeightData

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.RunWeightDom

theorem lt_of_succ_lt {p : ℕ} {f : ℕ → ℤ} (h : ∀ i, i + 1 < p → f (i + 1) < f i) :
    ∀ i j, i < j → j < p → f j < f i := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hik | rfl
    · exact lt_trans (h k (by omega)) (ih hik (by omega))
    · exact h i (by omega)

theorem le_of_succ_lt {p : ℕ} {f : ℕ → ℤ} (h : ∀ i, i + 1 < p → f (i + 1) < f i) (i : ℕ) (hi : i < p) :
    f (p - 1) ≤ f i := by
  rcases Nat.lt_or_ge i (p - 1) with hlt | hge
  · exact (lt_of_succ_lt h i (p - 1) hlt (by omega)).le
  · have : i = p - 1 := by omega
    subst this
    exact le_rfl

theorem fdiv_spec {x y T' : ℤ} (hT : 0 < T') (h : y = Int.fdiv x T') :
    ∃ ρ, 0 ≤ ρ ∧ ρ < T' ∧ x = T' * y + ρ := by
  have e : Int.fdiv x T' = x / T' := Int.fdiv_eq_ediv_of_nonneg x hT.le
  refine ⟨x % T', Int.emod_nonneg x hT.ne', Int.emod_lt_of_pos x hT, ?_⟩
  rw [h, e]
  exact (Int.mul_ediv_add_emod x T').symm

theorem block {p : ℕ} (hp : 0 < p) (ka wL wF : Fin p → ℕ) (T Dm r c : ℤ) (hD : 0 ≤ Dm) (hr : 0 ≤ r)
    (h40 : 40 * (Dm + 2) ≤ T) (hc : c ≤ T)
    (hg : ∀ i : Fin p, i.1 + 1 < p → (T + Dm + 2) * (T + Dm + 2 + 2 * r) ≤ gapZ ka i + 2)
    (hl : ∀ i : Fin p, i.1 + 1 = p → 2 * T ^ 2 ≤ ka i)
    (hL : ∀ i : Fin p, gapZ wL i = if i.1 + 1 < p then Int.fdiv (gapZ ka i + 2) (T + Dm + 2)
      else Int.fdiv ((ka i : ℤ) - c) (T + Dm + 2))
    (hF : ∀ i, (wF i : ℤ) = ka i - T * wL i) :
    (∀ i, i + 1 < p → (ext0 wL (i + 1) : ℤ) < ext0 wL i) ∧
    (∀ i, i + 1 < p → (ext0 wF (i + 1) : ℤ) - 2 + (Dm + 2) * (ext0 wL i - ext0 wL (i + 1)) ≤ ext0 wF i) ∧
    19 * T ≤ 10 * (ext0 wL (p - 1) : ℤ) ∧ (Dm + 2) * (ext0 wL (p - 1) : ℤ) + c ≤ ext0 wF (p - 1) := by
  have hT' : 0 < T + Dm + 2 := by linarith
  have e : ∀ (f : Fin p → ℕ) (i : ℕ) (hi : i < p), ext0 f i = f ⟨i, hi⟩ := by
    intro f i hi
    simp [ext0, hi]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [e wL (i + 1) hi, e wL i (by omega)]
    have hg' := hg ⟨i, by omega⟩ hi
    have hL' := hL ⟨i, by omega⟩
    simp only [gapZ, hi, dif_pos, if_true] at hL' hg'
    obtain ⟨ρ, hρ0, hρ1, hx⟩ := fdiv_spec hT' hL'
    nlinarith
  · intro i hi
    rw [e wF (i + 1) hi, e wF i (by omega), e wL (i + 1) hi, e wL i (by omega),
      hF ⟨i + 1, hi⟩, hF ⟨i, by omega⟩]
    have hL' := hL ⟨i, by omega⟩
    simp only [gapZ, hi, dif_pos, if_true] at hL'
    obtain ⟨ρ, hρ0, hρ1, hx⟩ := fdiv_spec hT' hL'
    linarith
  · have hlast : p - 1 < p := by omega
    rw [e wL (p - 1) hlast]
    have hl' := hl ⟨p - 1, hlast⟩ (by simp; omega)
    have hL' := hL ⟨p - 1, hlast⟩
    have hn : ¬ (p - 1 + 1 < p) := by omega
    simp only [gapZ, hn, dif_neg, if_false, not_false_eq_true] at hL'
    obtain ⟨ρ, hρ0, hρ1, hx⟩ := fdiv_spec hT' hL'
    by_contra hc'
    have h1 : 10 * (wL ⟨p - 1, hlast⟩ : ℤ) ≤ 19 * T - 1 := by linarith [not_le.mp hc']
    nlinarith [mul_le_mul_of_nonneg_left h1 hT'.le, mul_nonneg (by linarith : (0 : ℤ) ≤ 41 * T - 40 * (T + Dm + 2)) (by linarith : (0 : ℤ) ≤ 19 * T + 9)]
  · have hlast : p - 1 < p := by omega
    rw [e wL (p - 1) hlast, e wF (p - 1) hlast, hF ⟨p - 1, hlast⟩]
    have hL' := hL ⟨p - 1, hlast⟩
    have hn : ¬ (p - 1 + 1 < p) := by omega
    simp only [gapZ, hn, dif_neg, if_false, not_false_eq_true] at hL'
    obtain ⟨ρ, hρ0, hρ1, hx⟩ := fdiv_spec hT' hL'
    nlinarith

theorem row {r p q : ℕ} (hpq : p + q = r) (T Dm nL nF : ℤ) (hnL : 0 ≤ nL) (hnF : 0 ≤ nF)
    (LP LM FP FM : ℕ → ℤ) (L F : Fin r → ℤ) (hT : 0 ≤ T)
    (hL : ∀ a : Fin r, L a = if q ≤ (a : ℕ) then LP (a - q) + nL else -LM (q - 1 - a) - nL)
    (hF : ∀ a : Fin r, F a = if q ≤ (a : ℕ) then FP (a - q) + nF else -FM (q - 1 - a) - nF)
    (p1 : ∀ i, i + 1 < p → LP (i + 1) < LP i)
    (p2 : ∀ i, i + 1 < p → FP (i + 1) - 2 + (Dm + 2) * (LP i - LP (i + 1)) ≤ FP i)
    (p3 : 19 * T ≤ 10 * LP (p - 1)) (p4 : (Dm + 2) * LP (p - 1) + ((Dm + 2) * (2 * nL) + 2 * r) ≤ FP (p - 1))
    (m1 : ∀ i, i + 1 < q → LM (i + 1) < LM i)
    (m2 : ∀ i, i + 1 < q → FM (i + 1) - 2 + (Dm + 2) * (LM i - LM (i + 1)) ≤ FM i)
    (m3 : 19 * T ≤ 10 * LM (q - 1)) (m4 : (Dm + 2) * LM (q - 1) + 0 ≤ FM (q - 1)) :
    (∀ i j : Fin r, i < j → (j : ℕ) < q → L j < L i) ∧
    (∀ i j : Fin r, q ≤ (i : ℕ) → i < j → L j < L i) ∧
    (∀ a b : Fin r, (b : ℕ) = a + 1 → (b : ℕ) ≠ q →
      F b - (2 * (b : ℤ) - ((r : ℤ) - 1)) - Dm * L b + 2 * (L a - L b) ≤
        F a - (2 * (a : ℤ) - ((r : ℤ) - 1)) - Dm * L a) ∧
    (∀ a b : Fin r, (a : ℕ) < q → q ≤ (b : ℕ) → 19 * T ≤ 10 * (L b - L a)) ∧
    (∀ a b : Fin r, (a : ℕ) = 0 → (b : ℕ) = r - 1 → 0 < p → 0 < q →
      2 * (L b - L a) ≤ F b - (2 * (b : ℤ) - ((r : ℤ) - 1)) - Dm * L b -
        (F a - (2 * (a : ℤ) - ((r : ℤ) - 1)) - Dm * L a)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij hjq
    have hij' : (i : ℕ) < j := hij
    have hi' : ¬ q ≤ (i : ℕ) := by omega
    have hj' : ¬ q ≤ (j : ℕ) := by omega
    rw [hL i, hL j, if_neg hi', if_neg hj']
    have key := lt_of_succ_lt m1 (q - 1 - j) (q - 1 - i) (by omega) (by omega)
    linarith
  · intro i j hqi hij
    have hij' : (i : ℕ) < j := hij
    have hj' : q ≤ (j : ℕ) := by omega
    have hjr := j.isLt
    rw [hL i, hL j, if_pos hqi, if_pos hj']
    have key := lt_of_succ_lt p1 (i - q) (j - q) (by omega) (by omega)
    linarith
  · intro a b hb hbq
    have hbr := b.isLt
    have hbz : ((b : ℕ) : ℤ) = ((a : ℕ) : ℤ) + 1 := by rw [hb]; push_cast; ring
    by_cases ha : q ≤ (a : ℕ)
    · have hb' : q ≤ (b : ℕ) := by omega
      rw [hL a, hL b, hF a, hF b, if_pos ha, if_pos ha, if_pos hb', if_pos hb']
      have hi : (b : ℕ) - q = (a : ℕ) - q + 1 := by omega
      rw [hi]
      have key := p2 ((a : ℕ) - q) (by omega)
      rw [hbz]
      linarith
    · have hb' : ¬ q ≤ (b : ℕ) := by omega
      rw [hL a, hL b, hF a, hF b, if_neg ha, if_neg ha, if_neg hb', if_neg hb']
      have hi : q - 1 - (a : ℕ) = q - 1 - (b : ℕ) + 1 := by omega
      rw [hi]
      have key := m2 (q - 1 - (b : ℕ)) (by omega)
      rw [hbz]
      linarith
  · intro a b ha hb
    have hbr := b.isLt
    have ha' : ¬ q ≤ (a : ℕ) := by omega
    rw [hL a, hL b, if_neg ha', if_pos hb]
    have h1 := le_of_succ_lt p1 ((b : ℕ) - q) (by omega)
    have h2 := le_of_succ_lt m1 (q - 1 - (a : ℕ)) (by omega)
    linarith
  · intro a b ha hb hp hq
    have ha' : ¬ q ≤ (a : ℕ) := by omega
    have hb' : q ≤ (b : ℕ) := by omega
    rw [hL a, hL b, hF a, hF b, if_neg ha', if_neg ha', if_pos hb', if_pos hb']
    have e1 : q - 1 - (a : ℕ) = q - 1 := by omega
    have e2 : (b : ℕ) - q = p - 1 := by omega
    have e3 : ((b : ℕ) : ℤ) = (r : ℤ) - 1 := by
      rw [hb]; have : 1 ≤ r := by omega
      push_cast [this]; ring
    have e4 : ((a : ℕ) : ℤ) = 0 := by rw [ha]; rfl
    rw [e1, e2, e3, e4]
    linarith

theorem run_weight_dom : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → j < D.R.m → 8 ≤ D.R.r → ∀ k : (T.U j T.σ₀).Comp, IsStrictDom ((T.U j T.σ₀).X k) (laR T j wL k) ∧ IsStrictDom ((T.U j T.σ₀).X k) (2 • laR T j wL k - de2W ((T.U j T.σ₀).X k)) ∧ ∀ τ : ((T.U j T.σ₀).X k).Ψ, (∀ a b : Fin D.R.r, (b : ℕ) = a + 1 → (b : ℕ) ≠ ((T.U j T.σ₀).X k).p0 → (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ b + 2 * (laR T j wL k τ a - laR T j wL k τ b) ≤ (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ a) ∧ ∀ a b : Fin D.R.r, (a : ℕ) < ((T.U j T.σ₀).X k).p0 → ((T.U j T.σ₀).X k).p0 ≤ (b : ℕ) → 19 * (Tn : ℤ) ≤ 10 * (laR T j wL k τ b - laR T j wL k τ a) ∧ 2 * (laR T j wL k τ ⟨D.R.r - 1, by have := a.2; omega⟩ - laR T j wL k τ ⟨0, by have := a.2; omega⟩) ≤ (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ ⟨D.R.r - 1, by have := a.2; omega⟩ - (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ ⟨0, by have := a.2; omega⟩ := by
  intro D T h j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hH hjm hr k
  have hj' : 1 ≤ j ∧ j ≤ D.R.m := hj
  obtain ⟨-, -, -, -, -, hp0, -, tt, hlaR⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k
  unfold FamilyHypotheses.HypPage at hH
  obtain ⟨-, hS, -⟩ := hH
  unfold SetC at hS
  obtain ⟨-, hgP, hgM, hh0, -, hlP, hlM, -, -, -, -, -, -, -, hIsL, hIsF, -, -, -, h40, hc, -⟩ := hS
  unfold IsL at hIsL
  unfold IsF' at hIsF
  obtain ⟨hwLn, hLP, hLM⟩ := hIsL
  obtain ⟨-, hFP, hFM⟩ := hIsF
  have hsum : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := Formalism.L2.Geo.sigW_sum D hj'.1 hj'.2
  have hk := D.R.m_add_three_le_k
  have hq : 0 < (D.R.sigW j).2 := by
    show 0 < D.R.m - j
    omega
  have hp : 0 < (D.R.sigW j).1 := by
    show 0 < D.R.k + j - 1
    omega
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = (Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 := by
    unfold Tp
    push_cast
    ring
  have hD : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) := by positivity
  have hr0 : (0 : ℤ) ≤ (D.R.r : ℤ) := by positivity
  have h40' : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ (Tn : ℤ) := by exact_mod_cast h40
  have hc' : ((WeightFamilies.dimY D j : ℤ) + 2) * (nW : ℤ) + 2 * (D.R.r : ℤ) ≤ (Tn : ℤ) := by exact_mod_cast hc
  have hwn : ((wL.n / 2 : ℕ) : ℤ) * 2 = (nW : ℤ) := by
    rw [← hwLn]
    exact_mod_cast Nat.div_two_mul_two_of_even wL.n_even
  have gP : ∀ (t : D.what₂.Tau) (i : Fin (D.R.sigW j).1), i.1 + 1 < (D.R.sigW j).1 →
      ((Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2) * ((Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 + 2 * (D.R.r : ℤ)) ≤
        gapZ (ka.aP t) i + 2 := by
    intro t i hi
    have h1 := hgP t i hi
    push_cast at h1
    rw [hTp] at h1
    exact h1
  have gM : ∀ (t : D.what₂.Tau) (i : Fin (D.R.sigW j).2), i.1 + 1 < (D.R.sigW j).2 →
      ((Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2) * ((Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 + 2 * (D.R.r : ℤ)) ≤
        gapZ (ka.aM t) i + 2 := by
    intro t i hi
    have h1 := hgM t i hi
    push_cast at h1
    rw [hTp] at h1
    exact h1
  have lP : ∀ (t : D.what₂.Tau) (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      2 * (Tn : ℤ) ^ 2 ≤ (ka.aP t i : ℤ) := by
    intro t i hi
    have h1 := hlP t i hi
    have h2 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP t i : ℝ) := by linarith
    exact_mod_cast h2
  have lM : ∀ (t : D.what₂.Tau) (i : Fin (D.R.sigW j).2), i.1 + 1 = (D.R.sigW j).2 →
      2 * (Tn : ℤ) ^ 2 ≤ (ka.aM t i : ℤ) := by
    intro t i hi
    have h1 := hlM t i hi
    have h2 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aM t i : ℝ) := by linarith
    exact_mod_cast h2
  have LPf : ∀ (t : D.what₂.Tau) (i : Fin (D.R.sigW j).1), gapZ (wL.aP t) i =
      if i.1 + 1 < (D.R.sigW j).1 then Int.fdiv (gapZ (ka.aP t) i + 2) ((Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2)
      else Int.fdiv ((ka.aP t i : ℤ) - (((WeightFamilies.dimY D j : ℤ) + 2) * (nW : ℤ) + 2 * (D.R.r : ℤ)))
        ((Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2) := by
    intro t i
    rw [hLP t i, hTp, sub_sub]
  have LMf : ∀ (t : D.what₂.Tau) (i : Fin (D.R.sigW j).2), gapZ (wL.aM t) i =
      if i.1 + 1 < (D.R.sigW j).2 then Int.fdiv (gapZ (ka.aM t) i + 2) ((Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2)
      else Int.fdiv ((ka.aM t i : ℤ) - 0) ((Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2) := by
    intro t i
    rw [hLM t i, hTp, sub_zero]
  have BP := fun t : D.what₂.Tau => block hp (ka.aP t) (wL.aP t) (wF.aP t) (Tn : ℤ) (WeightFamilies.dimY D j : ℤ)
    (D.R.r : ℤ) (((WeightFamilies.dimY D j : ℤ) + 2) * (nW : ℤ) + 2 * (D.R.r : ℤ)) hD hr0 h40' hc' (gP t) (lP t)
    (LPf t) (hFP t)
  have BM := fun t : D.what₂.Tau => block hq (ka.aM t) (wL.aM t) (wF.aM t) (Tn : ℤ) (WeightFamilies.dimY D j : ℤ)
    (D.R.r : ℤ) 0 hD hr0 h40' (by positivity) (gM t) (lM t) (LMf t) (hFM t)
  have RW := fun τ : ((T.U j T.σ₀).X k).Ψ =>
    row (r := D.R.r) (p := (D.R.sigW j).1) (q := (D.R.sigW j).2) hsum (Tn : ℤ) (WeightFamilies.dimY D j : ℤ)
      ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ) (by positivity) (by positivity)
      (fun i => (ext0 (wL.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wL.aM (tt τ)) i : ℤ))
      (fun i => (ext0 (wF.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wF.aM (tt τ)) i : ℤ))
      (laR T j wL k τ) (laR T j wF k τ) (by positivity)
      (fun a => by rw [hlaR wL τ a, hp0]) (fun a => by rw [hlaR wF τ a, hp0])
      (BP (tt τ)).1 (BP (tt τ)).2.1 (BP (tt τ)).2.2.1
      (by
        have h1 := (BP (tt τ)).2.2.2
        rw [← hwn] at h1
        linarith)
      (BM (tt τ)).1 (BM (tt τ)).2.1 (BM (tt τ)).2.2.1 (BM (tt τ)).2.2.2
  unfold IsStrictDom de2W kapW
  rw [hp0]
  refine ⟨fun τ => ?_, fun τ => ?_, fun τ => ?_⟩
  · obtain ⟨R1, R2, -, R4, -⟩ := RW τ
    refine ⟨R1, R2, fun i j hi hj => ?_⟩
    linarith [R4 i j hi hj]
  · obtain ⟨R1, R2, -, R4, -⟩ := RW τ
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul]
    refine ⟨fun i j hij hjq => ?_, fun i j hqi hij => ?_, fun i j hi hj => ?_⟩
    · have hij' : (i : ℕ) < j := hij
      have h1 := R1 i j hij hjq
      split_ifs <;> omega
    · have hij' : (i : ℕ) < j := hij
      have h1 := R2 i j hqi hij
      split_ifs <;> omega
    · have h1 := R4 i j hi hj
      split_ifs <;> omega
  · obtain ⟨-, -, R3, R4, R5⟩ := RW τ
    refine ⟨fun a b hb hbq => ?_, fun a b ha hb => ⟨R4 a b ha hb, ?_⟩⟩
    · have h1 := R3 a b hb hbq
      simp only [Pi.sub_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul]
      linarith
    · have h1 := R5 ⟨0, by omega⟩ ⟨D.R.r - 1, by omega⟩ rfl rfl hp hq
      simp only [Pi.sub_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul]
      linarith

end GlobalTheory.RunWeightDom
