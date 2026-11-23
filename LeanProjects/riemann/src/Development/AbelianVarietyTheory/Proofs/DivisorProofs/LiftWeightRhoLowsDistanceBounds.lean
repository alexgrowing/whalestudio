import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

theorem low_dist : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → ((Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) ≤ a ∧ a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ) ∨ Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) + (GlobalTheory.ExpTie.Lift.wts L j).j τ + (GlobalTheory.ExpTie.parOf L j).t ≤ a) → 2 * (GlobalTheory.ExpTie.parOf L j).b / (GlobalTheory.ExpTie.parOf L j).lstar + ((GlobalTheory.ExpTie.parOf L j).t : ℝ) / 2 + 3 ≤ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ∧ |((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) - (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.Lift.wts L j).e τ| ≤ (GlobalTheory.ExpTie.parOf L j).η := by
  intro D L P5 j τ hv a ha hcase
  have hn := rank_eq j
  have hk := D.R.m_add_three_le_k
  have hjm := j.2
  change a < (Vc D j).rank at ha
  change (D.R.k - 1 ≤ a ∧ a < D.R.k - 1 + ((j : ℕ) + 1)) ∨ D.R.k - 1 + ((j : ℕ) + 1) + D.R.t ≤ a at hcase
  obtain ⟨i, hval⟩ : ∃ i : Fin D.R.m,
      ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ) := by
    rcases hcase with ⟨h1, h2⟩ | h1
    · refine ⟨⟨a - (D.R.k - 1), by omega⟩, ?_⟩
      have h := hv.2.1 ⟨a - (D.R.k - 1), by omega⟩ (by simp only [Fin.le_def]; omega)
      have ha' : D.R.k - 1 + (a - (D.R.k - 1)) = a := by omega
      simp only [ha'] at h
      exact h
    · refine ⟨⟨a - (D.R.k - 1) - D.R.t, by omega⟩, ?_⟩
      have h := hv.2.2.2 ⟨a - (D.R.k - 1) - D.R.t, by omega⟩ (by simp only [Fin.lt_def]; omega)
      have ha' : D.R.k - 1 + (a - (D.R.k - 1) - D.R.t) + D.R.t = a := by omega
      simp only [ha'] at h
      exact h
  have he : (wts L j).e τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    show wj D ((j : ℕ) + 1) τ = _
    unfold wj
    rw [dif_pos (by omega)]
    congr 3
  have habs : |((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ + (wts L j).e τ| =
      |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| := by
    rw [hval, he, ← abs_neg]
    push_cast
    ring_nf
  rw [habs]
  refine ⟨?_, L.be_close τ i j⟩
  have hN : ((D.R.N D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by
    unfold Ranks.N
    push_cast
    ring
  have hls : (parOf L j).lstar = LevelStarExponents.lStar L := by
    unfold Formalism.CohomologicalDescent.LogSmallConstantBounds.Par.lstar LevelStarExponents.lStar
    rw [hN]
    rfl
  have hb : (parOf L j).b = L.sc.b := rfl
  rw [hls, hb]
  exact P5.lows_far τ i j

end GlobalTheory.ExpTie.Lift

end
