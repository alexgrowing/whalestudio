import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvHasInfinityTypeCmType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeightEqAbsInfType
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BotSmall

theorem bottom_small : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (δ t0 : ℂ) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q) (i j : Fin D.R.m) 𝔪, IsBottom G μ₀ i j 𝔪 P P' → P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap) := by
  intro D T L sc μ₀ hL G δ t0 Q P P' i j 𝔪 hB
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hB.rank
  have hd : P.d ≤ 2 * bigN D := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    have hj := j.2
    obtain ⟨e1, e2, -⟩ := ranks_exact D i j
    have h1 : rankV D (i + 1) (j + 1) ≤ bigN D - 1 := by
      simp only [rankV, bigN, Ranks.r]
      have : (↑i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ (by omega)
      have : (↑j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
      have : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
      omega
    have h2 : rankV D i j ≤ rankV D (i + 1) (j + 1) := by
      simp only [rankV]
      have : (↑i) * sLen D ≤ (↑i + 1) * sLen D := Nat.mul_le_mul_right _ (by omega)
      have : (↑j) * D.R.t ≤ (↑j + 1) * D.R.t := Nat.mul_le_mul_right _ (by omega)
      omega
    omega

  have key : ∀ (R : Pair D ⊤ δ t0 Q) (χ : Formalism.L2.Host.HChar D.host.E),
      HasChars R χ (nuH G μ₀ i j)⁻¹ → R.d = botBig D i j + botSmall D i j → ∀ τ, (R.n τ : ℝ) ≤ 2 * (maxWt D sc.cGap : ℝ) := by
    intro R χ hc hRd τ
    have habs := GlobalTheory.SplitWeight.abs_weight_eq_abs_infType R.W.chV' R.W.ep' (nuH G μ₀ i j)⁻¹ _ R.W.ep_pm.2 hc.2
      (nuH_inv_hasInf hL G i j) τ
    have hw := R.wt τ
    have hsub := two_mul_wtA_sub D sc.cGap i j τ
    set E := (num D sc.cGap τ).e (↑j + 1) + cen D sc.cGap τ (D.R.m - ↑i)
    have hA : (wtA D sc.cGap i j τ).natAbs ≤ maxWt D sc.cGap ∧ (wtA' D sc.cGap i j τ).natAbs ≤ maxWt D sc.cGap := by
      have := Finset.le_sup (f := fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
        max (wtA D sc.cGap x.1 x.2.1 x.2.2).natAbs (wtA' D sc.cGap x.1 x.2.1 x.2.2).natAbs) (Finset.mem_univ (i, j, τ))
      have h2 := le_max_right 1 (Finset.univ.sup fun x : Fin D.R.m × Fin D.R.m × D.what₂.Tau =>
        max (wtA D sc.cGap x.1 x.2.1 x.2.2).natAbs (wtA' D sc.cGap x.1 x.2.1 x.2.2).natAbs)
      simp only at this
      exact ⟨le_trans (le_max_left _ _) (this.trans h2), le_trans (le_max_right _ _) (this.trans h2)⟩
    have hA1 : |wtA D sc.cGap i j τ| ≤ (maxWt D sc.cGap : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA.1
    have hA2 : |wtA' D sc.cGap i j τ| ≤ (maxWt D sc.cGap : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hA.2
    have hep : |(R.W.ep' : ℤ) * R.W.chV'.n τ| = |2 * E| := by
      rw [abs_mul, ← habs]
      rcases R.W.ep_pm.2 with h | h <;> rw [h] <;> simp
    have hdz : (R.d : ℤ) = (botBig D i j : ℤ) + (botSmall D i j : ℤ) := by rw [hRd]; push_cast; ring
    have hn : (R.n τ : ℤ) ≤ 2 * (maxWt D sc.cGap : ℤ) := by
      have hnn : (0 : ℤ) ≤ R.n τ := Nat.cast_nonneg _
      have hpos : 0 ≤ (R.W.ep' : ℤ) * R.W.chV'.n τ := by push_cast at hw; omega
      rw [abs_of_nonneg hpos] at hep
      have h1 := abs_le.1 hA1
      have h2 := abs_le.1 hA2
      rcases le_or_gt 0 E with hE | hE
      · rw [abs_of_nonneg (by omega)] at hep
        push_cast at hw hsub; omega
      · rw [abs_of_neg (by omega)] at hep
        push_cast at hw hsub; omega
    exact_mod_cast hn
  exact ⟨⟨hd, key P _ hB.chars hr3⟩, ⟨hr4 ▸ hd, key P' _ hB.chars' (hr4.trans hr3)⟩⟩

end GlobalTheory.BotSmall
