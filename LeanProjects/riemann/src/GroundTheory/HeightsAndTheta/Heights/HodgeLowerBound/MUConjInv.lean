import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagSectionNeZero
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Imports
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem sl_eq {PP arLim c degMu vol J m : ℝ} (hPP : PP = c * arLim) (hc : c ≠ 0) (hvol : c * degMu = vol * J) :
    PP / (m * vol * J) = arLim / (m * degMu) := by
  rw [hPP, mul_assoc m vol J, ← hvol, show m * (c * degMu) = c * (m * degMu) by ring, mul_div_mul_left _ _ hc]

namespace ComponentData

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

def MUConjInv (D : ComponentData Ψ K ι) : Prop :=
  ∀ B : ℕ, 4 * D.f + 2 ≤ B → ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 → (D.MU B eps t').IsConjInv

end ComponentData

open ComponentData

def LowerBoundComponentConjugate.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (D : ComponentData Ψ K ι) (II : IntersectionSystem) (Ch Cu : ℝ) (B : ℕ),
    D.Clauses → IsIntersectionSystem II → D.KBound II →
    ZhangLowerX.Statement → DimX.Statement → D.CuspBundlePos → D.MUConjInv → D.HtInterior II Ch →
    D.HtBoundary II Ch → StokesLimit.Statement → D.CuspMean Cu → PushDown.Statement → GrassmannianHeightZTwo.Statement →
    1 ≤ D.jp → 3 * D.jp + 1 ≤ D.N → 4 * D.f * D.N ^ 2 ≤ B → 4 * D.f + 2 ≤ B →
    ∀ vol : ℝ, ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) * D.degMu = vol * (D.J' : ℝ) →
      -(Ch + Cu / 2) * D.f * D.jp * D.abelian₂ B ≤ D.PPB II B / (((D.n + 1 : ℕ) : ℝ) * vol * (D.J' : ℝ))

theorem LowerBoundComponentConjugate.proof (hF : FdegNeZero.Statement) : LowerBoundComponentConjugate.Statement := by
  intro Ψ _ _ K _ _ ι _ D II Ch Cu B hC hII hK hZ _hX hpos hconj hint hbd hS hmean hP _hH hj1 hj3 hB1 hB2 vol hvol

  have hyp : ∀ eps t' : ℝ, 0 < eps → eps ≤ 1 → 0 < t' → t' ≤ 1 →
      ((D.n + 1 : ℕ) : ℝ) * (-Ch * D.f * D.jp * D.abelian₂ B - eps * D.Kamp) * (D.MU B eps t').geomDeg D.P D.n ≤
        (D.MU B eps t').top II D.P (D.n + 1) := by
    intro eps t' he0 he1 ht0 ht1
    obtain ⟨h1, h2, h3⟩ := hpos B hB2 eps t' he0 he1 ht0 ht1
    refine hZ Ψ K ι D II (D.MU B eps t') _ hII h1 h2 h3 (hconj B hB2 eps t' he0 he1 ht0 ht1) ?_
    intro W hW
    by_cases hb : OnBd D.Bd W
    · exact hbd B hB1 eps t' he0 he1 ht0 ht1 W hW hb
    · exact hint B hB1 eps t' he0 he1 ht0 ht1 W hW hb
  have hlim := hS Ψ K ι D II hC hII hK B hB2 (-Ch * D.f * D.jp * D.abelian₂ B) hyp
  have hU := hmean hj1 hj3 B hB1
  obtain ⟨hPP, -, hdeg⟩ := hP Ψ K ι D II hC hII B
  have hc : ((cf D.n : ℚ) : ℝ) * (D.fdeg' : ℝ) ≠ 0 := by
    refine mul_ne_zero (by simp [cf]) ?_
    exact_mod_cast hF Ψ D.N D.j D.j_le_N
  rw [sl_eq hPP hc hvol]
  have hm : (0 : ℝ) < ((D.n + 1 : ℕ) : ℝ) * D.degMu := mul_pos (by positivity) hdeg
  rw [le_div_iff₀ hm]
  have hU' := mul_le_mul_of_nonneg_left hU hm.le
  nlinarith [hlim, hU']

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
