import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionOfProp25
import Formalism.GL3MeanSquares.HookFormulaTorsion.BoxCountAllStatement
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.MeanSquareOfPrimeNumberTheorem
import Formalism.GL3MeanSquares.HookFormulaTorsion.MeanSquareWeakOfPrimeNumberTheorem

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.MergeGL2b

open Formalism.LFunctionChainParameters Formalism.HermitianLattices Formalism.L2.GlobalTheoryTheory.MergeGL2

def AnalyticEndFinal : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₄ →
    WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
      ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x)

def AnalyticConclusionCompatible : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₄ →
    WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d

def Chain6AtFinal : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε C₄ x₄ : ℝ, 0 < ε → ε < 1 / 4 → 0 < A → 0 < C₄ →
    WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

def AnalyticEndPNT : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ (PrimeNumberTheoremConsequences.PNTAPRelW → ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
      ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x))

def AnalyticPrimeNumberTheoremCompatible : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ (PrimeNumberTheoremConsequences.PNTAPRelW → ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d)

def Chain6AtPNT : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ (PrimeNumberTheoremConsequences.PNTAPRelW → ∀ eD eL A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)))

theorem boxCount_pos : ∃ C : ℝ, 0 < C ∧ ZeroFreeRegionGL2.BoxCountHyp C := by
  obtain ⟨C, hC⟩ := BoxCountUnconditional.boxCountAll_statement
  exact ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), boxCount_mono (le_max_left _ _) hC⟩

theorem boxCountAll_iff : BoxCountUnconditional.BoxCountAll ↔ ∃ C : ℝ, ZeroFreeRegionGL2.BoxCountHyp C := Iff.rfl

theorem zeroDensityBox : ZeroDensityInBoxes.ZeroDensityBox := Ext.PrimitiveCharacterCasts.ZD.zero_density_box

theorem analyticEndFinal : AnalyticEndFinal := by
  obtain ⟨c', hc', h⟩ := analyticEndSel
  refine ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hM => ?_⟩
  obtain ⟨C₂, hC₂, h1⟩ := boxCount_pos
  obtain ⟨x₂, h2⟩ := boxTail_CVal0 ε hε hε1
  exact h ε A C₂ CVal0 x₂ C₄ x₄ hε hε1 hA hC₂ hC₄ h1 h2 hM

theorem analyticEndFinalTied : AnalyticConclusionCompatible := by
  obtain ⟨c', hc', h⟩ := analyticEndTied
  refine ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hM => ?_⟩
  obtain ⟨C₂, hC₂, h1⟩ := boxCount_pos
  obtain ⟨x₂, h2⟩ := boxTail_CVal0 ε hε hε1
  exact h ε A C₂ CVal0 x₂ C₄ x₄ hε hε1 hA hC₂ hC₄ h1 h2 hM

theorem chain6AtFinal : Chain6AtFinal := by
  obtain ⟨Cord, hC, h⟩ := chain6At
  obtain ⟨c', _, hE⟩ := analyticEndFinal
  refine ⟨Cord, hC, fun eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ hM => ?_⟩
  obtain ⟨xa, hxa⟩ := h eD eL A K cHH eK CVal0 eW KW ε hε hε4 hA
  obtain ⟨xb, hxb⟩ := hE ε A C₄ x₄ hε (by linarith) hA hC₄ hM
  refine ⟨max xa xb, fun x hx => ?_⟩
  obtain ⟨_, iq, id, hEnd⟩ := hxb x (le_trans (le_max_right _ _) hx)
  exact ⟨iq, id, fun hc => hxa x (le_trans (le_max_left _ _) hx)
    (core_of_coreAt _ _ A Cord eD eL K cHH eK CVal0 eW KW ε x hEnd.1 hc)⟩

theorem analyticEndPNT : AnalyticEndPNT := by
  obtain ⟨c', hc', h⟩ := analyticEndFinal
  refine ⟨c', hc', fun hP ε A hε hε1 hA => ?_⟩
  obtain ⟨C₄, x₄, hC₄, hM⟩ := WeakMeanSquareEstimates.mean_square_weak_of_prime_number_theorem hP ε hε hε1
  exact h ε A C₄ x₄ hε hε1 hA hC₄ hM

theorem analyticEndPNTTied : AnalyticPrimeNumberTheoremCompatible := by
  obtain ⟨c', hc', h⟩ := analyticEndFinalTied
  refine ⟨c', hc', fun hP ε A hε hε1 hA => ?_⟩
  obtain ⟨C₄, x₄, hC₄, hM⟩ := WeakMeanSquareEstimates.mean_square_weak_of_prime_number_theorem hP ε hε hε1
  exact h ε A C₄ x₄ hε hε1 hA hC₄ hM

theorem chain6AtPNT : Chain6AtPNT := by
  obtain ⟨Cord, hC, h⟩ := chain6AtFinal
  refine ⟨Cord, hC, fun hP eD eL A K cHH eK eW KW ε hε hε4 hA => ?_⟩
  obtain ⟨C₄, x₄, hC₄, hM⟩ := WeakMeanSquareEstimates.mean_square_weak_of_prime_number_theorem hP ε hε (by linarith)
  exact h eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ hM

theorem final_iff_closed : AnalyticEndFinal ↔ AnalyticEndClosed :=
  ⟨fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ _ hM => h ε A C₄ x₄ hε hε1 hA hC₄ hM⟩,
   fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hM => h ε A C₄ x₄ hε hε1 hA hC₄ zeroDensityBox hM⟩⟩

theorem finalTied_iff_closedTied : AnalyticConclusionCompatible ↔ AnalyticEndClosedTied :=
  ⟨fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ _ hM => h ε A C₄ x₄ hε hε1 hA hC₄ hM⟩,
   fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hM => h ε A C₄ x₄ hε hε1 hA hC₄ zeroDensityBox hM⟩⟩

theorem chain6AtFinal_iff_closed : Chain6AtFinal ↔ Chain6AtClosed :=
  ⟨fun ⟨Cord, hC, h⟩ => ⟨Cord, hC, fun eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ _ hM =>
      h eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ hM⟩,
   fun ⟨Cord, hC, h⟩ => ⟨Cord, hC, fun eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ hM =>
      h eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ zeroDensityBox hM⟩⟩

example : AnalyticEndFinal := final_iff_closed.2 analyticEndClosed
example : AnalyticConclusionCompatible := finalTied_iff_closedTied.2 analyticEndClosedTied
example : Chain6AtFinal := chain6AtFinal_iff_closed.2 chain6AtClosed

theorem analytic_conclusion_mean_square :
    ∃ c' : ℝ, 0 < c' ∧ ∀ ε A x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → WeakMeanSquareEstimates.MeanSquareHypW ε 36 x₄ →
      ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
        ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x) := by
  obtain ⟨c', hc', h⟩ := analyticEndFinal
  exact ⟨c', hc', fun ε A x₄ hε hε1 hA hM => h ε A 36 x₄ hε hε1 hA (by norm_num) hM⟩

theorem analytic_conclusion_compatible_mean_square :
    ∃ c' : ℝ, 0 < c' ∧ ∀ ε A x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → WeakMeanSquareEstimates.MeanSquareHypW ε 36 x₄ →
      ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
        ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d := by
  obtain ⟨c', hc', h⟩ := analyticEndFinalTied
  exact ⟨c', hc', fun ε A x₄ hε hε1 hA hM => h ε A 36 x₄ hε hε1 hA (by norm_num) hM⟩

theorem prime_gap_chain_mean_square :
    ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε x₄ : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
      WeakMeanSquareEstimates.MeanSquareHypW ε 36 x₄ →
      ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
        (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
          Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)) := by
  obtain ⟨Cord, hC, h⟩ := chain6AtFinal
  exact ⟨Cord, hC, fun eD eL A K cHH eK eW KW ε x₄ hε hε4 hA hM =>
    h eD eL A K cHH eK eW KW ε 36 x₄ hε hε4 hA (by norm_num) hM⟩

end Formalism.L2.GlobalTheoryTheory.MergeGL2b
