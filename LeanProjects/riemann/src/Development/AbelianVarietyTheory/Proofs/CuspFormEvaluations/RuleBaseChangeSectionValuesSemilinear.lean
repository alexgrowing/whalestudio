import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.FieldBC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (ValueWD HasBC hasBC_of ruleUp_mem_sec evR_ruleUp)

theorem rulBC_sec_val_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, rulBC hle f ∈ sec Xo c' a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S), evR Xo c' (rulBC hle f) y = evR Xo c f (y.res hle h)) ∧ (∀ (t : c.F) (f g : Rul Xo c), rulBC hle (t • f + g) = incF c c' hle t • rulBC hle f + rulBC hle g) := by
  intro E _ _ _ H Dw l Xo c c' hle
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hBC : HasBC Xo c := hasBC_of hS
  refine ⟨fun a n f hf => ⟨ruleUp_mem_sec hle hWD hBC hf, ?_⟩, fun t f g => ?_⟩
  · intro S _ A _ h y
    obtain rfl : A = resAlg hle S := Algebra.algebra_ext _ _ fun x => (h x).symm
    exact evR_ruleUp hle hWD hBC hf.1 y
  · funext p y
    letI := resAlg hle p.R
    have h1 : evR Xo c (t • f + g) (y.res hle (fun _ => rfl)) =
        algebraMap c.F p.R t * evR Xo c f (y.res hle (fun _ => rfl)) + evR Xo c g (y.res hle (fun _ => rfl)) := by
      unfold evR
      rw [evalAt_add, evalAt_smul]
    refine h1.trans ?_
    show _ = incF c c' hle t • rulBC hle f p y + rulBC hle g p y
    rw [Algebra.smul_def]
    rfl

end GlobalTheory.FieldBC
