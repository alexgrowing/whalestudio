import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RefSum

open AlgebraicGeometry CategoryTheory

theorem intFr_res_down : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (c' : Coeff l) (hle : c.F ≤ c'.F) (T : CDVR) (io' : c'.F →+* T.Fr) (y' : IntFr Xo c' T io'), y'.IsAlg → ∃ y : IntFr Xo c T (io'.comp (IntermediateField.inclusion hle).toRingHom), y.IsAlg ∧ (∀ φ : ℝ, HasPhi y' φ → HasPhi y φ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, evI y' (GlobalTheory.FieldBC.rulBC hle f) = evI y f := by
  intro E _ _ _ H Dw l Xo c c' hle T io' y' hy
  obtain ⟨pt, rest⟩ := y'
  letI : Algebra c'.F T.Fr := io'.toAlgebra
  letI : Algebra c.F T.Fr := (io'.comp (IntermediateField.inclusion hle).toRingHom).toAlgebra
  have hover : AlgOver c c' hle T.Fr := fun _ => rfl
  refine ⟨⟨pt.res hle hover, GlobalTheory.FlagTan.fromTest_of_isLocalRing _, rest.2⟩, hy, fun φ hφ => hφ, ?_⟩
  intro a n f hf
  exact ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2 T.Fr hover pt

end GlobalTheory.RefSum
