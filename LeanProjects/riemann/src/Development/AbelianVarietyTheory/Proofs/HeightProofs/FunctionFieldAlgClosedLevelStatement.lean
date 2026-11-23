import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_alg_closed_level : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ n : ℕ, 0 < n → CurveOver (hostOfRecord D) (FO D) n → ∀ j, InR D j → ∀ (l₂ : Level Q.H) (Xo₂ : Moduli (Q.Dw j) l₂) (c₂ : Coeff l₂), l₂.A = 1 → l₂.M ∣ n → c₂.F = Q.c.F → FnAlgClosed Xo₂ c₂ := by
  first | exact @GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins | exact GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins | (intros; apply GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins <;> assumption)
