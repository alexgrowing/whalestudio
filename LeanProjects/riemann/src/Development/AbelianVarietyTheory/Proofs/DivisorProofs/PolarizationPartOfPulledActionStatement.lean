import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationPartOfPulledAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_part_of_pulled_action : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (B : ℝ) (q : ℕ) [Fact q.Prime], q ∉ FlagAr.setB O.Y B →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharP Ω q] (x : Sp Ω ⟶ O.s.T.Z.X) (G : Over (Sp Ω)) [GrpObj G]
    (i : OAct (𝓞 D.host.E) G) (φ : G.left ⟶ O.s.T.Z.t.G.left), IsActPull i O.s.T.Z.t.act x φ →
    PolPart (O.A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) i := by
  first | exact @GlobalTheory.PolPoint.polPart_at_point | exact GlobalTheory.PolPoint.polPart_at_point | (intros; apply GlobalTheory.PolPoint.polPart_at_point <;> assumption)
