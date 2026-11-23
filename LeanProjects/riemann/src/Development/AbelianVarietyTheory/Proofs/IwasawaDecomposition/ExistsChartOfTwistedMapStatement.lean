import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartOfTwistedMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_of_twisted_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H)
    (Xo : Moduli D l) (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (Z : GMod Xo c) (Z' : GMod Xo' c')
    (σ : 𝓞 E ≃+* 𝓞 E) (π : Z'.X ⟶ Z.X) (mu : TwMap σ Z'.t Z.t π), σ H.w0 = H.w0 →
    ∀ (M : GlobalTheory.Reg.MChart Z) (x : Z'.X), π x ∈ M.U → ∃ M' : GlobalTheory.Reg.MChart Z', x ∈ M'.U := by
  first | exact @GlobalTheory.ChartPull.exists_chart_of_pull | exact GlobalTheory.ChartPull.exists_chart_of_pull | (intros; apply GlobalTheory.ChartPull.exists_chart_of_pull <;> assumption)
