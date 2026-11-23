import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FineDataOfCone
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_data_of_cone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m N : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsCN R → P.TorsionIso → InCone P.D.toPre γ → IsFine N γ →
    FineData P.D.toPre N := by
  first | exact @GlobalTheory.TorRef.fineData_of_inCone | exact GlobalTheory.TorRef.fineData_of_inCone | (intros; apply GlobalTheory.TorRef.fineData_of_inCone <;> assumption)
