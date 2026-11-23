import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdealEqTopDimZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_ideal_eq_top_dim_zero : ∀ {X Y' Y : Scheme.{0}} (ρ : Y' ⟶ X) (ι : Y' ⟶ Y) [Flat ι] (D : EffCartierData Y) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X), (Scheme.stalkClosedPointTo ξ).hom.Flat → ∀ v : ↥(pullback ξ ρ : Scheme.{0}), ringKrullDim ((pullback ξ ρ).presheaf.stalk v) = 0 → FinalTheorems.stalkId (((D.idealSheaf ^ n).comap ι).comap (pullback.snd ξ ρ)) v = ⊤ := by
  first | exact @GlobalTheory.GenFibre.stalkId_eq_top_of_dim_zero | exact GlobalTheory.GenFibre.stalkId_eq_top_of_dim_zero | (intros; apply GlobalTheory.GenFibre.stalkId_eq_top_of_dim_zero <;> assumption)
