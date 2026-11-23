import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReps
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.TraitLattice

theorem nontrivial_of_closed_not_mem_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (y : Sp T.V ⟶ Y.X) (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), y (closedPoint T.V) ∉ abLocus Y.t.G → Nontrivial P.D.toPre.X := by
  intro E _ _ _ H D l Xo c O _ β Y T y t m P hy
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have hab := GlobalTheory.isAbelianScheme_of_unif_of_subsingleton GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 T.V T.cpl
    P.D P.A t.G t.semi P.U hn
  exact hy (GlobalTheory.ModelSum.range_subset_abLocus m hab.proper ⟨closedPoint T.V, rfl⟩)

end GlobalTheory.TraitLattice
