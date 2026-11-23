import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.MixedLocalChains

theorem Pres.kills_pull (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O)
    (f : GlobalTheory.Vert.Model.Hom B' B) (P : Pres B) (g : Γ(B.X, ⊤)) :
    Kills g P.mod → Kills (f.f.appTop g) (P.pull f).mod := by
  intro h
  unfold Kills at h ⊢
  have h1 : smulHom ((Scheme.Modules.pullback f.f).obj P.mod) (f.f.appTop g) = 0 := by
    rw [← GlobalTheory.VB.pullback_map_smulHom, h, Functor.map_zero]
  have h2 : smulHom (P.pull f).mod (f.f.appTop g) =
      (P.pullModIso f).hom ≫ smulHom _ (f.f.appTop g) ≫ (P.pullModIso f).inv := by
    rw [← smulHom_comp_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h2, h1, zero_comp, comp_zero]

end GlobalTheory.MixedLocalChains
