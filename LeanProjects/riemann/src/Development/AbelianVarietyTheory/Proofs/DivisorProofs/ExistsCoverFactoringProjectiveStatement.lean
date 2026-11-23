import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverFactoringProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_factoring_projective : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (Z : Scheme.{0}) (s : Z ⟶ Sp (𝓞 F)) (h : V.G ⟶ Z), IsProjOver s → h ≫ s = V.j ≫ V.p → ∃ (V' : Cover Y) (ν : V'.X ⟶ Z) (g : V'.G ⟶ V.G), ν ≫ s = V'.p ∧ V'.j ≫ ν = g ≫ h ∧ g ≫ V.π = V'.π := by
  first | exact @GlobalTheory.LatChain.ProjDom.exists_cover_dominating_proj | exact GlobalTheory.LatChain.ProjDom.exists_cover_dominating_proj | (intros; apply GlobalTheory.LatChain.ProjDom.exists_cover_dominating_proj <;> assumption)
