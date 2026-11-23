import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEmbeddingProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_embedding_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp O) (t : SAB H X), IsProjOver s → ∃ (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd := by
  first | exact @GlobalTheory.LieEmb.exists_isLieEmb | exact GlobalTheory.LieEmb.exists_isLieEmb | (intros; apply GlobalTheory.LieEmb.exists_isLieEmb <;> assumption)
