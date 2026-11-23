import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueEffectiveCartier
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_effective_cartier : ∀ {X : Scheme.{0}} {I : Type} {Y : I → Scheme.{0}} (u : ∀ i, Y i ⟶ X) (J : ∀ i, EffCartierData (Y i)), (∀ i, IsOpenImmersion (u i)) → (∀ x : X, ∃ i, x ∈ Set.range (u i)) → (∀ i j, (J i).idealSheaf.comap (pullback.fst (u i) (u j)) = (J j).idealSheaf.comap (pullback.snd (u i) (u j))) → ∃ D : EffCartierData X, ∀ i, D.idealSheaf.comap (u i) = (J i).idealSheaf := by
  first | exact @GlobalTheory.CartierGlue.exists_glue | exact GlobalTheory.CartierGlue.exists_glue | (intros; apply GlobalTheory.CartierGlue.exists_glue <;> assumption)
