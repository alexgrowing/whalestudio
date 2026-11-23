import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfLocalAffineCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_of_local_affine_cover : ∀ {X : Scheme.{0}} {O : Type} [CommRing O] {I : Type} [Finite I] {Y : I → Scheme.{0}} (s : X ⟶ Sp O) (u : ∀ i, Y i ⟶ X) (a : I → O) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X), CompactSpace X → QuasiSeparatedSpace X → Ideal.span (Set.range a) = ⊤ → (∀ i, IsOpenImmersion (u i)) → (∀ i, Set.range (u i) = s ⁻¹' {x : Sp O | a i ∉ x.asIdeal}) → (∀ i, GlobalTheory.IsAmpleLB (L.pull (u i))) → GlobalTheory.IsAmpleLB L := by
  first | exact @GlobalTheory.AmpleOverBase.isAmpleLB_of_basicOpen_cover | exact GlobalTheory.AmpleOverBase.isAmpleLB_of_basicOpen_cover | (intros; apply GlobalTheory.AmpleOverBase.isAmpleLB_of_basicOpen_cover <;> assumption)
