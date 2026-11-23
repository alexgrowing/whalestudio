import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealOfFlatStalkPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_ideal_of_flat_stalk_pullback : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] [QuasiSeparated ρ] (I : Y'.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X), (Scheme.stalkClosedPointTo ξ).hom.Flat → ∀ h : R, (∀ v : ↥(pullback ξ ρ : Scheme.{0}), ((pullback ξ ρ).presheaf.germ ⊤ v trivial).hom ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h)) ∈ FinalTheorems.stalkId (I.comap (pullback.snd ξ ρ)) v) → h ∈ idlAlong (I.map ρ) ξ := by
  first | exact @GlobalTheory.FlatPush.mem_idlAlong_map_of_flat | exact GlobalTheory.FlatPush.mem_idlAlong_map_of_flat | (intros; apply GlobalTheory.FlatPush.mem_idlAlong_map_of_flat <;> assumption)
