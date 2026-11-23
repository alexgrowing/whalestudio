import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundlePullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleOverFieldIrreducibleStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.FlagOverField

theorem geometricallyConnected_of_isFlagBundle : ∀ (F : Type) [Field F] (G : Scheme.{0}) (s : G ⟶ Sp F) (ι : Type) [Fintype ι] (E : ι → (Sp F).Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback s).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → IsFlagBundle s E r fl → GeometricallyConnected s := by
  intro F _ G s ι _ E r fl hE H
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have hirr : IrreducibleSpace ↥(Limits.pullback s y) :=
    GlobalTheory.T.flag_bundle_over_field_irreducible K _ (Limits.pullback.snd s y) ι _ r _ (fun a => (hE a).pullback y)
      (GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag _ _ _ s y ι E r fl H)
  have hc : ConnectedSpace ↥(Limits.pullback s y) := inferInstance
  exact h.isoPullback.hom.homeomorph.connectedSpace_iff.mpr hc

end GlobalTheory.FlagOverField
