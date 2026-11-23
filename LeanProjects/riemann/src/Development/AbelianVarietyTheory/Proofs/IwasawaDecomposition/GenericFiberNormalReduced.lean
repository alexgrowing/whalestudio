import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLocallyNoetherianOfIsQProjOver
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFibre

theorem gen_normal_reduced_noetherian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) ∧ IsReduced (gen Y) ∧ IsLocallyNoetherian (gen Y) := by
  intro E _ _ _ H D l Xo c Y
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) :=
    GlobalTheory.AbelianLocusNormalisation.isNormalScheme_of_open (genι Y) Y.normal
  refine ⟨hn, GlobalTheory.AbelianLocusNormalisation.isReduced_of_normal hn, ?_⟩
  have hq : IsQProjOver Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    exact ⟨N, i, inferInstance, inferInstance, hs⟩
  have : IsLocallyNoetherian Y.X := GlobalTheory.ZM.isLocallyNoetherian_of_isQProjOver hq
  exact isLocallyNoetherian_of_isOpenImmersion (genι Y)

end GlobalTheory.GenFibre
