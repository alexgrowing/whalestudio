import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizationSectionExpansionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineSectionFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpansionIndependentSectionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpansionConstantTermIndependentStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

theorem freeClosedSt : FreeClosedSt := by
  intro E _ _ _ H R _ _ _ t P N hR hN hF
  obtain ⟨n, Φ, f, hfΦ, hli, hsp, hcl⟩ := GlobalTheory.T.exists_fine_section_families R hR P.D P.A t.G t.semi P.U N hN hF
  choose σ hσ using fun i => GlobalTheory.T.uniformization_section_expansion R hR P.D P.A t.G t.semi P.U N hN (Φ i) (f i) (hfΦ i)
  have hb := GlobalTheory.T.expansion_independent_sections R hR P.D P.A t.G t.semi P.U N hN n σ Φ f (fun i e => hσ i e) hfΦ hli hsp
  have hi := GlobalTheory.T.expansion_constant_term_independent R hR P.D P.A t.G t.semi P.U N hN n σ f (fun i => hσ i 0) hcl
  rw [← P.bundle]
  exact ⟨n, fun i => upSec t.G (σ i), hb, hi⟩

end GlobalTheory.TorRef
