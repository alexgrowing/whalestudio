import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySabMapOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepsRegularCompatibleMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorAddStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorNsmulStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetOmIsLBOfAmpleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetOmPullbackIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupTwistedBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothGenericOfIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SncBoundaryOfIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsOfIsoStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem blowPolSt : BlowPolSt := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n k b ψ φ DX hpol hblow hb hEX hY
  obtain ⟨-, hj, hs, he, -, -, -, hamp⟩ := hblow
  obtain ⟨T₀, hT₀⟩ := hamp _ hpol.2
  have hreg := GlobalTheory.T.keepsRegular_compatible_map E H D l Xo c X Z π DX hj
  have hsab := GlobalTheory.T.nonempty_sabMap_of_compatible E H D l Xo c X Z π hj hs
  have hDZ := GlobalTheory.T.phi_divisor_pullback E H D l Xo c _ _ _ _ X Z π ψ DX hreg hj hsab hpol.1
  have hΩX := GlobalTheory.T.detOm_isLB_of_ample E H D l Xo c _ _ X k DX hpol.2
  obtain ⟨hΩZ, hiso⟩ := GlobalTheory.T.detOm_pullback_iso E H D l Xo c X Z π hsab hΩX
  obtain ⟨hsm, hsnc, htor⟩ := hY
  have hcomb : ∀ T : ℕ, comb T ψ b φ = comb 1 (comb T ψ 0 ψ) 1 (comb 0 φ b φ) := by
    intro T
    have key : ∀ f g : InvFun (𝓞 E), f.toFun = g.toFun → f = g := by
      intro f g h
      cases f
      cases g
      simp only [InvFun.mk.injEq]
      exact h
    refine key _ _ (funext fun m => funext fun B => ?_)
    simp only [comb]
    push_cast
    ring
  refine ⟨⟨b, 1, T₀, hb, one_pos, fun T hT => ⟨((DX.pull π hreg).nsmul T).add EX, ?_⟩⟩,
    GlobalTheory.T.smooth_generic_of_iso E H D l Xo c Y Z e he hsm, GlobalTheory.T.snc_boundary_of_iso E H D l Xo c Y Z e he hsnc, GlobalTheory.T.toric_charts_of_iso E H D l Xo c Y Z e he htor⟩
  rw [one_mul]
  refine ⟨?_, ?_⟩
  · rw [hcomb T]
    exact GlobalTheory.T.phi_divisor_add E H D l Xo c _ _ Z _ _ _ _ (GlobalTheory.T.phi_divisor_nsmul E H D l Xo c _ _ Z ψ _ T hDZ) hEX
  · obtain ⟨hL, hI⟩ := GlobalTheory.T.blowup_twisted_bundle_iso π (GlobalTheory.FlagMod.detOm X) (GlobalTheory.FlagMod.detOm Z) DX EX hreg k T hΩX hΩZ hiso
    exact (hT₀ T hT).of_lbIso hL hI

end GlobalTheory.TorRef
