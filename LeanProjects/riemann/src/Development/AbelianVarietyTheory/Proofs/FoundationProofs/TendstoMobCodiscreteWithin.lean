import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem isOpen_Hs_mobt : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem tendsto_mob_codiscreteWithin :
    ∀ g : GQ, Filter.Tendsto (mob g) (Filter.codiscreteWithin Hs) (Filter.codiscreteWithin Hs) := by
  intro g
  obtain ⟨hmaps, hmul, hone, -, hdiff, -⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  have hinj : ∀ x y : ℂ, x ∈ Hs → y ∈ Hs → mob g x = mob g y → x = y := by
    intro x y hx hy hxy
    have ex : mob (g⁻¹ * g) x = x := by rw [inv_mul_cancel, hone]
    have ey : mob (g⁻¹ * g) y = y := by rw [inv_mul_cancel, hone]
    rw [← ex, ← ey, hmul _ _ _ hx, hmul _ _ _ hy, hxy]
  intro S hS
  rw [Filter.mem_map, mem_codiscreteWithin]
  rw [mem_codiscreteWithin] at hS
  intro z hz
  have hw := hS (mob g z) (hmaps g z hz)
  have hHs : Hs ∈ nhds z := isOpen_Hs_mobt.mem_nhds hz
  have hcont : ContinuousAt (mob g) z := (hdiff g).continuousOn.continuousAt hHs
  have htend : Filter.Tendsto (mob g) (nhdsWithin z {z}ᶜ) (nhdsWithin (mob g z) {mob g z}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hHs, self_mem_nhdsWithin] with x hx hxz
    exact fun h => hxz (hinj x z hx hz h)
  rw [Filter.disjoint_principal_right] at hw ⊢
  filter_upwards [htend hw, nhdsWithin_le_nhds hHs] with x hx hxH
  rintro ⟨hx1, hx2⟩
  exact hx ⟨hmaps g x hx1, hx2⟩

end GlobalTheory.FN
