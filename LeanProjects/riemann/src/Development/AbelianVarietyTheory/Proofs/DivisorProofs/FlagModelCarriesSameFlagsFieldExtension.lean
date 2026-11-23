import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

attribute [local instance] Over.cartesianMonoidalCategory

theorem rel_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C (spMap ι ≫ z) (spMap ι ≫ p) := by
  intro E _ _ _ H Dw l Xo c Y X hFE C K K' _ _ ι z p hR
  obtain ⟨φ, k, hz, g, hs, hg, y, ψ, φ₁, f, t, t', hp, hf0, hx, hφ, hcomb⟩ := hR
  have hz' : ⊤ ≤ (spMap ι ≫ z) ⁻¹ᵁ X.F.U k := fun w _ => by
    exact hz (show spMap ι w ∈ (⊤ : (Sp K).Opens) from trivial)
  have hs' : (spMap ι ≫ z) ≫ X.π ≫ Y.s = spMap (ι.comp φ) := by
    rw [Category.assoc, hs, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  obtain ⟨g', hg'⟩ := hFE K' (ι.comp φ) (spMap ι ≫ z) k hz' hs'
  have e : spMap ι ≫ (z ≫ X.π) = (spMap ι ≫ z) ≫ X.π := (Category.assoc _ _ _).symm
  have hv : ∀ τ i, g'.v τ i = spMap (dualMap ι) ≫ g.v τ i := fun τ i => by
    have h1 : g'.v τ i = (tv (GlobalTheory.FlagMod.tanPull ι e (X.F.vecAt k z hz rfl τ i))).left := by
      rw [hg' τ i, X.F.tanPull_vecAt k ι z hz hz' rfl rfl e]
    rw [h1, hg τ i]
    rfl
  refine ⟨ι.comp φ, k, hz', g', hs', hg', y, ι.comp ψ, φ₁, f, t, fun τ i => Units.map ι.toMonoidHom (t' τ i), ?_, hf0,
    ?_, ?_, fun τ i => ?_⟩
  · rw [hp, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  · rw [Category.assoc, hx, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  · rw [hφ]; rfl
  · obtain ⟨cf, h1, h2, h3⟩ := hcomb τ i
    refine ⟨fun j => ι (cf j), by simp [h1], fun j hj => by simp [h2 j hj], ?_⟩
    have h4 := GlobalTheory.LatDRFree.comb_map Y.t ι h3
    have hd : ∀ j, spMap (dualMap ι) ≫ spMap (dualMap ψ) ≫ f.v τ j = spMap (dualMap (ι.comp ψ)) ≫ f.v τ j := fun j => by
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
      congr 2
      exact RingHom.ext fun a => by ext <;> simp [dualMap]
    simp only [hd] at h4
    rw [hv, ← e]
    exact h4

end GlobalTheory.VarFlag
