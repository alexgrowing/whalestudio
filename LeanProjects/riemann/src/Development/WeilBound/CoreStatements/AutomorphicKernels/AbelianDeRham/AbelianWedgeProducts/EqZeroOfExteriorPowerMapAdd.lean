import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianSchemeCharts.GrpPull
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianPullbackLattices.GeoSys
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.ThetaMulti
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.PairInj
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.PullbackWedgeCupSquare
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.POOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

theorem eq_zero_of_exteriorPower_map_add {K : Type} [CommRing K] (hK : IsField K) {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V) (h11 : r₁ ∘ₗ p = LinearMap.id)
    (h12 : r₁ ∘ₗ q = 0) (h21 : r₂ ∘ₗ p = 0) (h22 : r₂ ∘ₗ q = LinearMap.id) (t : ⋀[K]^2 V)
    (ht : exteriorPower.map 2 (p + q) t = exteriorPower.map 2 p t + exteriorPower.map 2 q t) : t = 0 := by
  letI := hK.toField
  exact key_alg p q r₁ r₂ h11 h12 h21 h22 t ht

end MainStatements.Hodge.Pf.WedgeProjections

theorem MainStatements.Hodge.Pf.noprim : DescentSt → LowSt → SteinSt → AxOSt → WedgeFieldSt → NoPrimSt := by
  intro hD hL _ hAx hW R _ A _ g hA hg hR z a b c ha hb hc habc
  obtain ⟨eZ, hZ⟩ := hW R A g hA hg hR
  obtain ⟨eY, hY⟩ := hW R (A ⊗ A) (g + g) (MainStatements.Hodge.Sh.isAbelianScheme_tensor' A A hA hA)
    (MainStatements.Hodge.Sh.smooth_tensor hg hg) hR
  have hsep : IsSeparated A.hom := by have := hA.proper; infer_instance
  have hsep2 : IsSeparated (A ⊗ A).hom := MainStatements.Hodge.Pf.AXO.sep_tensor A
  have inj : ∀ f : A ⊗ A ⟶ A, Function.Injective (pairRes f.left (A ⊗ A).hom).pull2 := fun f ↦
    MainStatements.Hodge.Pf.WedgeProjections.pairRes_pull2_injective hD hL A.hom (A ⊗ A).hom f.left hsep hsep2
  obtain ⟨t, rfl⟩ := eZ.surjective z
  have e : ∀ (f : A ⊗ A ⟶ A) (a' : GlobalTheory.CatCoh.H2 (OAff (A ⊗ A).hom)), IsPullbackH2Structure (wOver f) (eZ t) a' →
      a' = eY (exteriorPower.map 2 (MainStatements.Hodge.Pf.AXO.pO f) t) := fun f a' h' ↦
    inj f (h'.symm.trans (MainStatements.Hodge.Pf.WedgeProjections.pullback_wedge_cup_square f eZ hZ eY hY t))
  rw [e _ _ ha, e _ _ hb, e _ _ hc, ← map_add] at habc
  have ht := eY.injective habc
  rw [MainStatements.Hodge.Pf.WedgeProjections.pO_mul A hAx g hA hg] at ht
  rw [MainStatements.Hodge.Pf.WedgeProjections.eq_zero_of_exteriorPower_map_add hR _ _ _ _ (MainStatements.Hodge.Pf.WedgeProjections.r11 A) (MainStatements.Hodge.Pf.WedgeProjections.r12 A)
    (MainStatements.Hodge.Pf.WedgeProjections.r21 A) (MainStatements.Hodge.Pf.WedgeProjections.r22 A) t ht, map_zero]
