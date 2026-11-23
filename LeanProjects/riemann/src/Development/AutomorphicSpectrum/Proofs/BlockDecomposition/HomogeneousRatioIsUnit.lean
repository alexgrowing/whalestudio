import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.ConeUnit

theorem yQ_appLE_isUnit {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m)
    (W : X.Opens) (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k') :
    IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := by
  have ha : y k' ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')
  have hb : y k ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have ha1 : y k' ∈ grK K N (1 • e) := by simpa using ha
  have hb1 : y k ∈ grK K N (1 • e) := by simpa using hb
  have hVx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k' * y k) := by
    rw [Proj.basicOpen_mul]
    exact le_inf h2 h1
  have e1 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))
    (Proj.awayMap_awayToSection (grK K N) hb (x := y k' * y k) rfl)
  have e2 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1))
    (Proj.awayMap_awayToSection (grK K N) ha (x := y k' * y k) (mul_comm _ _))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  have e3 : (i.appLE _ W h2).hom (yQ y hy k k') = (i.appLE _ W hVx).hom
      ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) hb (x := y k' * y k) rfl
          (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))) := by
    rw [e1, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  refine IsUnit.of_mul_eq_one ((i.appLE _ W hVx).hom ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) ha (x := y k' * y k) (mul_comm _ _)
          (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1)))) ?_
  rw [e3, ← map_mul, ← map_mul, GlobalTheory.CompanionTheory.GeoUnit.awayMap_ratio_mul ha hb hb1 ha1, map_one, map_one]

end GlobalTheory.CompanionTheory.ConeUnit
