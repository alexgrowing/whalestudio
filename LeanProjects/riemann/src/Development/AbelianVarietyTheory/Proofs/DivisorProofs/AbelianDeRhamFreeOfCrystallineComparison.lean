import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamComparisonBijectiveCupSmooth

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof.AbelianDeRhamFreeOfHodge

def extSqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])

theorem extSqEquiv_ιMulti {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) (a b : M) :
    extSqEquiv E (exteriorPower.ιMulti R 2 ![a, b]) = exteriorPower.ιMulti R 2 ![E a, E b] := by
  change exteriorPower.map 2 (E : M →ₗ[R] N) _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem free_of (hC : GlobalTheory.Published.CrystallineSmoothLift) (hA : GlobalTheory.Published.AbelianHodgeDeRham)
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (s : A.left ⟶ Sp R) (hs : s = A.hom) :
    Module.Finite R (FirstDeRham s) ∧ Module.Projective R (FirstDeRham s) ∧
    (∀ p : PrimeSpectrum R, Module.rankAtStalk (FirstDeRham s) p = 2 * g) ∧
    ∃ e : ⋀[R]^2 (FirstDeRham s) ≃ₗ[R] SecondDeRham s,
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cup _ a b := by
  subst hs
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  obtain ⟨⟨hfin, hproj, hrank⟩, ⟨eH, heH⟩, -⟩ := hA R A g hab hg
  obtain ⟨hbij, e2, he2⟩ := GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left A.hom inferInstance inferInstance inferInstance
  let E1 : FirstDeRham A.hom ≃ₗ[R] HH1 A.hom := LinearEquiv.ofBijective (cmp1 A.hom) hbij
  refine ⟨Module.Finite.equiv E1.symm, Module.Projective.of_equiv E1.symm, ?_, ?_⟩
  · intro p
    rw [Module.rankAtStalk_eq_of_equiv E1]
    exact hrank p
  · refine ⟨(extSqEquiv E1).trans (eH.trans e2.symm), fun a b => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, extSqEquiv_ιMulti, heH, LinearEquiv.symm_apply_eq]
    exact (he2 a b).symm

end GlobalTheory.Proof.AbelianDeRhamFreeOfHodge

open GlobalTheory.Proof.AbelianDeRhamFreeOfHodge in

theorem GlobalTheory.Proof.abelianDeRhamFree_of_hodge :
    GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  intro hC hA R _ A _ g hab hg
  exact free_of hC hA R A g hab hg _ (Category.comp_id _)
