import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem eq_top_of_special_part : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y : Over (Spec (CommRingCat.of R))) [UniversallyClosed Y.hom] (U : Y.left.Opens), (∀ z : (thickObj R I 0 Y).left, pullback.fst Y.hom (thick R I 0) z ∈ U) → U = ⊤ := by
  intro R _ I hI Y _ U hU
  by_contra hne
  have hcl : IsClosed (Y.hom '' ((U : Set Y.left)ᶜ)) :=
    Y.hom.isClosedMap _ U.isOpen.isClosed_compl
  have hne' : ((U : Set Y.left)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    exact hne (TopologicalSpace.Opens.ext h)
  obtain ⟨y, hy⟩ := hne'
  let p : PrimeSpectrum R := Y.hom y
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let q : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hspec : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 hpm
  have hq : q ∈ Y.hom '' ((U : Set Y.left)ᶜ) :=
    hspec.mem_closed hcl ⟨y, hy, rfl⟩
  obtain ⟨y', hy', hyq⟩ := hq
  have hr : q ∈ Set.range (thick R I 0) := by
    have h1 : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        PrimeSpectrum.mem_zeroLocus]
      intro x hx
      have hx' : x ∈ I := by simpa using hx
      exact (Ideal.mem_sInf.1 (hI hx')) ⟨bot_le, hm⟩
    exact h1
  have h2 : y' ∈ Set.range (pullback.fst Y.hom (thick R I 0)) := by
    rw [Scheme.Pullback.range_fst]
    show Y.hom y' ∈ Set.range (thick R I 0)
    rw [hyq]; exact hr
  obtain ⟨z, rfl⟩ := h2
  exact hy' (hU z)

end GlobalTheory.Unif
