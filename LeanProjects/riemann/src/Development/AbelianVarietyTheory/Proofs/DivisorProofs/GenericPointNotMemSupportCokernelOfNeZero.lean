import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.VB

theorem genericPoint_notMem_support_cokernel_of_ne_zero :
    ∀ (X : Scheme.{0}) [IsIntegral X] (E L : X.Modules) (φ : E ⟶ L), IsVB L 1 → φ ≠ 0 → genericPoint X ∉ GlobalTheory.QCoh.support (Limits.cokernel φ) := by
  intro X _ E L φ hL h0
  have hex : ∃ (V : X.Opens) (s : Γ(E, V)), φ.app V s ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h0
    ext V s
    exact (hc V s).trans rfl
  obtain ⟨V, s, hs⟩ := hex
  have hV : genericPoint X ∈ V := by
    by_contra hη
    refine hs (QCoh.section_eq_zero_of_germ _ fun x hx => ?_)
    exact absurd (VB.genericPoint_mem hx) hη
  have hg : L.presheaf.germ V _ hV (φ.app V s) ≠ 0 := fun h => hs (hL.isTorsionFree V hV _ h)
  have hr : Module.finrank X.functionField (genStalk L) = 1 := hL.genRank_eq
  have hsurj : Function.Surjective (QCoh.stalkLinear φ (genericPoint X)) := by
    intro w
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hg).1 hr w
    refine ⟨c • E.presheaf.germ V _ hV s, ?_⟩
    rw [map_smul, QCoh.stalkLinear_germ]
    exact hc
  have hexact := (QCoh.exact_iff_stalkLinear _).1 (ShortComplex.exact_cokernel φ) (genericPoint X)
  refine QCoh.notMem_support_iff.2 ⟨fun a b => ?_⟩
  have key : ∀ y, y = (0 : ((Limits.cokernel φ).presheaf.stalk (genericPoint X) :)) := by
    intro y
    obtain ⟨t, rfl⟩ := QCoh.stalkLinear_surjective (Limits.cokernel.π φ) (genericPoint X) y
    obtain ⟨u, rfl⟩ := hsurj t
    exact (hexact _).2 ⟨u, rfl⟩
  rw [key a, key b]

end GlobalTheory.VB
