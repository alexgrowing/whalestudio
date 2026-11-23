import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
theorem nbhd_basicOpen_of_mem : ∀ (S : Type) [CommRing S] (X : Scheme.{0}) (x : Sp S ⟶ X) (V : X.Opens) (q : PrimeSpectrum S), x q ∈ V → ∃ f₀ : S, f₀ ∉ q.asIdeal ∧ ⊤ ≤ (spMap (algebraMap S (Localization.Away f₀)) ≫ x) ⁻¹ᵁ V := by
  intro S _ X x V q hq
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := q) (u := (show Set (PrimeSpectrum S) from (x ⁻¹ᵁ V).1)) hq (x ⁻¹ᵁ V).2
  refine ⟨f₀, hqf, ?_⟩
  intro y _
  show x ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away f₀)))).base y) ∈ V
  apply hsub
  show f₀ ∉ (PrimeSpectrum.comap (algebraMap S (Localization.Away f₀)) y).asIdeal
  intro h
  exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit f₀))
end GlobalTheory
