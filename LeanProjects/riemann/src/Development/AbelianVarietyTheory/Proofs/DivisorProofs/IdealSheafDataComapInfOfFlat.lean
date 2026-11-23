import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FlatInf
open TensorProduct

theorem map_eq_baseChange {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (K : Ideal R) :
    Ideal.map (algebraMap R S) K =
      (K.baseChange S).map ((Algebra.TensorProduct.rid R S S).toLinearEquiv : S ⊗[R] R →ₗ[S] S) := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Ideal.map]
  congr 1
  ext y
  simp [Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

theorem map_inf_of_flat {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat)
    (I J : Ideal R) : Ideal.map f (I ⊓ J) = Ideal.map f I ⊓ Ideal.map f J := by
  letI := f.toAlgebra
  haveI : Module.Flat R S := hf
  have e : f = algebraMap R S := rfl
  rw [e, map_eq_baseChange, map_eq_baseChange, map_eq_baseChange, GlobalTheory.baseChange_inf,
    Submodule.map_inf _ (Algebra.TensorProduct.rid R S S).toLinearEquiv.injective]

end GlobalTheory.FlatInf

namespace GlobalTheory.FlatInf

theorem comap_inf_of_flat : ∀ (W V : Scheme.{0}) (g : V ⟶ W), Flat g →
    ∀ a b : W.IdealSheafData, (a ⊓ b).comap g = a.comap g ⊓ b.comap g := by
  intro W V g hg a b
  haveI := hg
  have hU : ∀ y : V, ∃ U : W.affineOpens, g y ∈ U.1 := fun y => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show g y ∈ ((⊤ : W.Opens) : Set W) from trivial) (⊤ : W.Opens).isOpen
    exact ⟨⟨U, hU⟩, hyU⟩
  choose U hyU using hU
  have hA : ∀ y : V, ∃ A : V.affineOpens, y ∈ A.1 ∧ A.1 ≤ g ⁻¹ᵁ (U y).1 := fun y => by
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAle⟩ := V.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ ((g ⁻¹ᵁ (U y).1 : V.Opens) : Set V) from hyU y) (g ⁻¹ᵁ (U y).1).isOpen
    exact ⟨⟨A, hA⟩, hyA, hAle⟩
  choose A hyA hAU using hA
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top A ?_ fun y => ?_
  · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyA y⟩
  · rw [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply,
      GlobalTheory.Principalise.comapIdealAffine _ g (U y) (A y) (hAU y),
      GlobalTheory.Principalise.comapIdealAffine _ g (U y) (A y) (hAU y),
      GlobalTheory.Principalise.comapIdealAffine _ g (U y) (A y) (hAU y),
      Scheme.IdealSheafData.ideal_inf, Pi.inf_apply]
    exact map_inf_of_flat _ (g.flat_appLE (U y).2 (A y).2 (hAU y)) _ _

end GlobalTheory.FlatInf
