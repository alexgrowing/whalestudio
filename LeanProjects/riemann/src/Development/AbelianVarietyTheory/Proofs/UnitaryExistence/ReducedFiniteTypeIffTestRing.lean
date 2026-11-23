import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem reduced_finiteType_iff_testRing :
    ∀ (K : Type) [Field K], (∀ (R : Type) [CommRing R] [Algebra K R], Algebra.FiniteType K R → IsReduced R → ∃ p : TRing K, Nonempty (p.R ≃ₐ[K] R)) ∧ ∀ p : TRing K, Algebra.FiniteType K p.R ∧ IsReduced p.R := by
  intro K _
  refine ⟨fun R _ _ hft hred => ?_, fun p => ⟨inferInstance, ?_⟩⟩
  · obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
    have hrad : (RingHom.ker f).IsRadical := by
      intro x hx
      obtain ⟨m, hm⟩ := hx
      rw [RingHom.mem_ker, map_pow] at hm
      exact (RingHom.mem_ker).2 (IsReduced.eq_zero _ ⟨m, hm⟩)
    exact ⟨⟨n, RingHom.ker f, hrad⟩, ⟨Ideal.quotientKerAlgEquivOfSurjective hf⟩⟩
  · exact (Ideal.isRadical_iff_quotient_reduced p.I).1 p.3

end GlobalTheory
