import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem abelianScheme_id_pow_finite_etale_surjective :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (m : ℕ), IsAbelianScheme A → IsUnit (m : Γ(S, ⊤)) → IsMonHom ((𝟙 A) ^ m) ∧ IsFinite ((𝟙 A) ^ m).left ∧ Etale ((𝟙 A) ^ m).left ∧ Surjective ((𝟙 A) ^ m).left := by
  intro S A _ m hA hm
  obtain ⟨⟩ := hA
  have hmon : ∀ n : ℕ, IsMonHom ((𝟙 A) ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Hom.one_def]; infer_instance
    | succ n ih => rw [pow_succ, Hom.mul_def]; infer_instance
  have hfin : IsFinite ((𝟙 A) ^ m).left := GrpTangent.isFinite_id_pow A hm
  have het : Etale ((𝟙 A) ^ m).left := GrpTangent.etale_id_pow A hm
  refine ⟨hmon m, hfin, het, ⟨fun x => ?_⟩⟩
  set f := ((𝟙 A) ^ m).left with hf

  have hcl : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩

  have hw : A.hom (f x) = A.hom x := by
    rw [← Scheme.Hom.comp_apply, hf, Over.w]

  have hsub : A.hom ⁻¹' {A.hom x} ⊆ Set.range f :=
    (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected.subset_isClopen hcl
      ⟨f x, by simp [hw], Set.mem_range_self x⟩
  exact hsub rfl

end GlobalTheory
