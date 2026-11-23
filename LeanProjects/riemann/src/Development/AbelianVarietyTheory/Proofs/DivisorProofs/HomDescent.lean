import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedDescent

theorem hom_descent : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B B' : Over (Sp k₀)) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B', IsMonHom f → ∃! f₀ : B ⟶ B', IsMonHom f₀ ∧ (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
  intro k₀ K _ _ _ _ B B' _ _ hB hB' f hf
  have hP : IsAbelianScheme (B ⊗ B') := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB'
  let i : B ⟶ B ⊗ B' := lift (𝟙 B) 1
  let j : B' ⟶ B ⊗ B' := lift 1 (𝟙 B')
  have hi : IsMonHom i := by
    have : IsMonHom (1 : B ⟶ B') := by
      rw [Hom.one_def]; infer_instance
    infer_instance
  have hj : IsMonHom j := by
    have : IsMonHom (1 : B' ⟶ B) := by
      rw [Hom.one_def]; infer_instance
    infer_instance
  obtain ⟨F₀, ⟨hF₀, hF⟩, -⟩ := endo_descent (K := K) (B ⊗ B') hP
    ((Over.pullback (spMap (algebraMap k₀ K))).map (fst B B') ≫ f ≫
      (Over.pullback (spMap (algebraMap k₀ K))).map j) inferInstance
  have key : (Over.pullback (spMap (algebraMap k₀ K))).map (i ≫ F₀ ≫ snd B B') = f := by
    rw [Functor.map_comp, Functor.map_comp, hF]
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← Functor.map_comp_assoc, lift_fst, lift_snd,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
  exact ⟨i ≫ F₀ ≫ snd B B', ⟨inferInstance, key⟩, fun f₁ hf₁ =>
    ActDescent.pullback_map_injective (spMap (algebraMap k₀ K)) B B' (hf₁.2.trans key.symm)⟩

end GlobalTheory.AlgClosedDescent
