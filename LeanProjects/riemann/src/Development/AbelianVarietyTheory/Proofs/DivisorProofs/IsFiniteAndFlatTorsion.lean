import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbTorsionAnyBase

open ReciprocityTheory.ChartRestriction.G.Out

theorem isFinite_and_flat_mulA (S : Scheme.{0}) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A)
    (k : ℕ) (hk : 1 ≤ k) : IsFinite (mulA A k).left ∧ Flat (mulA A k).left := by
  have hc := hA.comm
  have hsm := hA.smooth
  have hpr := hA.proper
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA A k
  have hg : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map (mulA A k)).left := fun K _ _ t => by
    rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA]
    exact GlobalTheory.MulFiniteAny.isFinite_mulA K _ (TLinPf.isAb_pullback t A hA) k hk
  have h1 : IsProper ((mulA A k).left ≫ A.hom) := by rw [Over.w]; exact hpr
  have h2 : IsProper (mulA A k).left := IsProper.of_comp _ A.hom
  have h3 : LocallyQuasiFinite (mulA A k).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _
      (GlobalTheory.MulFiniteFlat.finite_preimage_of_geomFibres _ hg)
  have hf : IsFinite (mulA A k).left := .of_isProper_of_locallyQuasiFinite _
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S _ _ _
    inferInstance inferInstance inferInstance hf fun K _ _ t => ?_⟩
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (TLinPf.isAb_pullback t A hA) _ inferInstance (hg K t)).1

theorem isFinite_and_flat_torsion : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ N : ℕ, 1 ≤ N → IsFinite (torsion B N).hom ∧ Flat (torsion B N).hom := by
  intro S B _ hB N hN
  obtain ⟨h1, h2⟩ := isFinite_and_flat_mulA S B hB N hN
  rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion B N) h1,
    MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion B N) h2⟩

end GlobalTheory.AbTorsionAnyBase
