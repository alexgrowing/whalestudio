import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

set_option backward.isDefEq.respectTransparency false in

theorem tors_glue_away : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (B : Type) [CommRing B] [Algebra R B], ∀ (Idx : Type) (f : Idx → B), Ideal.span (Set.range f) = ⊤ → ∀ z : ∀ i, Tors G N (Localization.Away (f i)), (∀ (i j : Idx) (D : Type) [CommRing D] [Algebra R D] (a : Localization.Away (f i) →ₐ[R] D) (b : Localization.Away (f j) →ₐ[R] D), a.comp (IsScalarTower.toAlgHom R B (Localization.Away (f i))) = b.comp (IsScalarTower.toAlgHom R B (Localization.Away (f j))) → torsMap a (z i) = torsMap b (z j)) → ∃ w : Tors G N B, ∀ i, torsMap (IsScalarTower.toAlgHom R B (Localization.Away (f i))) w = z i := by
  intro R _ G _ _ N B _ _ Idx f hf z h
  let q : ∀ i, B →ₐ[R] Localization.Away (f i) := fun i => IsScalarTower.toAlgHom R B (Localization.Away (f i))
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of B) f hf).openCover
  let y : ∀ i : Idx, 𝒰.X i ⟶ G.left := fun i => (z i).1.left
  have hc : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ y i = pullback.snd _ _ ≫ y j := by
    intro (i : Idx) (j : Idx)
    have := congrArg (fun t => CommaMorphism.left t.1) (h i j
      (TensorProduct B (Localization.Away (f i)) (Localization.Away (f j)))
      Algebra.TensorProduct.includeLeft
      (Algebra.TensorProduct.includeRight.restrictScalars R)
      (AlgHom.ext fun a => by
        change (algebraMap B (Localization.Away (f i)) a) ⊗ₜ[B] (1 : Localization.Away (f j)) =
          (1 : Localization.Away (f i)) ⊗ₜ[B] algebraMap B (Localization.Away (f j)) a
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]))
    change pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (f i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (f j))))) ≫ _ = pullback.snd _ _ ≫ _
    rw [← pullbackSpecIso_hom_fst, ← pullbackSpecIso_hom_snd, Category.assoc, Category.assoc]
    exact congrArg _ this
  have hk : ∀ i : Idx, (spOver (q i)).left ≫ 𝒰.glueMorphisms y hc = (z i).1.left :=
    fun i => 𝒰.ι_glueMorphisms y hc i
  have hw : 𝒰.glueMorphisms y hc ≫ G.hom = (SpAlg R B).hom := by
    refine 𝒰.hom_ext _ _ fun (i : Idx) => ?_
    change (spOver (q i)).left ≫ _ = (spOver (q i)).left ≫ (SpAlg R B).hom
    rw [← Category.assoc, hk, Over.w, Over.w]
  let w : SpAlg R B ⟶ G := Over.homMk (𝒰.glueMorphisms y hc) hw
  have hres : ∀ i, spOver (q i) ≫ w = (z i).1 := fun i => Over.OverMorphism.ext (hk i)
  have hN : w ^ N = 1 := by
    refine Over.OverMorphism.ext (𝒰.hom_ext _ _ fun (i : Idx) => ?_)
    have e : spOver (q i) ≫ (w ^ N) = spOver (q i) ≫ 1 := by
      rw [MonObj.comp_pow, hres, (z i).2, MonObj.comp_one]
    exact congrArg CommaMorphism.left e
  exact ⟨⟨w, hN⟩, fun i => Subtype.ext (hres i)⟩

end GlobalTheory.GroupBplus.Aff
