import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem etSet_of_lists : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (N n : ℕ) (σ : Fin n → (𝟙_ (Over S') ⟶ G')) (K : Set G.left), IsAbelianScheme G → IsGrpPullback G' G f φ → IsUnit (N : Γ(S, ⊤)) → IsFinite f → Etale f → Surjective f → Lists N σ (φ ⁻¹' K) → EtSet G K := by
  intro S S' f G G' _ _ φ N n σ K hG h hN hfin het hsurj hL
  obtain ⟨hpow, hK, -⟩ := hL
  obtain ⟨-, hWf, hWe⟩ := GrpTangent.finiteEtale_mulN_torsion G hN
  have := hG.proper
  let T : Over S := Over.mk ((𝟙_ (Over S')).hom ≫ f)
  have hTf : IsFinite T.hom := by
    change IsFinite (𝟙 S' ≫ f); infer_instance
  have hTe : Etale T.hom := by
    change Etale (𝟙 S' ≫ f); infer_instance
  let ρ : (𝟙_ (Over S') ⟶ G') →* (T ⟶ G) :=
    MonoidHom.mk' (fun x => Over.homMk (x.left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]; rfl))
      fun x y => Over.OverMorphism.ext (h.2 _ x y _ _ rfl rfl).symm
  have hρ : ∀ j, ρ (σ j) ^ N = 1 := fun j => by rw [← map_pow, hpow, map_one]
  choose τ hτ using fun j => (LatticeTorsion.existsUnique_torsion G N (ρ (σ j)) (hρ j)).exists
  have hτl : ∀ j, (τ j).left ≫ (torsion.ι G N).left = (σ j).left ≫ φ := fun j =>
    congrArg (fun z => z.left) (hτ j)
  have hτf : ∀ j, IsFinite (τ j).left := fun j => by
    have : IsFinite ((τ j).left ≫ (torsion G N).hom) := by rw [Over.w]; exact hTf
    exact IsFinite.of_comp _ (torsion G N).hom
  have hτe : ∀ j, Etale (τ j).left := fun j => by
    have : Etale ((τ j).left ≫ (torsion G N).hom) := by rw [Over.w]; exact hTe
    exact Etale.of_comp _ (torsion G N).hom
  have hop : IsOpen (⋃ j, Set.range (τ j).left) :=
    isOpen_iUnion fun j => (τ j).left.isOpenMap.isOpen_range
  have hcl : IsClosed (⋃ j, Set.range (τ j).left) :=
    isClosed_iUnion_of_finite fun j => (τ j).left.isClosedMap.isClosed_range
  let U : (torsion G N).left.Opens := ⟨_, hop⟩
  have hU : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl)
  have hη : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
    exact IsClosedImmersion.of_comp _ G.hom
  have hι : IsClosedImmersion (torsion.ι G N).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GrpTangent.isPullback_torsion G N).flip hη
  have hφ : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip hsurj
  refine ⟨Over.mk (U.ι ≫ (torsion G N).hom), Over.homMk (U.ι ≫ (torsion.ι G N).left) (by simp), ?_, ?_, ?_, ?_⟩
  · change IsFinite (U.ι ≫ _); infer_instance
  · change Etale (U.ι ≫ _); infer_instance
  · change IsClosedImmersion (U.ι ≫ _); infer_instance
  · change Set.range (U.ι ≫ (torsion.ι G N).left) = K
    rw [← Set.image_preimage_eq K φ.surjective, hK, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    change _ '' (⋃ j, Set.range (τ j).left) = _
    rw [Set.image_iUnion, Set.image_iUnion]
    refine Set.iUnion_congr fun j => ?_
    rw [← Set.range_comp, ← Set.range_comp, ← TopCat.coe_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      ← Scheme.Hom.comp_base, hτl]

end GlobalTheory.HkFam
