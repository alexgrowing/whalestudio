import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionReduction

theorem eq_of_residue_eq : ∀ (S : Type) [CommRing S] (P : Out.PolAV (Sp S)) (T : Type) [CommRing T] [IsLocalRing T] (b : S →+* T) (n : ℕ), IsUnit (n : T) → ∀ x y : Over.mk (spMap b) ⟶ P.A, x ^ n = 1 → y ^ n = 1 → spMap (IsLocalRing.residue T) ≫ x.left = spMap (IsLocalRing.residue T) ≫ y.left → x = y := by
  intro S _ P T _ _ b n hn x y hx hy hr
  letI := P.isAb.comm
  haveI : Smooth P.A.hom := P.isAb.smooth
  let j : Sp T ⟶ Sp S := spMap b
  let G : Over (Sp T) := (Over.pullback j).obj P.A
  have hn' : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  let m : G.left ⟶ G.left := (Out.mulA G n).left
  have hw : m ≫ G.hom = G.hom := Over.w _
  have h₁ : FormallyUnramified m := formallyUnramified_mulA (Sp T) G n hn'
  have h₂ : LocallyOfFiniteType (m ≫ G.hom) := by
    rw [hw]; dsimp [G]; infer_instance
  have h₃ : LocallyOfFiniteType m := locallyOfFiniteType_of_comp _ G.hom
  have e : (Over.pullback j).map (Out.mulA P.A n) = Out.mulA G n :=
    (map_pow (Over.pullback j).homMonoidHom (𝟙 P.A) n).trans
      (congrArg (· ^ n) (CategoryTheory.Functor.map_id (Over.pullback j) P.A))
  have mf : m ≫ pullback.fst P.A.hom j = pullback.fst P.A.hom j ≫ (Out.mulA P.A n).left := by
    change (Out.mulA G n).left ≫ _ = _
    rw [← e]; exact pullback.lift_fst _ _ _
  have kx : ∀ z : Over.mk (spMap b) ⟶ P.A, z ^ n = 1 → z.left ≫ (Out.mulA P.A n).left = j ≫ (η[P.A]).left := by
    intro z hz
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, hz, Hom.one_def]
    simp [j]
  let x' : Sp T ⟶ G.left := pullback.lift x.left (𝟙 _) (by simpa [j] using Over.w x)
  let y' : Sp T ⟶ G.left := pullback.lift y.left (𝟙 _) (by simpa [j] using Over.w y)
  have x₁ : x' ≫ pullback.fst P.A.hom j = x.left := pullback.lift_fst _ _ _
  have y₁ : y' ≫ pullback.fst P.A.hom j = y.left := pullback.lift_fst _ _ _
  have x₂ : x' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have y₂ : y' ≫ pullback.snd P.A.hom j = 𝟙 _ := pullback.lift_snd _ _ _
  have hab : x' ≫ m = y' ≫ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, mf, pullback.lift_fst_assoc, pullback.lift_fst_assoc, kx x hx, kx y hy]
    · rw [Category.assoc, Category.assoc]
      change x' ≫ m ≫ G.hom = y' ≫ m ≫ G.hom
      rw [hw]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hc : spMap (IsLocalRing.residue T) ≫ x' = spMap (IsLocalRing.residue T) ≫ y' := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) x₁).trans
        (hr.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) y₁)).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (x₂.trans y₂.symm)).trans (Category.assoc _ _ _).symm)
  have hopen := isOpenImmersion_equalizer_ι_of_unramified m hab
  have hsub := range_subset_range_equalizer_ι _ hc
  have hcl : IsLocalRing.closedPoint T ∈ Set.range (equalizer.ι x' y') :=
    hsub ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue T)⟩
  have hall : Set.range (equalizer.ι x' y') = Set.univ :=
    Set.eq_univ_of_forall fun p =>
      (IsLocalRing.specializes_closedPoint p).mem_open (equalizer.ι x' y').isOpenEmbedding.isOpen_range hcl
  have hxy : x' = y' := eq_of_range_equalizer_ι_eq_univ m hab hall
  apply Over.OverMorphism.ext
  exact x₁.symm.trans ((congrArg (· ≫ pullback.fst P.A.hom j) hxy).trans y₁)

end GlobalTheory.TorsionReduction
