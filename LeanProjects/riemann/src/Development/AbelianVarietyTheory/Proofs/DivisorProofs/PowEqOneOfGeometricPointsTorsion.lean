import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.TorsGeomPow

theorem pow_eq_one_of_geometric_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left),
      ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1 := by
  intro S A _ hA n hn T x hx d hpt
  obtain ⟨-, -, hZe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  set P : Over S := pullback (mulN A n) (η : 𝟙_ (Over S) ⟶ A) with hP
  have hPe : Etale P.hom := hZe
  have hxd : (x ^ d) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, ← pow_mul, mul_comm, pow_mul, hx, one_pow, CategoryTheory.Hom.one_def]
  have h1 : (1 : T ⟶ A) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, one_pow, CategoryTheory.Hom.one_def]
  let y₁ : T ⟶ P := pullback.lift (x ^ d) (toUnit T) hxd
  let u₁ : T ⟶ P := pullback.lift 1 (toUnit T) h1
  have hy : y₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = x ^ d := pullback.lift_fst _ _ _
  have hu : u₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = 1 := pullback.lift_fst _ _ _
  have key : ∀ {W : Over S} (f : W ⟶ T), (f ≫ x) ^ d = 1 → f ≫ y₁ = f ≫ u₁ := by
    intro W f hf
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hy, hu, MonObj.comp_pow, hf, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hyu : y₁ = u₁ := by
    haveI := hPe
    have hw : y₁.left ≫ P.hom = u₁.left ≫ P.hom := by rw [Over.w, Over.w]
    let l : T.left ⟶ pullback P.hom P.hom := pullback.lift _ _ hw
    have hl1 : l ≫ pullback.fst _ _ = y₁.left := pullback.lift_fst _ _ _
    have hl2 : l ≫ pullback.snd _ _ = u₁.left := pullback.lift_snd _ _ _
    have hs : Function.Surjective (pullback.snd (pullback.diagonal P.hom) l) := by
      intro s
      let k := AlgebraicClosure (T.left.residueField s)
      let ξ : Sp k ⟶ T.left :=
        Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField s) k)) ≫ T.left.fromSpecResidueField s
      have hξ : ξ ≫ y₁.left = ξ ≫ u₁.left :=
        congrArg CommaMorphism.left (key (Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) (hpt k ξ))
      have hq : (ξ ≫ y₁.left) ≫ pullback.diagonal P.hom = ξ ≫ l := by
        apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [pullback.diagonal_fst, Category.comp_id, hl1]
        · simp only [Category.assoc]
          rw [pullback.diagonal_snd, Category.comp_id, hl2, hξ]
      refine ⟨pullback.lift _ _ hq (IsLocalRing.closedPoint k), ?_⟩
      have e : (pullback.lift _ _ hq ≫ pullback.snd (pullback.diagonal P.hom) l) (IsLocalRing.closedPoint k) =
          ξ (IsLocalRing.closedPoint k) := by rw [Limits.pullback.lift_snd]
      refine (Eq.trans ?_ e).trans ?_
      · rfl
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply s _)
    have : Epi (pullback.snd (pullback.diagonal P.hom) l).base :=
      (TopCat.epi_iff_surjective _).2 hs
    have : IsIso (pullback.snd (pullback.diagonal P.hom) l) := IsOpenImmersion.isIso _
    have hl : l = inv (pullback.snd (pullback.diagonal P.hom) l) ≫ pullback.fst _ _ ≫
        pullback.diagonal P.hom := by
      rw [pullback.condition, IsIso.inv_hom_id_assoc]
    apply Over.OverMorphism.ext
    rw [← hl1, ← hl2, hl]
    simp
  rw [← hy, hyu, hu]

end GlobalTheory.TorsGeomPow
