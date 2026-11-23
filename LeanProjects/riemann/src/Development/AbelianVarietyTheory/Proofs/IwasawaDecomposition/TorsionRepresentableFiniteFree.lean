import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRep

theorem exists_finite_free_rep (O : Type) [CommRing O] [HenselianLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Sp O)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (j : Sp A ⟶ Y), Module.Finite O A ∧ Module.Free O A ∧
      j ≫ f = spMap (algebraMap O A) ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
        (h : Sp B ⟶ Y), h ≫ f = spMap (algebraMap O B) → ∃! φ : A →ₐ[O] B, spMap (φ : A →+* B) ≫ j = h := by
  have : HenselianLocalRing (CommRingCat.of O) := ‹_›
  have hfin : IsFinite ((finitePart f).ι ≫ f) := isFinite_finitePart f
  have : IsAffine (finitePart f).toScheme := isAffine_of_isAffineHom ((finitePart f).ι ≫ f)
  let A : CommRingCat.{0} := Γ((finitePart f).toScheme, ⊤)
  let i : Spec A ≅ (finitePart f).toScheme := (finitePart f).toScheme.isoSpec.symm
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i.hom ≫ (finitePart f).ι ≫ f)
  have h₁ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    infer_instance
  have h₂ : ψ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hψ]
    infer_instance
  let _ : Algebra O A := ψ.hom.toAlgebra
  have h₃ : Module.Finite O A := h₁
  have h₄ : Module.Flat O A := h₂
  have hj : (i.hom ≫ (finitePart f).ι) ≫ f = spMap (algebraMap O A) := by
    rw [Category.assoc, ← hψ]; rfl
  refine ⟨A, inferInstance, inferInstance, i.hom ≫ (finitePart f).ι, h₃,
    Module.free_of_flat_of_isLocalRing, hj, fun B _ _ _ h hh => ?_⟩
  have : IsFinite (spMap (algebraMap O B)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 ‹_›)
  obtain ⟨l, hl, -⟩ := existsUnique_lift_finitePart f _ h hh
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (R := A) (S := .of B) (l ≫ i.inv)
  have hχ' : Spec.map χ ≫ i.hom ≫ (finitePart f).ι = h := by
    rw [hχ, Category.assoc, i.inv_hom_id_assoc, hl]
  have hc : CommRingCat.ofHom (algebraMap O A) ≫ χ = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ hh
    rw [← hχ', Category.assoc, hj]
  refine ⟨⟨χ.hom, fun r => congr(($hc).hom r)⟩, hχ', fun φ hφ => ?_⟩
  have h₅ : spMap (φ : A →+* B) = Spec.map χ := by
    rw [← cancel_mono (i.hom ≫ (finitePart f).ι)]
    exact hφ.trans hχ'.symm
  have h₆ := Spec.map_injective h₅
  exact AlgHom.ext fun a => congr(($h₆).hom a)

theorem exists_finite_free_torsion_rep : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : Type) [CommRing O] [HenselianLocalRing O] (x : Sp O ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (u : overAt x A ⟶ G), Module.Finite O A ∧ Module.Free O A ∧ u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 → ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g := by
  intro X G _ _ hG O _ _ x q hq
  obtain ⟨hf, hqf⟩ := GlobalTheory.T.pow_flat_locallyQuasiFinite X G hG q hq
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  let m : G ⟶ G := (𝟙 G) ^ q
  have hm : ∀ {T : Over X} (g : T ⟶ G), g ≫ m = g ^ q := fun g => by
    rw [MonObj.comp_pow, Category.comp_id]
  have : Flat m.left := hf
  have : LocallyQuasiFinite m.left := hqf
  have : LocallyOfFiniteType (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType m.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact m.left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated m.left := IsSeparated.of_comp _ G.hom
  let e : Sp O ⟶ G.left := (1 : Over.mk x ⟶ G).left
  have he : e ≫ G.hom = x := Over.w (1 : Over.mk x ⟶ G)
  have h1 : ∀ (B : Type) [CommRing B] [Algebra O B],
      (1 : overAt x B ⟶ G).left = spMap (algebraMap O B) ≫ e := fun B _ _ => by
    let t : overAt x B ⟶ Over.mk x := Over.homMk (spMap (algebraMap O B)) rfl
    rw [← MonObj.comp_one t]
    rfl
  have : LocallyQuasiFinite (pullback.snd m.left e) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (IsPullback.of_hasPullback m.left e) hqf
  obtain ⟨A, _, _, j, hA₁, hA₂, hj, H⟩ := exists_finite_free_rep O (pullback.snd m.left e)
  have hu : (j ≫ pullback.fst m.left e) ≫ m.left = spMap (algebraMap O A) ≫ e := by
    rw [Category.assoc, pullback.condition, reassoc_of% hj]
  let u : overAt x A ⟶ G := Over.homMk (j ≫ pullback.fst m.left e) (by
    rw [← Over.w m, ← Category.assoc]
    exact (congrArg (· ≫ G.hom) hu).trans (by rw [Category.assoc, he]; rfl))
  refine ⟨A, inferInstance, inferInstance, u, hA₁, hA₂, ?_, fun B _ _ _ g hg => ?_⟩
  · rw [← hm]
    exact Over.OverMorphism.ext (hu.trans (h1 A).symm)
  have hg' : g.left ≫ m.left = spMap (algebraMap O B) ≫ e := by
    rw [← Over.comp_left, hm, hg, h1]
  obtain ⟨φ, hφ, hφ'⟩ := H B (pullback.lift g.left (spMap (algebraMap O B)) hg') (pullback.lift_snd _ _ _)
  refine ⟨φ, Over.OverMorphism.ext ?_, fun φ' h' => hφ' φ' ?_⟩
  · change spMap (φ : A →+* B) ≫ j ≫ pullback.fst m.left e = g.left
    rw [← Category.assoc, hφ]
    exact pullback.lift_fst _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc]
      exact (congrArg CommaMorphism.left h').trans (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, hj]
      refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ'.comp_algebraMap]

end GlobalTheory.TorsionRep
