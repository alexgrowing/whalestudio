import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

set_option autoImplicit false

namespace GlobalTheory.HilbGlue

theorem idealSheaf_ext_of_openImmersions {P : Scheme.{0}} {ι : Type*} {X : ι → Scheme.{0}}
    (f : ∀ i, X i ⟶ P) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x : P, ∃ i y, f i y = x)
    (I J : P.IdealSheafData) (h : ∀ i, I.comap (f i) = J.comap (f i)) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := Σ i, (X i).affineOpens)
    (fun a => ⟨f a.1 ''ᵁ a.2.1, a.2.2.image_of_isOpenImmersion (f a.1)⟩) ?_ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨W, hW, hyW⟩ : ∃ W : (X i).Opens, IsAffineOpen W ∧ y ∈ W := by
      obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ := (X i).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ y) isOpen_univ
      exact ⟨W, hW, hy⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, W, hW⟩, ⟨y, hyW, rfl⟩⟩
  · rintro ⟨i, W⟩
    have e := congrArg (fun K : (X i).IdealSheafData => K.ideal W) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((f i).appIso W).inv).2) e

end GlobalTheory.HilbGlue

theorem GlobalTheory.HilbGlue.HPt.ext_openCover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x x' : GlobalTheory.HilbGlue.HPt z r Y), (∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x = GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x') → x = x' := by
  intro S Z z r Y 𝒰 x x' e
  obtain ⟨g, I⟩ := x
  obtain ⟨g', I'⟩ := x'
  obtain rfl : g = g' := 𝒰.hom_ext _ _ fun i => congrArg Sigma.fst (e i)
  rw [HPt.mk_eq_mk_iff]
  have hP : ∀ i : 𝒰.I₀, IsPullback (pullback.snd z (𝒰.f i ≫ g)) (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) (𝒰.f i)
      (pullback.snd z g) := fun i => (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).flip
  haveI : ∀ i : 𝒰.I₀, IsOpenImmersion (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i) inferInstance
  refine idealSheaf_ext_of_openImmersions (ι := 𝒰.I₀) (X := fun i => pullback z (𝒰.f i ≫ g)) (fun i => bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) ?_ I.1 I'.1 fun i => ?_
  · intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (pullback.snd z g x)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd z g)
      (g := 𝒰.f i) x y hy.symm
    refine ⟨i, (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw]
  · have := (HPt.mk_eq_mk_iff _ _).1 (e i)
    exact this
