import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdealThickeningImmersionOfIsPullbackSquareZeroStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AddFamLift

theorem isPullback_lift {S : Scheme.{0}} (Z U S' : Over S) {W : Scheme.{0}} {pr : W ⟶ Z.left} {t : W ⟶ U.left}
    (hp : IsPullback pr t Z.hom U.hom) (j : (Z ⊗ (U ⊗ S')).left ⟶ W)
    (hj₁ : j ≫ pr = (fst Z (U ⊗ S')).left) (hj₂ : j ≫ t = (snd Z (U ⊗ S')).left ≫ (fst U S').left) :
    IsPullback j ((snd Z (U ⊗ S')).left ≫ (snd U S').left) (t ≫ U.hom) S'.hom := by
  have outer : IsPullback (fst Z (U ⊗ S')).left (snd Z (U ⊗ S')).left Z.hom (U ⊗ S').hom :=
    IsPullback.of_hasPullback Z.hom (U ⊗ S').hom
  have e : (U ⊗ S').hom = (fst U S').left ≫ U.hom := (Over.w _).symm
  rw [e, ← hj₁] at outer
  have left : IsPullback j (snd Z (U ⊗ S')).left t (fst U S').left := IsPullback.of_right outer hj₂ hp
  exact left.paste_vert (IsPullback.of_hasPullback U.hom S'.hom)

abbrev Ov {R C : Type} [CommRing R] [CommRing C] (σ : R →+* C) : Over (Sp R) := Over.mk (spMap σ)

theorem finiteRing_sq_sub_mul_sq_eq_of_card (hAb : AbLift) (R : Type) [CommRing R] (J : Ideal R) (hJ : J ^ 2 = ⊥) (A : Over (Sp R)) [GrpObj A]
    (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (C : Type) [CommRing C] (σ : R →+* C)
    (N : LB (A ⊗ (Ov σ ⊗ Ov (Ideal.Quotient.mk J))).left) (hN : N.IsLB) (hadd : IsAdditive N) :
    ∃ c : Pic (A ⊗ Ov σ).left, CechPic.pull (A ◁ fst (Ov σ) (Ov (Ideal.Quotient.mk J))).left c = cls N hN := by
  letI := σ.toAlgebra
  let U := Ov σ
  let S' := Ov (Ideal.Quotient.mk J)
  obtain ⟨B, _, pr, pr', hB, hBg, hp, hp', hμ, h₁, h₂, -, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R C A g hA hg
  have hp : IsPullback pr B.hom A.hom U.hom := hp
  have hp' : IsPullback pr' (B ⊗ B).hom (A ⊗ A).hom U.hom := hp'
  have wZ : ∀ Z : Over (Sp R), (fst Z (U ⊗ S')).left ≫ Z.hom = ((snd Z (U ⊗ S')).left ≫ (fst U S').left) ≫ U.hom :=
    fun Z ↦ by rw [Category.assoc, Over.w, Over.w, Over.w]
  obtain ⟨i, hi₁, hi₂⟩ : ∃ i : (A ⊗ (U ⊗ S')).left ⟶ B.left, i ≫ pr = (fst A (U ⊗ S')).left ∧
      i ≫ B.hom = (snd A (U ⊗ S')).left ≫ (fst U S').left :=
    ⟨hp.lift _ _ (wZ A), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  obtain ⟨i', hi'₁, hi'₂⟩ : ∃ i' : ((A ⊗ A) ⊗ (U ⊗ S')).left ⟶ (B ⊗ B).left,
      i' ≫ pr' = (fst (A ⊗ A) (U ⊗ S')).left ∧ i' ≫ (B ⊗ B).hom = (snd (A ⊗ A) (U ⊗ S')).left ≫ (fst U S').left :=
    ⟨hp'.lift _ _ (wZ (A ⊗ A)), hp'.lift_fst _ _ _, hp'.lift_snd _ _ _⟩
  have hJ' : J.map σ ^ 2 = ⊥ := by rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have th : IsThick (J.map σ) B.hom i := by
    have q := isPullback_lift A U S' hp i hi₁ hi₂
    exact GlobalTheory.T.isIdealThickeningImmersion_of_isPullback_square_zero_quotient R C σ J hJ _ _ B.hom _ i q
  have th' : IsThick (J.map σ) (B ⊗ B).hom i' := by
    have q := isPullback_lift (A ⊗ A) U S' hp' i' hi'₁ hi'₂
    exact GlobalTheory.T.isIdealThickeningImmersion_of_isPullback_square_zero_quotient R C σ J hJ _ _ (B ⊗ B).hom _ i' q
  have key : ∀ (φ : A ⊗ A ⟶ A) (φB : B ⊗ B ⟶ B), φB.left ≫ pr = pr' ≫ φ.left →
      (φ ▷ (U ⊗ S')).left ≫ i = i' ≫ φB.left := by
    intro φ φB hφ
    apply hp.hom_ext
    · rw [Category.assoc, hi₁, Category.assoc, hφ, ← Category.assoc, hi'₁, ← Over.comp_left, ← Over.comp_left,
        whiskerRight_fst]
    · rw [Category.assoc, hi₂, Category.assoc, Over.w φB, hi'₂, ← Category.assoc, ← Over.comp_left,
        whiskerRight_snd]
  have ev : ∀ φ : A ⊗ A ⟶ A, CechPic.pull (φ ▷ (U ⊗ S')).left (cls N hN) =
      evc hN (fst (A ⊗ A) (U ⊗ S') ≫ φ) (snd (A ⊗ A) (U ⊗ S')) := fun φ ↦ by
    have : φ ▷ (U ⊗ S') = lift (fst (A ⊗ A) (U ⊗ S') ≫ φ) (snd (A ⊗ A) (U ⊗ S')) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerRight_fst, lift_fst]
      · rw [whiskerRight_snd, lift_snd]
    rw [this]; rfl
  have hm : fst (A ⊗ A) (U ⊗ S') ≫ μ[A] =
      (fst (A ⊗ A) (U ⊗ S') ≫ fst A A) * (fst (A ⊗ A) (U ⊗ S') ≫ snd A A) := by
    rw [← MonObj.comp_mul]
    congr 1
    show μ[A] = lift (fst A A) (snd A A) ≫ μ[A]
    rw [lift_fst_snd, Category.id_comp]
  have add : CechPic.pull (μ[A] ▷ (U ⊗ S')).left (cls N hN) =
      CechPic.pull (fst A A ▷ (U ⊗ S')).left (cls N hN) + CechPic.pull (snd A A ▷ (U ⊗ S')).left (cls N hN) := by
    rw [ev, ev, ev, hm]
    exact (isAdditive_iff hN).1 hadd _ _ _ _
  obtain ⟨c', hc'⟩ := hAb C (J.map σ) hJ' B g hB hBg _ _ i i' _ _ _ th th' (key _ _ hμ) (key _ _ h₁) (key _ _ h₂)
    (cls N hN) add
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k : (A ⊗ U).left ⟶ B.left, k ≫ pr = (fst A U).left ∧ k ≫ B.hom = (snd A U).left :=
    ⟨hp.lift _ _ (by rw [Over.w, Over.w]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  refine ⟨CechPic.pull k c', ?_⟩
  have hk : (A ◁ fst U S').left ≫ k = i := by
    apply hp.hom_ext
    · rw [Category.assoc, hk₁, hi₁, ← Over.comp_left, whiskerLeft_fst]
    · rw [Category.assoc, hk₂, hi₂, ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  rw [← pull_comp, hk, hc']

theorem main : AbLift → ∀ (R : Type) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (C : Type) [CommRing C] (σ : R →+* C) (N : LB (A ⊗ (Over.mk (spMap σ) ⊗ Over.mk (spMap (Ideal.Quotient.mk J)))).left) (hN : N.IsLB), IsAdditive N → ∃ c : Pic (A ⊗ Over.mk (spMap σ)).left, GlobalTheory.CechPic.pull (A ◁ fst (Over.mk (spMap σ)) (Over.mk (spMap (Ideal.Quotient.mk J)))).left c = cls N hN := fun hAb R _ J hJ A _ g hA hg C _ σ N hN hadd ↦
  finiteRing_sq_sub_mul_sq_eq_of_card hAb R J hJ A g hA hg C σ N hN hadd

end GlobalTheory.AddFamLift
