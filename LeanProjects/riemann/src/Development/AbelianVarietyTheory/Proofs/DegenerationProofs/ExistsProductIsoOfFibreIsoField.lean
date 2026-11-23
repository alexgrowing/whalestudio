import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.AbPartIso

theorem exists_prodIso {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {H : Over S'} {Φ : H.left ⟶ G.left}
    (h : IsPullback Φ H.hom G.hom f) :
    ∃ ψ : (Over.mk f ⊗ G).left ≅ H.left, ψ.hom ≫ Φ = (snd (Over.mk f) G).left ∧
      ψ.hom ≫ H.hom = (fst (Over.mk f) G).left := by
  have p : IsPullback (snd (Over.mk f) G).left (fst (Over.mk f) G).left G.hom f :=
    (IsPullback.of_hasPullback f G.hom).flip
  exact ⟨p.isoIsPullback _ _ h, p.isoIsPullback_hom_fst _ _ h, p.isoIsPullback_hom_snd _ _ h⟩

theorem exists_prodIso_of_common {S S' : Scheme.{0}} {f : S' ⟶ S} {G G' : Over S} {H : Over S'}
    [GrpObj G] [GrpObj G'] [GrpObj H] {Φ : H.left ⟶ G.left} {Ψ : H.left ⟶ G'.left}
    (h : IsGrpPullback H G f Φ) (h' : IsGrpPullback H G' f Ψ) :
    ∃ (φ : Over.mk f ⊗ G ≅ Over.mk f ⊗ G') (ψ : (Over.mk f ⊗ G).left ⟶ H.left),
      ψ ≫ Φ = (snd (Over.mk f) G).left ∧ ψ ≫ H.hom = (fst (Over.mk f) G).left ∧
      ψ ≫ Ψ = (φ.hom ≫ snd (Over.mk f) G').left ∧ φ.hom ≫ fst _ _ = fst _ _ ∧
      ∀ (Z : Over S) (t : Z ⟶ Over.mk f) (x y : Z ⟶ G),
        lift t (x * y) ≫ φ.hom ≫ snd _ _ = (lift t x ≫ φ.hom ≫ snd _ _) * (lift t y ≫ φ.hom ≫ snd _ _) := by
  obtain ⟨ψ, e₁, e₂⟩ := exists_prodIso h.1
  obtain ⟨ψ', e₁', e₂'⟩ := exists_prodIso h'.1
  have w : ∀ G₀ : Over S, (fst (Over.mk f) G₀).left ≫ f = (Over.mk f ⊗ G₀).hom := fun G₀ =>
    Over.w (fst (Over.mk f) G₀)
  have k₂ : (ψ ≪≫ ψ'.symm).hom ≫ (fst (Over.mk f) G').left = (fst (Over.mk f) G).left := by
    rw [← e₂', ← e₂]; simp
  have k₁ : (ψ ≪≫ ψ'.symm).hom ≫ (snd (Over.mk f) G').left = ψ.hom ≫ Ψ := by
    rw [← e₁']; simp
  let φ : Over.mk f ⊗ G ≅ Over.mk f ⊗ G' := Over.isoMk (ψ ≪≫ ψ'.symm) (by
    rw [← w, ← w, ← k₂]; exact (Category.assoc _ _ _).symm)
  have k : (φ.hom ≫ snd (Over.mk f) G').left = ψ.hom ≫ Ψ := k₁
  refine ⟨φ, ψ.hom, e₁, e₂, k.symm, Over.OverMorphism.ext k₂, fun Z t x y => ?_⟩
  obtain ⟨Zl, ⟨⟨⟩⟩, Zh⟩ := Z
  have ht : t.left ≫ f = Zh := Over.w t
  let up : (Over.mk Zh ⟶ G) → (Over.mk t.left ⟶ H) := fun z =>
    Over.homMk ((lift t z).left ≫ ψ.hom) (by
      show ((lift t z).left ≫ ψ.hom) ≫ H.hom = t.left
      rw [Category.assoc, e₂]
      exact congrArg CommaMorphism.left (lift_fst t z))
  have hup : ∀ z, (up z).left ≫ Φ = z.left := fun z => by
    show ((lift t z).left ≫ ψ.hom) ≫ Φ = z.left
    rw [Category.assoc, e₁]
    exact congrArg CommaMorphism.left (lift_snd t z)
  have hup' : ∀ z, (up z).left ≫ Ψ = (lift t z ≫ φ.hom ≫ snd _ _).left := fun z => by
    show ((lift t z).left ≫ ψ.hom) ≫ Ψ = (lift t z).left ≫ (φ.hom ≫ snd _ _).left
    rw [Category.assoc, k]
  have hm : up (x * y) = up x * up y := by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hup, ← h.2 _ (up x) (up y) (pushPt h.1.w (up x)) (pushPt h.1.w (up y)) rfl rfl]
      exact mul_left_congr ht.symm x y _ _ (hup x).symm (hup y).symm
    · rw [Over.w, Over.w]
  apply Over.OverMorphism.ext
  refine (hup' (x * y)).symm.trans ?_
  rw [hm, ← h'.2 _ (up x) (up y) (pushPt h'.1.w (up x)) (pushPt h'.1.w (up y)) rfl rfl]
  exact mul_left_congr ht _ _ _ _ (hup' x) (hup' y)

theorem exists_iso_of_isFib : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (Q Q' : PolAV (Sp F)) (Φ : Q.A.left ⟶ D.P.A.left) (Φ' : Q'.A.left ⟶ D'.P.A.left), IsFib D F Q Φ → IsFib D' F Q' Φ' → ∀ σ : Q.A ≅ Q'.A, IsPolIso Q Q' σ → ∃ (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) (w : BunIso φ), HomF φ ∧ w.IsGen ∧ ∀ (a : TF (R := R) F ⟶ D.P.A) (a' : TF (R := R) F ⟶ D'.P.A), (∀ x : baseOver (Sp F) ⟶ Q.A, a.left = x.left ≫ Φ → a'.left = (x ≫ σ.hom).left ≫ Φ') → lift (𝟙 _) a ≫ φ.hom = lift (𝟙 _) a' := by
  intro R _ _ D D' F _ _ Q Q' Φ Φ' hΦ hΦ' σ hσ
  have := hσ.1
  have g' : IsGrpPullback Q.A D'.P.A (TF (R := R) F).hom (σ.hom.left ≫ Φ') :=
    ((isGrpPullback_of_iso σ).comp hΦ'.1).congr (Category.id_comp _) rfl
  obtain ⟨φ, ψ, e₁, e₂, e₃, e₄, e₅⟩ := exists_prodIso_of_common hΦ.1 g'
  have l₁ : LBIso (Q'.L.pull σ.hom.left) (D'.P.L.pull (σ.hom.left ≫ Φ')) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q'.L _ _ rfl)
      (chartPullSame D'.P.L (fun _ : PUnit => σ.hom.left ≫ Φ') (fun _ => Φ') _ σ.hom.left fun _ => rfl) hΦ'.2.1
  have l₂ : LBIso Q.L (D'.P.L.pull (σ.hom.left ≫ Φ')) :=
    LBIso.trans Q.isLB (pull_isLB Q'.isLB _) (pull_isLB D'.P.isLB _) (LBIso.symm hσ.2) l₁
  have l₃ : LBIso (D.P.L.pull Φ) (D'.P.L.pull (σ.hom.left ≫ Φ')) :=
    LBIso.trans (pull_isLB D.P.isLB _) Q.isLB (pull_isLB D'.P.isLB _) (LBIso.symm hΦ.2.1) l₂
  obtain ⟨w, hw⟩ : LBIso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left)
      (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left) :=
    LBIso.chartPull
      (chartPullSame D.P.L (fun _ : PUnit => (snd (TF (R := R) F) D.P.A).left) (fun _ => Φ) _ ψ fun _ => e₁.symm)
      (chartPullSame D'.P.L (fun _ : PUnit => (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)
        (fun _ => σ.hom.left ≫ Φ') _ ψ fun _ => e₃.symm) l₃
  refine ⟨φ, w, ⟨e₄, e₅⟩, hw, fun a a' ha => ?_⟩
  let x : baseOver (Sp F) ⟶ Q.A := Over.homMk ((lift (𝟙 (TF (R := R) F)) a).left ≫ ψ) (by
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans ?_)
    exact congrArg CommaMorphism.left (lift_fst (𝟙 (TF (R := R) F)) a))
  have hx : a.left = x.left ≫ Φ := by
    refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ?_))
    exact congrArg CommaMorphism.left (lift_snd (𝟙 (TF (R := R) F)) a)
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst]
    exact (congrArg (_ ≫ ·) e₄).trans (lift_fst _ _)
  · rw [Category.assoc, lift_snd]
    apply Over.OverMorphism.ext
    refine Eq.symm ((ha x hx).trans ?_)
    refine Eq.trans ?_ (congrArg ((lift (𝟙 (TF (R := R) F)) a).left ≫ ·) e₃)
    exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

end GlobalTheory.Ex.AbPartIso
end
