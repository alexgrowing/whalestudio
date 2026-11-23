import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem f_eq_of_pt_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z Y : Scheme.{0}} {x x' : Pt A B L M Z} (h : x = x') (p : Y ⟶ pullback A.hom x.t)
    (q : Y ⟶ pullback A.hom x'.t) (h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _)
    (h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _) : p ≫ x.f = q ≫ x'.f := by
  subst h
  rw [pullback.hom_ext h1 h2]

theorem exists_glue_data : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (x : ∀ i, HomGlue.Pt A B L M (𝒰.X i)), (∀ i j (T : Scheme.{0}) (b : T ⟶ 𝒰.X i) (c : T ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → (x i).map hL hM b = (x j).map hL hM c) → ∃ (t : Z ⟶ S) (f : pullback A.hom t ⟶ B.left), ∀ i, 𝒰.f i ≫ t = (x i).t ∧ ∀ e : pullback A.hom (x i).t ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = pullback.fst _ _ → e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ 𝒰.f i → e ≫ f = (x i).f := by
  intro S A B _ _ L M hL hM Z 𝒰 x hx
  have hxt : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (x i).t = pullback.snd (𝒰.f i) (𝒰.f j) ≫ (x j).t :=
    fun i j => congrArg Pt.t (hx i j _ _ _ pullback.condition)
  obtain ⟨t, ht⟩ : ∃ t : Z ⟶ S, ∀ i, 𝒰.f i ≫ t = (x i).t :=
    ⟨_, fun i => 𝒰.ι_glueMorphisms _ hxt i⟩
  have c1 : ∀ i, pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.snd A.hom t = pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ 𝒰.f i := fun i => pullback.condition
  have hw : ∀ i, (pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t) ≫ A.hom = pullback.snd (pullback.snd A.hom t) (𝒰.f i) ≫ (x i).t := by
    intro i
    rw [Category.assoc, pullback.condition, ← Category.assoc, c1, Category.assoc, ht]
  have hu1 : ∀ i, pullback.lift _ _ (hw i) ≫ pullback.fst A.hom (x i).t = pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ pullback.fst A.hom t :=
    fun i => pullback.lift_fst _ _ _
  have hu2 : ∀ i, pullback.lift _ _ (hw i) ≫ pullback.snd A.hom (x i).t = pullback.snd (pullback.snd A.hom t) (𝒰.f i) := fun i => pullback.lift_snd _ _ _
  have hc : ∀ i j, pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ (pullback.lift _ _ (hw i) ≫ (x i).f) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ (pullback.lift _ _ (hw j) ≫ (x j).f) := by
    intro i j
    have c3 : pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f i) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f j) := pullback.condition
    have hbc : (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ 𝒰.f i = (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← c1, ← c1, ← Category.assoc, ← Category.assoc, c3]
    have H := hx i j _ _ _ hbc
    have e1 : (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) ≫ pullback.fst _ _) ≫ A.hom = 𝟙 _ ≫ (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).t := by
      rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (pullback.lift _ _ (hw i)),
        hu2, Category.assoc]
    have e2 : (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) ≫ pullback.fst _ _) ≫ A.hom = 𝟙 _ ≫ (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).t := by
      rw [Category.id_comp, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (pullback.lift _ _ (hw j)),
        hu2, Category.assoc]
    obtain ⟨p, hp1, hp2⟩ : ∃ p : pullback (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ⟶ pullback A.hom ((pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).t),
        p ≫ pullback.fst _ _ = pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) ≫ pullback.fst _ _ ∧ p ≫ pullback.snd _ _ = 𝟙 _ :=
      ⟨pullback.lift _ _ e1, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨q, hq1, hq2⟩ : ∃ q : pullback (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ⟶ pullback A.hom ((pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).t),
        q ≫ pullback.fst _ _ = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) ≫ pullback.fst _ _ ∧ q ≫ pullback.snd _ _ = 𝟙 _ :=
      ⟨pullback.lift _ _ e2, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have h1 : p ≫ pullback.fst _ _ = q ≫ pullback.fst _ _ := by
      rw [hp1, hq1, hu1, hu1, ← Category.assoc, ← Category.assoc, c3]
    have h2 : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _ := by rw [hp2, hq2]
    have K : p ≫ pmap A (x i).t (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) ≫ (x i).f = q ≫ pmap A (x j).t (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) ≫ (x j).f :=
      f_eq_of_pt_eq H p q h1 h2
    have p1 : p ≫ pmap A (x i).t (pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i)) = pullback.fst (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw i) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hp1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hp2, Category.id_comp, Category.assoc, hu2]
    have p2 : q ≫ pmap A (x j).t (pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f j)) = pullback.snd (pullback.fst (pullback.snd A.hom t) (𝒰.f i)) (pullback.fst (pullback.snd A.hom t) (𝒰.f j)) ≫ pullback.lift _ _ (hw j) := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, hq1, Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hq2, Category.id_comp, Category.assoc, hu2]
    rw [← Category.assoc, ← Category.assoc, ← p1, ← p2]
    exact (Category.assoc _ _ _).trans (K.trans (Category.assoc _ _ _).symm)
  let 𝒱 := 𝒰.pullback₁ (pullback.snd A.hom t)
  refine ⟨t, Scheme.Cover.glueMorphisms 𝒱 (fun i => pullback.lift _ _ (hw i) ≫ (x i).f) hc, fun i => ⟨ht i, fun e he1 he2 => ?_⟩⟩
  have hι : pullback.fst (pullback.snd A.hom t) (𝒰.f i) ≫ Scheme.Cover.glueMorphisms 𝒱 (fun i => pullback.lift _ _ (hw i) ≫ (x i).f) hc = pullback.lift _ _ (hw i) ≫ (x i).f :=
    Scheme.Cover.ι_glueMorphisms 𝒱 _ hc i
  have hv : e ≫ pullback.snd A.hom t = pullback.snd A.hom (x i).t ≫ 𝒰.f i := he2
  obtain ⟨v, hv1, hv2⟩ : ∃ v : pullback A.hom (x i).t ⟶ pullback (pullback.snd A.hom t) (𝒰.f i),
      v ≫ pullback.fst (pullback.snd A.hom t) (𝒰.f i) = e ∧ v ≫ pullback.snd (pullback.snd A.hom t) (𝒰.f i) = pullback.snd A.hom (x i).t :=
    ⟨pullback.lift e _ hv, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hvu : v ≫ pullback.lift _ _ (hw i) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hu1, ← Category.assoc, hv1, he1, Category.id_comp]
    · rw [Category.assoc, hu2, hv2, Category.id_comp]
  rw [← hv1, Category.assoc, hι, ← Category.assoc, hvu, Category.id_comp]

end GlobalTheory.EndLoc.HomGlue
