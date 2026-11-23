import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPrincipallyPolarisedAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumProd

namespace GlobalTheory.SumDeg

section Tens

variable {X Y Z : Scheme.{0}} (L M : LB X) {K : Type} [Fintype K]

lemma tens_le₁ (φ : K → (Y ⟶ X)) (jj : K → (tensLB L M).ι) :
    LB.wchart (tensLB L M) φ jj ≤ LB.wchart L φ (fun k => (jj k).1) :=
  fun _ hy => Set.mem_iInter.2 fun k => (Set.mem_iInter.1 hy k).1

lemma tens_le₂ (φ : K → (Y ⟶ X)) (jj : K → (tensLB L M).ι) :
    LB.wchart (tensLB L M) φ jj ≤ LB.wchart M φ (fun k => (jj k).2) :=
  fun _ hy => Set.mem_iInter.2 fun k => (Set.mem_iInter.1 hy k).2

def tensGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb M φ ε)) :
    LB.Gen (LB.LinComb (tensLB L M) φ ε) where
  s := fun jj => res (tens_le₁ L M φ jj) (t.s (fun k => (jj k).1)) * res (tens_le₂ L M φ jj) (t'.s (fun k => (jj k).2))

theorem gm_tensGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb M φ ε))
    (r : Z ⟶ Y) (z : Z) (jj : K → (tensLB L M).ι) (h : r z ∈ LB.wchart (tensLB L M) φ jj) :
    gm r z (LB.wchart (tensLB L M) φ jj) ((tensGen L M φ ε t t').s jj) =
      gm r z (LB.wchart L φ (fun k => (jj k).1)) (t.s (fun k => (jj k).1)) *
        gm r z (LB.wchart M φ (fun k => (jj k).2)) (t'.s (fun k => (jj k).2)) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ h _) (gm_res r z _ h _))

theorem trF_tens (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (jj jj' : K → (tensLB L M).ι)
    (h : r z ∈ LB.wchart (tensLB L M) φ jj) (h' : r z ∈ LB.wchart (tensLB L M) φ jj') :
    trF (L := tensLB L M) φ ε r z jj jj' =
      trF (L := L) φ ε r z (fun k => (jj k).1) (fun k => (jj' k).1) *
        trF (L := M) φ ε r z (fun k => (jj k).2) (fun k => (jj' k).2) := by
  unfold trF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow]
  refine congrArg (· ^ ε k) ?_
  have hm : (r ≫ φ k) z ∈ (tensLB L M).U (jj k) ⊓ (tensLB L M).U (jj' k) :=
    ⟨Set.mem_iInter.1 h k, Set.mem_iInter.1 h' k⟩
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z _ hm _) (gm_res _ z _ hm _))

theorem isGen_tensGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb M φ ε))
    (ht : t.IsGen) (ht' : t'.IsGen) : (tensGen L M φ ε t t').IsGen := by
  intro jj jj'
  refine unit_ext fun y hy => ?_
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_tensGen L M φ ε t t' (𝟙 Y) y jj hy.1)).trans
    (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb (tensLB L M) φ ε (𝟙 Y) y jj jj' hy.1 hy.2).trans
        (trF_tens L M φ ε (𝟙 Y) y jj jj' hy.1 hy.2))
      ((gm_res (𝟙 Y) y _ hy _).trans (gm_tensGen L M φ ε t t' (𝟙 Y) y jj' hy.2)))).symm)
  rw [gen_trans ht (𝟙 Y) y (tens_le₁ L M φ jj hy.1) (tens_le₁ L M φ jj' hy.2),
    gen_trans ht' (𝟙 Y) y (tens_le₂ L M φ jj hy.1) (tens_le₂ L M φ jj' hy.2), _root_.mul_mul_mul_comm]

variable {L M}

theorem good₁ {z : Z} {J : (Z ⟶ X) → (tensLB L M).ι} (hJ : Good (tensLB L M) z J) :
    Good L z (fun ψ => (J ψ).1) := fun ψ => (hJ ψ).1

theorem good₂ {z : Z} {J : (Z ⟶ X) → (tensLB L M).ι} (hJ : Good (tensLB L M) z J) :
    Good M z (fun ψ => (J ψ).2) := fun ψ => (hJ ψ).2

theorem val_tensGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb M φ ε))
    (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → (tensLB L M).ι} (hJ : Good (tensLB L M) z J) :
    val (tensGen L M φ ε t t') r z J = val t r z (fun ψ => (J ψ).1) * val t' r z (fun ψ => (J ψ).2) :=
  gm_tensGen L M φ ε t t' r z _ (hJ.mem φ r)

end Tens

section Cub

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def tensCub {L M : RigLB G} (c : CubicalStr G L) (d : CubicalStr G M)
    (r : LB.Gen ((tensLB L.L M.L).pull (eSec G))) (hL : (tensLB L.L M.L).IsLB) (hr : r.IsGen) :
    CubicalStr G ⟨tensLB L.L M.L, r, hL, hr⟩ where
  t := tensGen L.L M.L (thφ G (x3 G)) thε c.t d.t
  isGen := isGen_tensGen L.L M.L (thφ G (x3 G)) thε c.t d.t c.isGen d.isGen
  face := fun i => corr_of_val hL fun y J hJ => by
    have e₁ := (val_pull (good₁ hJ) _ _ _).symm.trans ((val_corr (good₁ hJ) (c.face i) (𝟙 _)).trans (val_one _))
    have e₂ := (val_pull (good₂ hJ) _ _ _).symm.trans ((val_corr (good₂ hJ) (d.face i) (𝟙 _)).trans (val_one _))
    refine (val_pull hJ _ _ _).trans ((val_tensGen c.t d.t _ hJ).trans (Eq.trans ?_ (val_one _).symm))
    exact (congrArg₂ (· * ·) e₁ e₂).trans (_root_.mul_one _)
  cubeSymmetric_swap_first := corr_of_val hL fun y J hJ => by
    have e₁ := (val_corr (good₁ hJ) c.cubeSymmetric_swap_first (𝟙 _)).trans (val_pull (good₁ hJ) _ _ _)
    have e₂ := (val_corr (good₂ hJ) d.cubeSymmetric_swap_first (𝟙 _)).trans (val_pull (good₂ hJ) _ _ _)
    exact (val_tensGen c.t d.t _ hJ).trans ((congrArg₂ (· * ·) e₁ e₂).trans
      ((val_pull hJ _ _ _).trans (val_tensGen c.t d.t _ hJ)).symm)
  cubeSymmetric_swap_last := corr_of_val hL fun y J hJ => by
    have e₁ := (val_corr (good₁ hJ) c.cubeSymmetric_swap_last (𝟙 _)).trans (val_pull (good₁ hJ) _ _ _)
    have e₂ := (val_corr (good₂ hJ) d.cubeSymmetric_swap_last (𝟙 _)).trans (val_pull (good₂ hJ) _ _ _)
    exact (val_tensGen c.t d.t _ hJ).trans ((congrArg₂ (· * ·) e₁ e₂).trans
      ((val_pull hJ _ _ _).trans (val_tensGen c.t d.t _ hJ)).symm)
  cocycle := corr_of_val hL fun y J hJ => by
    have e₁ := (val_mul (good₁ hJ) _ _ _).symm.trans ((val_corr (good₁ hJ) c.cocycle (𝟙 _)).trans
      (val_mul (good₁ hJ) _ _ _))
    have e₂ := (val_mul (good₂ hJ) _ _ _).symm.trans ((val_corr (good₂ hJ) d.cocycle (𝟙 _)).trans
      (val_mul (good₂ hJ) _ _ _))
    have v : ∀ a : (G4 G).left ⟶ (G3 G).left,
        val (LB.pullGen (tensLB L.L M.L) (thφ G (x3 G)) thε (tensGen L.L M.L (thφ G (x3 G)) thε c.t d.t) a) (𝟙 _) y J =
        val (LB.pullGen L.L (thφ G (x3 G)) thε c.t a) (𝟙 _) y (fun ψ => (J ψ).1) *
          val (LB.pullGen M.L (thφ G (x3 G)) thε d.t a) (𝟙 _) y (fun ψ => (J ψ).2) := fun a =>
      (val_pull hJ _ _ _).trans ((val_tensGen c.t d.t _ hJ).trans
        (congrArg₂ (· * ·) (val_pull (good₁ hJ) _ _ _) (val_pull (good₂ hJ) _ _ _)).symm)
    refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _) (v _))).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v _) (v _))).symm)
    exact (_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg₂ (· * ·) e₁ e₂).trans (_root_.mul_mul_mul_comm _ _ _ _))

end Cub

section Ext

variable {X X₁ X₂ Y Y₁ Y₂ Z : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂)
  {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
  (h₁ : Y ⟶ Y₁) (φ₁ : K → (Y₁ ⟶ X₁)) (e₁ : ∀ k, ψ k ≫ f₁ = h₁ ≫ φ₁ k) (t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε))
  (h₂ : Y ⟶ Y₂) (φ₂ : K → (Y₂ ⟶ X₂)) (e₂ : ∀ k, ψ k ≫ f₂ = h₂ ≫ φ₂ k) (t₂ : LB.Gen (LB.LinComb L₂ φ₂ ε))

def extGen : LB.Gen (LB.LinComb (extLB L₁ L₂ f₁ f₂) ψ ε) :=
  tensGen (L₁.pull f₁) (L₂.pull f₂) ψ ε (GeneratorPullback.pullAlong L₁ f₁ h₁ φ₁ ε ψ e₁ t₁) (GeneratorPullback.pullAlong L₂ f₂ h₂ φ₂ ε ψ e₂ t₂)

theorem isGen_extGen (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) :
    (extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂).IsGen :=
  isGen_tensGen _ _ _ _ _ _ (LBxP.isGen_pullAlong _ _ _ _ _ _ _ _ ht₁) (LBxP.isGen_pullAlong _ _ _ _ _ _ _ _ ht₂)

theorem gm_pullAlong (r : Z ⟶ Y) (z : Z) (jj : K → (L₁.pull f₁).ι) (h : r z ∈ LB.wchart (L₁.pull f₁) ψ jj) :
    gm r z (LB.wchart (L₁.pull f₁) ψ jj) ((GeneratorPullback.pullAlong L₁ f₁ h₁ φ₁ ε ψ e₁ t₁).s jj) =
      gm (r ≫ h₁) z (LB.wchart L₁ φ₁ (fun k => jj k ⟨⟩)) (t₁.s (fun k => jj k ⟨⟩)) :=
  (gm_res r z _ h _).trans (gm_pull r h₁ z _ (GeneratorPullback.pullAlong_le L₁ f₁ h₁ φ₁ ψ e₁ jj h) _)

theorem gm_extGen (r : Z ⟶ Y) (z : Z) (jj : K → (extLB L₁ L₂ f₁ f₂).ι)
    (h : r z ∈ LB.wchart (extLB L₁ L₂ f₁ f₂) ψ jj) :
    gm r z (LB.wchart (extLB L₁ L₂ f₁ f₂) ψ jj) ((extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂).s jj) =
      gm (r ≫ h₁) z (LB.wchart L₁ φ₁ (fun k => (jj k).1 ⟨⟩)) (t₁.s (fun k => (jj k).1 ⟨⟩)) *
        gm (r ≫ h₂) z (LB.wchart L₂ φ₂ (fun k => (jj k).2 ⟨⟩)) (t₂.s (fun k => (jj k).2 ⟨⟩)) :=
  (gm_tensGen _ _ _ _ _ _ r z jj h).trans (congrArg₂ (· * ·)
    (gm_pullAlong L₁ f₁ ψ ε h₁ φ₁ e₁ t₁ r z _ (tens_le₁ _ _ ψ jj h))
    (gm_pullAlong L₂ f₂ ψ ε h₂ φ₂ e₂ t₂ r z _ (tens_le₂ _ _ ψ jj h)))

def chg (z : Z) (I : (Z ⟶ X) → (L₁.pull f₁).ι) (J : (Z ⟶ X₁) → L₁.ι) (p : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm (p ≫ f₁) z (L₁.U (I p ⟨⟩) ⊓ L₁.U (J (p ≫ f₁))) (L₁.g (I p ⟨⟩) (J (p ≫ f₁)))

theorem val_pullAlong (ht₁ : t₁.IsGen) (r : Z ⟶ Y) {z : Z} {I : (Z ⟶ X) → (L₁.pull f₁).ι}
    (hI : Good (L₁.pull f₁) z I) {J : (Z ⟶ X₁) → L₁.ι} (hJ : Good L₁ z J) :
    val (GeneratorPullback.pullAlong L₁ f₁ h₁ φ₁ ε ψ e₁ t₁) r z I =
      (∏ k, chg L₁ f₁ z I J (r ≫ ψ k) ^ ε k) * val t₁ (r ≫ h₁) z J := by
  refine (gm_pullAlong L₁ f₁ ψ ε h₁ φ₁ e₁ t₁ r z _ (hI.mem ψ r)).trans ?_
  refine (gen_trans ht₁ (r ≫ h₁) z (GeneratorPullback.pullAlong_le L₁ f₁ h₁ φ₁ ψ e₁ _ (hI.mem ψ r)) (hJ.mem φ₁ (r ≫ h₁))).trans
    (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) rfl)
  have e : (r ≫ h₁) ≫ φ₁ k = (r ≫ ψ k) ≫ f₁ := by rw [Category.assoc, Category.assoc, e₁]
  unfold chg
  rw [← e]

def chg₂ (z : Z) (J : (Z ⟶ X) → (extLB L₁ L₂ f₁ f₂).ι) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι) (p : Z ⟶ X) :
    (Z.presheaf.stalk z)ˣ :=
  chg L₁ f₁ z (fun q => (J q).1) J₁ p * chg L₂ f₂ z (fun q => (J q).2) J₂ p

theorem val_extGen (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → (extLB L₁ L₂ f₁ f₂).ι}
    (hJ : Good (extLB L₁ L₂ f₁ f₂) z J) {J₁ : (Z ⟶ X₁) → L₁.ι} (hJ₁ : Good L₁ z J₁) {J₂ : (Z ⟶ X₂) → L₂.ι}
    (hJ₂ : Good L₂ z J₂) :
    val (extGen L₁ L₂ f₁ f₂ ψ ε h₁ φ₁ e₁ t₁ h₂ φ₂ e₂ t₂) r z J =
      (∏ k, chg₂ L₁ L₂ f₁ f₂ z J J₁ J₂ (r ≫ ψ k) ^ ε k) * (val t₁ (r ≫ h₁) z J₁ * val t₂ (r ≫ h₂) z J₂) := by
  refine (val_tensGen _ _ r hJ).trans ((congrArg₂ (· * ·)
    (val_pullAlong L₁ f₁ ψ ε h₁ φ₁ e₁ t₁ ht₁ r (good₁ hJ) hJ₁)
    (val_pullAlong L₂ f₂ ψ ε h₂ φ₂ e₂ t₂ ht₂ r (good₂ hJ) hJ₂)).trans ((_root_.mul_mul_mul_comm _ _ _ _).trans
      (congrArg₂ (· * ·) ?_ rfl)))
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => (mul_zpow _ _ _).symm

end Ext

section At

variable {X X₁ X₂ Y Z : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) (p : Y ⟶ X) (n : ℤ)
  (p₁ : Y ⟶ X₁) (e₁ : p ≫ f₁ = p₁) (t₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p₁) (fun _ => n)))
  (p₂ : Y ⟶ X₂) (e₂ : p ≫ f₂ = p₂) (t₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p₂) (fun _ => n)))

def extAt : LB.Gen (LB.LinComb (extLB L₁ L₂ f₁ f₂) (K := PUnit) (fun _ => p) (fun _ => n)) :=
  extGen L₁ L₂ f₁ f₂ (fun _ => p) (fun _ => n) (𝟙 Y) (fun _ => p₁) (fun _ => e₁.trans (Category.id_comp _).symm) t₁
    (𝟙 Y) (fun _ => p₂) (fun _ => e₂.trans (Category.id_comp _).symm) t₂

theorem isGen_extAt (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) : (extAt L₁ L₂ f₁ f₂ p n p₁ e₁ t₁ p₂ e₂ t₂).IsGen :=
  isGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht₁ ht₂

theorem gm_extAt (r : Z ⟶ Y) (z : Z) (q : (extLB L₁ L₂ f₁ f₂).ι) (h : p (r z) ∈ (extLB L₁ L₂ f₁ f₂).U q) :
    gm r z (LB.wchart (extLB L₁ L₂ f₁ f₂) (fun _ : PUnit => p) (fun _ => q))
        ((extAt L₁ L₂ f₁ f₂ p n p₁ e₁ t₁ p₂ e₂ t₂).s (fun _ => q)) =
      gm r z (LB.wchart L₁ (fun _ : PUnit => p₁) (fun _ => q.1 ⟨⟩)) (t₁.s (fun _ => q.1 ⟨⟩)) *
        gm r z (LB.wchart L₂ (fun _ : PUnit => p₂) (fun _ => q.2 ⟨⟩)) (t₂.s (fun _ => q.2 ⟨⟩)) := by
  refine (gm_extGen L₁ L₂ f₁ f₂ _ _ _ _ _ _ _ _ _ _ r z (fun _ => q) (Set.mem_iInter.2 fun _ => h)).trans ?_
  rw [Category.comp_id]

theorem val_extAt (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → (extLB L₁ L₂ f₁ f₂).ι}
    (hJ : Good (extLB L₁ L₂ f₁ f₂) z J) {J₁ : (Z ⟶ X₁) → L₁.ι} (hJ₁ : Good L₁ z J₁) {J₂ : (Z ⟶ X₂) → L₂.ι}
    (hJ₂ : Good L₂ z J₂) :
    val (extAt L₁ L₂ f₁ f₂ p n p₁ e₁ t₁ p₂ e₂ t₂) r z J =
      chg₂ L₁ L₂ f₁ f₂ z J J₁ J₂ (r ≫ p) ^ n * (val t₁ r z J₁ * val t₂ r z J₂) := by
  refine (val_extGen L₁ L₂ f₁ f₂ _ _ _ _ _ _ _ _ _ _ ht₁ ht₂ r hJ hJ₁ hJ₂).trans ?_
  rw [Category.comp_id, Fintype.prod_unique]

theorem corr_self (t : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p₁) (fun _ => n))) :
    LB.Gen.Corr L₁ _ _ _ _ t t := by
  intro j j' _ _ c
  obtain rfl : j = j' := funext fun k => c k k rfl
  rfl

theorem mapsAt_extAt (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) :
    ∃ b₁ b₂, MapsAt₂ (CubePf.idIsoL (extLB L₁ L₂ f₁ f₂)) p n (extAt L₁ L₂ f₁ f₂ p n p₁ e₁ t₁ p₂ e₂ t₂) b₁ b₂ ∧
      LB.Gen.Corr L₁ _ _ _ _ b₁ t₁ ∧ LB.Gen.Corr L₂ _ _ _ _ b₂ t₂ := by
  subst e₁ e₂
  refine ⟨t₁, t₂, fun j₁ j₂ jL => unit_ext fun y hy => ?_, corr_self _ _ _ _, corr_self _ _ _ _⟩
  have h2 : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (extLB L₁ L₂ f₁ f₂) (fun _ : PUnit => p) (fun _ => jL) :=
    Set.mem_iInter.2 fun _ => hy.2
  have h1 : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (extLB L₁ L₂ f₁ f₂) (fun _ : PUnit => p) (fun _ => extIdx j₁ j₂) :=
    Set.mem_iInter.2 fun _ => hy.1
  have key := gen_trans (isGen_extAt L₁ L₂ f₁ f₂ p n _ rfl t₁ _ rfl t₂ ht₁ ht₂) (𝟙 Y) y h1 h2
  have k2 := gm_extAt L₁ L₂ f₁ f₂ p n _ rfl t₁ _ rfl t₂ (𝟙 Y) y (extIdx j₁ j₂) hy.1
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hy _) (gm_res _ y _ hy _))).trans
    (k2.symm.trans (key.trans (Eq.symm ?_)))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _))
  unfold trF
  rw [Fintype.prod_unique]
  exact (map_zpow _ _ _).trans (congrArg (· ^ n) (gm_pull (𝟙 Y) p y _ hy _))

end At

section Points

variable {S : Scheme.{0}} {A A₁ A₂ : Over S} (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsIso (lift a₁ a₂)]

def pairPt {T : Over S} (x₁ : T ⟶ A₁) (x₂ : T ⟶ A₂) : T ⟶ A := lift x₁ x₂ ≫ inv (lift a₁ a₂)

theorem pairPt_lift {T : Over S} (x₁ : T ⟶ A₁) (x₂ : T ⟶ A₂) : pairPt a₁ a₂ x₁ x₂ ≫ lift a₁ a₂ = lift x₁ x₂ := by
  rw [pairPt, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem pairPt_fst {T : Over S} (x₁ : T ⟶ A₁) (x₂ : T ⟶ A₂) : pairPt a₁ a₂ x₁ x₂ ≫ a₁ = x₁ := by
  have := congrArg (· ≫ fst A₁ A₂) (pairPt_lift a₁ a₂ x₁ x₂)
  simpa using this

theorem pairPt_snd {T : Over S} (x₁ : T ⟶ A₁) (x₂ : T ⟶ A₂) : pairPt a₁ a₂ x₁ x₂ ≫ a₂ = x₂ := by
  have := congrArg (· ≫ snd A₁ A₂) (pairPt_lift a₁ a₂ x₁ x₂)
  simpa using this

theorem pt_ext {T : Over S} {x y : T ⟶ A} (h₁ : x ≫ a₁ = y ≫ a₁) (h₂ : x ≫ a₂ = y ≫ a₂) : x = y := by
  rw [← cancel_mono (lift a₁ a₂), comp_lift, comp_lift, h₁, h₂]

end Points

section Hom

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (a : A ⟶ B) [IsMonHom a]

theorem padd_comp {T : Over S} (x y : T ⟶ A) : padd A x y ≫ a = padd B (x ≫ a) (y ≫ a) := by
  rw [padd, padd, Category.assoc, IsMonHom.mul_hom, lift_map_assoc]

theorem eSec_comp : eSec A ≫ a.left = eSec B := by
  rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]

theorem inv_comp (k : Fin 2) :
    (![(ι[A]).left, 𝟙 A.left] : Fin 2 → (A.left ⟶ A.left)) k ≫ a.left =
      a.left ≫ (![(ι[B]).left, 𝟙 B.left] : Fin 2 → (B.left ⟶ B.left)) k := by
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
  · simp

theorem prod_sym {Z : Scheme.{0}} (r : Z ⟶ A.left) {U : Type} [CommGroup U] (f : (Z ⟶ A.left) → U) :
    ∏ k : Fin 2, f (r ≫ (![(ι[A]).left, 𝟙 A.left] : Fin 2 → (A.left ⟶ A.left)) k) ^ (![1, -1] : Fin 2 → ℤ) k =
      f (r ≫ (ι[A]).left) * (f r)⁻¹ := by
  simp [Fin.prod_univ_two]

theorem groupObj_lift3_comp_tensorCube_monHom {T : Over S} (x y z : T ⟶ A) :
    (lift x (lift y z)).left ≫ (a ⊗ₘ a ⊗ₘ a).left = (lift (x ≫ a) (lift (y ≫ a) (z ≫ a))).left := by
  rw [← Over.comp_left, lift_map, lift_map]

end Hom

abbrev withL {S : Scheme.{0}} (P : PolAV S) (L : LB P.A.left) (h : P.L = L) : PolAV S where
  A := P.A
  grp := P.grp
  isAb := P.isAb
  g := P.g
  smoothDim := P.smoothDim
  L := L
  isLB := h ▸ P.isLB
  rigid := h ▸ P.rigid
  sym := h ▸ P.sym
  ample := h ▸ P.ample
  ktriv := h ▸ P.ktriv

section Deg

variable {R : Type} [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (P : PolAV (Spec (CommRingCat.of R)))
  (a₁ : P.A ⟶ D₁.P.A) (a₂ : P.A ⟶ D₂.P.A) [IsMonHom a₁] [IsMonHom a₂]

abbrev sL : LB P.A.left := extLB D₁.P.L D₂.P.L a₁.left a₂.left

def sRig : LB.Gen ((sL D₁ D₂ P a₁ a₂).pull (eSec P.A)) :=
  extAt D₁.P.L D₂.P.L a₁.left a₂.left (eSec P.A) 1 _ (eSec_comp a₁) D₁.rig _ (eSec_comp a₂) D₂.rig

theorem sRig_gen : (sRig D₁ D₂ P a₁ a₂).IsGen := isGen_extAt _ _ _ _ _ _ _ _ _ _ _ _ D₁.rig_gen D₂.rig_gen

def sSym : LB.Gen (LB.LinComb (sL D₁ D₂ P a₁ a₂) (K := Fin 2) ![(ι[P.A]).left, 𝟙 P.A.left] ![1, -1]) :=
  extGen D₁.P.L D₂.P.L a₁.left a₂.left _ _ a₁.left _ (inv_comp a₁) D₁.sym a₂.left _ (inv_comp a₂) D₂.sym

theorem sSym_gen : (sSym D₁ D₂ P a₁ a₂).IsGen := isGen_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ D₁.sym_gen D₂.sym_gen

theorem val_sSym {Z : Scheme.{0}} (r : Z ⟶ P.A.left) {z : Z} {J} (hJ : Good (sL D₁ D₂ P a₁ a₂) z J)
    {J₁} (hJ₁ : Good D₁.P.L z J₁) {J₂} (hJ₂ : Good D₂.P.L z J₂) :
    val (sSym D₁ D₂ P a₁ a₂) r z J =
      chg₂ D₁.P.L D₂.P.L a₁.left a₂.left z J J₁ J₂ (r ≫ (ι[P.A]).left) *
        (chg₂ D₁.P.L D₂.P.L a₁.left a₂.left z J J₁ J₂ r)⁻¹ *
        (val D₁.sym (r ≫ a₁.left) z J₁ * val D₂.sym (r ≫ a₂.left) z J₂) :=
  (val_extGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ D₁.sym_gen D₂.sym_gen r hJ hJ₁ hJ₂).trans
    (congrArg₂ (· * ·) (prod_sym r _) rfl)

theorem val_sym_zero (D : DegPre R) {y} {J} (hJ : Good D.P.L y J) : val D.sym (eSec D.P.A) y J = 1 := by
  have v := val_corr hJ D.sym_rig (𝟙 _)
  rwa [val_pull hJ, Category.id_comp, val_one] at v

theorem sSym_rig (hL : (sL D₁ D₂ P a₁ a₂).IsLB) : LB.Gen.Corr (sL D₁ D₂ P a₁ a₂) _ _ _ _
    (LB.pullGen (sL D₁ D₂ P a₁ a₂) _ _ (sSym D₁ D₂ P a₁ a₂) (eSec P.A)) (LB.oneGen (sL D₁ D₂ P a₁ a₂)) := by
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have o : eSec P.A ≫ (ι[P.A]).left = eSec P.A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[P.A] ≫ ι[P.A] = η[P.A])
  rw [val_pull hJ, Category.id_comp, val_one, val_sSym D₁ D₂ P a₁ a₂ _ hJ hJ₁ hJ₂, o, mul_inv_cancel,
    eSec_comp, eSec_comp, val_sym_zero D₁ hJ₁, val_sym_zero D₂ hJ₂, _root_.mul_one, _root_.mul_one]

def pullCub (D : DegPre R) (a : P.A ⟶ D.P.A) [IsMonHom a] :=
  CubePf.cubical (CubeMap.ofHom a) ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ D.cub (LB.isLB_pull D.P.isLB _)
    (LBxP.isGen_pullAlong D.P.L a.left (𝟙 _) (fun _ : PUnit => eSec D.P.A) (fun _ => 1)
      (fun _ => eSec P.A) (fun _ => (CubeMap.ofHom a).e_comm) D.rig D.rig_gen)

def sCub (hL : (sL D₁ D₂ P a₁ a₂).IsLB) :
    CubicalStr P.A ⟨sL D₁ D₂ P a₁ a₂, sRig D₁ D₂ P a₁ a₂, hL, sRig_gen D₁ D₂ P a₁ a₂⟩ :=
  tensCub (pullCub P D₁ a₁) (pullCub P D₂ a₂) _ hL _

theorem cubV_sCub (hL : (sL D₁ D₂ P a₁ a₂).IsLB) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J}
    (hJ : Good (sL D₁ D₂ P a₁ a₂) z J) {J₁} (hJ₁ : Good D₁.P.L z J₁) {J₂} (hJ₂ : Good D₂.P.L z J₂)
    (x x' y : T ⟶ P.A) (h : (T.left ⟶ P.A.left) → (T.left.presheaf.stalk z)ˣ)
    (hh : h = chg₂ D₁.P.L D₂.P.L a₁.left a₂.left z J J₁ J₂) :
    cubV (sCub D₁ D₂ P a₁ a₂ hL) z J x x' y =
      h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : T ⟶ P.A).left)⁻¹ *
      (cubV D₁.cub z J₁ (x ≫ a₁) (x' ≫ a₁) (y ≫ a₁) * cubV D₂.cub z J₂ (x ≫ a₂) (x' ≫ a₂) (y ≫ a₂)) := by
  subst hh
  refine (val_extGen D₁.P.L D₂.P.L a₁.left a₂.left (thφ P.A (x3 P.A)) thε
    (a₁ ⊗ₘ a₁ ⊗ₘ a₁).left (thφ D₁.P.A (x3 D₁.P.A)) (fun I => (CubeMap.ofHom a₁).psum_comm I.down) D₁.cub.t
    (a₂ ⊗ₘ a₂ ⊗ₘ a₂).left (thφ D₂.P.A (x3 D₂.P.A)) (fun I => (CubeMap.ofHom a₂).psum_comm I.down) D₂.cub.t
    D₁.cub.isGen D₂.cub.isGen (lift x (lift x' y)).left hJ hJ₁ hJ₂).trans
    (congrArg₂ (· * ·) (prod_cub x x' y _) ?_)
  rw [groupObj_lift3_comp_tensorCube_monHom, groupObj_lift3_comp_tensorCube_monHom]
  rfl

variable [IsIso (lift a₁ a₂)]

def sC (x : D₁.X × D₂.X) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A := pairPt a₁ a₂ (D₁.c x.1) (D₂.c x.2)

theorem ptK_fst (x : D₁.X × D₂.X) : ptK (sC D₁ D₂ P a₁ a₂ x) ≫ a₁.left = ptK (D₁.c x.1) := by
  rw [← Over.comp_left, Category.assoc, sC, pairPt_fst]

theorem ptK_snd (x : D₁.X × D₂.X) : ptK (sC D₁ D₂ P a₁ a₂ x) ≫ a₂.left = ptK (D₂.c x.2) := by
  rw [← Over.comp_left, Category.assoc, sC, pairPt_snd]

variable (h : P.L = sL D₁ D₂ P a₁ a₂)

def sumPre : DegPre R where
  P := withL P (sL D₁ D₂ P a₁ a₂) h
  rig := sRig D₁ D₂ P a₁ a₂
  rig_gen := sRig_gen D₁ D₂ P a₁ a₂
  cub := sCub D₁ D₂ P a₁ a₂ (withL P _ h).isLB
  sym := sSym D₁ D₂ P a₁ a₂
  sym_gen := sSym_gen D₁ D₂ P a₁ a₂
  sym_rig := sSym_rig D₁ D₂ P a₁ a₂ (withL P _ h).isLB
  X := D₁.X × D₂.X
  c := sC D₁ D₂ P a₁ a₂
  c_add := fun a b => pt_ext a₁ a₂
    (by
      refine Eq.trans ?_ (padd_comp a₁ _ _).symm
      rw [sC, sC, sC, pairPt_fst, pairPt_fst, pairPt_fst]; exact D₁.c_add _ _)
    (by
      refine Eq.trans ?_ (padd_comp a₂ _ _).symm
      rw [sC, sC, sC, pairPt_snd, pairPt_snd, pairPt_snd]; exact D₂.c_add _ _)
  psi := fun x => extAt D₁.P.L D₂.P.L a₁.left a₂.left _ (-1) _ (ptK_fst D₁ D₂ P a₁ a₂ x) (D₁.psi x.1)
    _ (ptK_snd D₁ D₂ P a₁ a₂ x) (D₂.psi x.2)
  psi_gen := fun x => isGen_extAt _ _ _ _ _ _ _ _ _ _ _ _ (D₁.psi_gen x.1) (D₂.psi_gen x.2)

theorem isSumDeg_sumPre : IsSumDeg (sumPre D₁ D₂ P a₁ a₂ h) D₁ D₂ a₁ a₂ (AddMonoidHom.fst D₁.X D₂.X)
    (AddMonoidHom.snd D₁.X D₂.X) where
  hom₁ := inferInstanceAs (IsMonHom a₁)
  hom₂ := inferInstanceAs (IsMonHom a₂)
  lim := inferInstanceAs (IsIso (lift a₁ a₂))
  xsum := Function.bijective_id
  c_pr₁ := fun _ => pairPt_fst a₁ a₂ _ _
  c_pr₂ := fun _ => pairPt_snd a₁ a₂ _ _
  w := ⟨CubePf.idIsoL (sL D₁ D₂ P a₁ a₂), CubePf.idIsoL_isGen (withL P _ h).isLB,
    mapsAt_extAt D₁.P.L D₂.P.L a₁.left a₂.left (eSec P.A) 1 _ (eSec_comp a₁) D₁.rig _ (eSec_comp a₂) D₂.rig
      D₁.rig_gen D₂.rig_gen,
    fun x => mapsAt_extAt D₁.P.L D₂.P.L a₁.left a₂.left _ (-1) _ (ptK_fst D₁ D₂ P a₁ a₂ x) (D₁.psi x.1)
      _ (ptK_snd D₁ D₂ P a₁ a₂ x) (D₂.psi x.2) (D₁.psi_gen x.1) (D₂.psi_gen x.2)⟩

theorem val_psi (x : D₁.X × D₂.X) {y : (TK R).left} {J} (hJ : Good (sL D₁ D₂ P a₁ a₂) y J)
    {J₁} (hJ₁ : Good D₁.P.L y J₁) {J₂} (hJ₂ : Good D₂.P.L y J₂) :
    val ((sumPre D₁ D₂ P a₁ a₂ h).psi x) (𝟙 _) y J =
      (chg₂ D₁.P.L D₂.P.L a₁.left a₂.left y J J₁ J₂ (ptK (sC D₁ D₂ P a₁ a₂ x)))⁻¹ *
        (val (D₁.psi x.1) (𝟙 _) y J₁ * val (D₂.psi x.2) (𝟙 _) y J₂) := by
  refine (val_extAt D₁.P.L D₂.P.L a₁.left a₂.left _ (-1) _ (ptK_fst D₁ D₂ P a₁ a₂ x) (D₁.psi x.1)
      _ (ptK_snd D₁ D₂ P a₁ a₂ x) (D₂.psi x.2) (D₁.psi_gen x.1) (D₂.psi_gen x.2) (𝟙 _) hJ hJ₁ hJ₂).trans ?_
  rw [Category.id_comp, zpow_neg_one]

theorem val_rigK {y : (TK R).left} {J} (hJ : Good (sL D₁ D₂ P a₁ a₂) y J)
    {J₁} (hJ₁ : Good D₁.P.L y J₁) {J₂} (hJ₂ : Good D₂.P.L y J₂) :
    val (sumPre D₁ D₂ P a₁ a₂ h).rigK (𝟙 _) y J =
      chg₂ D₁.P.L D₂.P.L a₁.left a₂.left y J J₁ J₂ (1 : TK R ⟶ P.A).left *
        (val D₁.rigK (𝟙 _) y J₁ * val D₂.rigK (𝟙 _) y J₂) := by
  refine (val_pull hJ _ _ _).trans ((val_extAt D₁.P.L D₂.P.L a₁.left a₂.left (eSec P.A) 1 _ (eSec_comp a₁) D₁.rig _
    (eSec_comp a₂) D₂.rig D₁.rig_gen D₂.rig_gen _ hJ hJ₁ hJ₂).trans (congrArg₂ (· * ·) ?_
      (congrArg₂ (· * ·) (val_pull hJ₁ _ _ _).symm (val_pull hJ₂ _ _ _).symm)))
  rw [Category.id_comp, zpow_one]
  rfl

theorem psiEven (hE₁ : D₁.PsiEven) (hE₂ : D₂.PsiEven) : (sumPre D₁ D₂ P a₁ a₂ h).PsiEven := by
  intro (x : D₁.X × D₂.X)
  refine corr_of_val (sumPre D₁ D₂ P a₁ a₂ h).P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have n : ptK (sC D₁ D₂ P a₁ a₂ (-x)) = ptK (sC D₁ D₂ P a₁ a₂ x) ≫ (ι[P.A]).left := by
    have := PsiEvenPull.c_neg (sumPre D₁ D₂ P a₁ a₂ h) x
    exact (congrArg (fun m => ptK m) this).trans (Category.assoc (jK R) _ _).symm
  have e : ∀ (D : DegPre R), D.PsiEven → ∀ (χ : D.X) {I}, Good D.P.L y I →
      val (D.psi (-χ)) (𝟙 _) y I * val D.sym (ptK (D.c χ)) y I = val (D.psi χ) (𝟙 _) y I := fun D hE χ I hI => by
    have := val_corr hI (hE χ) (𝟙 _)
    rwa [val_mul hI, val_pull hI, Category.id_comp] at this
  have s := val_sSym D₁ D₂ P a₁ a₂ (ptK (sC D₁ D₂ P a₁ a₂ x)) hJ hJ₁ hJ₂
  rw [← n, ptK_fst, ptK_snd] at s
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_psi D₁ D₂ P a₁ a₂ h (-x) hJ hJ₁ hJ₂)
    ((val_pull hJ _ _ _).trans ((congrArg (fun m => val (sSym D₁ D₂ P a₁ a₂) m y J) (Category.id_comp _)).trans
      s)))).trans (Eq.trans ?_ (val_psi D₁ D₂ P a₁ a₂ h x hJ hJ₁ hJ₂).symm)
  rw [← e D₁ hE₁ x.1 hJ₁, ← e D₂ hE₂ x.2 hJ₂, Prod.fst_neg, Prod.snd_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem val_tau (p q : D₁.X × D₂.X) {y : (TK R).left} {J} (hJ : Good (sL D₁ D₂ P a₁ a₂) y J)
    {J₁} (hJ₁ : Good D₁.P.L y J₁) {J₂} (hJ₂ : Good D₂.P.L y J₂)
    (f : ((TK R).left ⟶ P.A.left) → ((TK R).left.presheaf.stalk y)ˣ)
    (hf : f = chg₂ D₁.P.L D₂.P.L a₁.left a₂.left y J J₁ J₂) (u v : TK R ⟶ P.A)
    (hu : u = toUnit _ ≫ sC D₁ D₂ P a₁ a₂ p) (hv : v = toUnit _ ≫ sC D₁ D₂ P a₁ a₂ q) :
    val ((sumPre D₁ D₂ P a₁ a₂ h).tau p q) (𝟙 _) y J =
      (f (u * v).left)⁻¹ * f u.left * f v.left * (f (1 : TK R ⟶ P.A).left)⁻¹ *
        (val (D₁.tau p.1 q.1) (𝟙 _) y J₁ * val (D₂.tau p.2 q.2) (𝟙 _) y J₂) := by
  have a : ptK (sC D₁ D₂ P a₁ a₂ (p + q)) = (u * v).left := by
    subst hu hv
    exact congrArg (fun m => m.left) (cPoint_add (sumPre D₁ D₂ P a₁ a₂ h) (TK R) p q)
  have b₃ := val_psi D₁ D₂ P a₁ a₂ h (p + q) hJ hJ₁ hJ₂
  rw [a, Prod.fst_add, Prod.snd_add, ← hf] at b₃
  have b₁ := val_psi D₁ D₂ P a₁ a₂ h p hJ hJ₁ hJ₂
  have b₂ := val_psi D₁ D₂ P a₁ a₂ h q hJ hJ₁ hJ₂
  have b₀ := val_rigK D₁ D₂ P a₁ a₂ h hJ hJ₁ hJ₂
  rw [show ptK (sC D₁ D₂ P a₁ a₂ p) = u.left by rw [hu], ← hf] at b₁
  rw [show ptK (sC D₁ D₂ P a₁ a₂ q) = v.left by rw [hv], ← hf] at b₂
  rw [← hf] at b₀
  refine (TauBalBox.tau_val (sumPre D₁ D₂ P a₁ a₂ h) hJ p q (𝟙 _)).trans ((congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) b₃ (congrArg (·⁻¹) b₁)) (congrArg (·⁻¹) b₂)) (congrArg (·⁻¹) b₀)).trans ?_)
  rw [TauBalBox.tau_val D₁ hJ₁, TauBalBox.tau_val D₂ hJ₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem tauBimult (hB₁ : D₁.TauBimult) (hB₂ : D₂.TauBimult) : (sumPre D₁ D₂ P a₁ a₂ h).TauBimult := by
  intro (a : D₁.X × D₂.X) (a' : D₁.X × D₂.X) (b : D₁.X × D₂.X)
  refine corr_of_val (sumPre D₁ D₂ P a₁ a₂ h).P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  obtain ⟨f, hf⟩ : ∃ f, f = chg₂ D₁.P.L D₂.P.L a₁.left a₂.left y J J₁ J₂ := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : TK R ⟶ P.A, u = toUnit _ ≫ sC D₁ D₂ P a₁ a₂ a := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u : TK R ⟶ P.A, u = toUnit _ ≫ sC D₁ D₂ P a₁ a₂ a' := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ u : TK R ⟶ P.A, u = toUnit _ ≫ sC D₁ D₂ P a₁ a₂ b := ⟨_, rfl⟩
  have huu : u * u' = toUnit _ ≫ sC D₁ D₂ P a₁ a₂ (a + a') := by
    subst hu hu'
    exact (cPoint_add (sumPre D₁ D₂ P a₁ a₂ h) (TK R) a a').symm
  have t₁ := val_tau D₁ D₂ P a₁ a₂ h (a + a') b hJ hJ₁ hJ₂ f hf _ _ huu hv
  have t₂ := val_tau D₁ D₂ P a₁ a₂ h a b hJ hJ₁ hJ₂ f hf _ _ hu hv
  have t₃ := val_tau D₁ D₂ P a₁ a₂ h a' b hJ hJ₁ hJ₂ f hf _ _ hu' hv
  have key := cubV_sCub D₁ D₂ P a₁ a₂ (withL P _ h).isLB hJ hJ₁ hJ₂ u u' v f hf
  have e : ∀ (D : DegPre R), D.TauBimult → ∀ (χ χ' ω : D.X) {I}, Good D.P.L y I →
      cubV D.cub y I (cP D (TK R) χ) (cP D (TK R) χ') (cP D (TK R) ω) = (val (D.tau (χ + χ') ω) (𝟙 _) y I)⁻¹ *
        (val (D.tau χ ω) (𝟙 _) y I * val (D.tau χ' ω) (𝟙 _) y I) := fun D hB χ χ' ω I hI =>
    eq_inv_mul_of_mul_eq ((TauBimultBox.val_lhs D hI _ _ _).symm.trans
      ((val_corr hI (hB χ χ' ω) (𝟙 _)).trans (val_mul hI _ _ _)))
  have f₁ : ∀ (w : TK R ⟶ P.A) (x : D₁.X × D₂.X), w = toUnit _ ≫ sC D₁ D₂ P a₁ a₂ x →
      w ≫ a₁ = cP D₁ (TK R) x.1 := fun w x hw => by rw [hw, Category.assoc, sC, pairPt_fst]; rfl
  have f₂ : ∀ (w : TK R ⟶ P.A) (x : D₁.X × D₂.X), w = toUnit _ ≫ sC D₁ D₂ P a₁ a₂ x →
      w ≫ a₂ = cP D₂ (TK R) x.2 := fun w x hw => by rw [hw, Category.assoc, sC, pairPt_snd]; rfl
  rw [f₁ u a hu, f₁ u' a' hu', f₁ v b hv, f₂ u a hu, f₂ u' a' hu', f₂ v b hv, e D₁ hB₁ _ _ _ hJ₁,
    e D₂ hB₂ _ _ _ hJ₂] at key
  have k' : cubV (sumPre D₁ D₂ P a₁ a₂ h).cub y J (cP (sumPre D₁ D₂ P a₁ a₂ h) (TK R) a)
      (cP (sumPre D₁ D₂ P a₁ a₂ h) (TK R) a') (cP (sumPre D₁ D₂ P a₁ a₂ h) (TK R) b) =
      cubV (sCub D₁ D₂ P a₁ a₂ (withL P _ h).isLB) y J u u' v := by
    subst hu hu' hv; rfl
  refine ((TauBimultBox.val_lhs (sumPre D₁ D₂ P a₁ a₂ h) hJ a a' b).trans
    (congrArg₂ (· * ·) t₁ (k'.trans key))).trans
    (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) t₂ t₃)).symm)
  rw [Prod.fst_add, Prod.snd_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem psiIn_mul (x : D₁.X × D₂.X) (I₁ I₂ : Ideal R) (H₁ : D₁.PsiIn x.1 I₁) (H₂ : D₂.PsiIn x.2 I₂) :
    (sumPre D₁ D₂ P a₁ a₂ h).PsiIn x (I₁ * I₂) := by
  refine PsiInPow.psiIn_of_gs (sumPre D₁ D₂ P a₁ a₂ h) x _ fun q V hV hle z hz => ?_
  have c₁ : (sC D₁ D₂ P a₁ a₂ x).left ≫ a₁.left = (D₁.c x.1).left := by
    rw [← Over.comp_left, sC, pairPt_fst]
  have c₂ : (sC D₁ D₂ P a₁ a₂ x).left ≫ a₂.left = (D₂.c x.2).left := by
    rw [← Over.comp_left, sC, pairPt_snd]
  obtain ⟨r₁, hr₁, e₁⟩ := PsiInPow.gs_of_psiIn D₁ _ _ H₁ (q.1 ⟨⟩) V hV (fun y hy =>
    (congrArg (fun m => m y ∈ D₁.P.L.U (q.1 ⟨⟩)) c₁).mp (Set.mem_iInter.1 (hle hy).1 ⟨⟩)) z hz
  obtain ⟨r₂, hr₂, e₂⟩ := PsiInPow.gs_of_psiIn D₂ _ _ H₂ (q.2 ⟨⟩) V hV (fun y hy =>
    (congrArg (fun m => m y ∈ D₂.P.L.U (q.2 ⟨⟩)) c₂).mp (Set.mem_iInter.1 (hle hy).2 ⟨⟩)) z hz
  refine ⟨r₁ * r₂, by rw [Ideal.map_mul]; exact Ideal.mul_mem_mul hr₁ hr₂, ?_⟩
  refine (gs_mul _ _ _ hz _ _).trans ((congrArg₂ (· * ·) e₁ e₂).trans ((Units.val_mul _ _).symm.trans
    (congrArg Units.val (Eq.symm ?_))))
  exact gm_extAt D₁.P.L D₂.P.L a₁.left a₂.left _ (-1) _ (ptK_fst D₁ D₂ P a₁ a₂ x) (D₁.psi x.1)
      _ (ptK_snd D₁ D₂ P a₁ a₂ x) (D₂.psi x.2) (𝟙 _) z q (hle hz)

end Deg

theorem exists_sum : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I),
    ∃ (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A)
      (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X),
      IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ := by
  intro R _ _ I D₁ D₂
  obtain ⟨P, a₁, a₂, hs, h⟩ := GlobalTheory.T.exists_product_principallyPolarised_abelianScheme _ D₁.toPre.P D₂.toPre.P
  have := hs.hom₁
  have := hs.hom₂
  have := hs.lim
  have l : ∀ (x : D₁.toPre.X × D₂.toPre.X) (J : Ideal R), D₁.toPre.PsiIn x.1 J →
      (sumPre D₁.toPre D₂.toPre P a₁ a₂ h).PsiIn x J := fun x J H => by
    have := psiIn_mul D₁.toPre D₂.toPre P a₁ a₂ h x J ⊤ H (PowDegData.psiIn_top D₂ x.2)
    rwa [Ideal.mul_top] at this
  have r : ∀ (x : D₁.toPre.X × D₂.toPre.X) (J : Ideal R), D₂.toPre.PsiIn x.2 J →
      (sumPre D₁.toPre D₂.toPre P a₁ a₂ h).PsiIn x J := fun x J H => by
    have := psiIn_mul D₁.toPre D₂.toPre P a₁ a₂ h x ⊤ J (PowDegData.psiIn_top D₁ x.1) H
    rwa [Ideal.top_mul] at this
  refine ⟨⟨sumPre D₁.toPre D₂.toPre P a₁ a₂ h, psiEven _ _ _ _ _ h D₁.psi_even D₂.psi_even,
    tauBimult _ _ _ _ _ h D₁.tau_bimult D₂.tau_bimult, fun x hx => ?_, fun n => ?_⟩, a₁, a₂, _, _,
    isSumDeg_sumPre D₁.toPre D₂.toPre P a₁ a₂ h⟩
  · by_cases h₁ : x.1 = 0
    · exact r x I (D₂.psi_pos _ fun h₂ => hx (Prod.ext h₁ h₂))
    · exact l x I (D₁.psi_pos _ h₁)
  · exact ((D₁.psi_tendsto n).prod (D₂.psi_tendsto n)).subset fun x hx =>
      ⟨fun H => hx (l x _ H), fun H => hx (r x _ H)⟩

end GlobalTheory.SumDeg
