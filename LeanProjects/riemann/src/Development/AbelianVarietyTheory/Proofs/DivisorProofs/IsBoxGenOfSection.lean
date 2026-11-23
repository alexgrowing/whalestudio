import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductDegenerationDataSum
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFunctional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.ProdUnif

section Vals

variable {X X₁ X₂ Z : Scheme.{0}} {M : LB X} {M₁ : LB X₁} {M₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

def om (w : LB.Iso M (extLB M₁ M₂ f₁ f₂)) (z : Z) (J₁ : (Z ⟶ X₁) → M₁.ι) (J₂ : (Z ⟶ X₂) → M₂.ι)
    (J : (Z ⟶ X) → M.ι) (ψ : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ (ψ ≫ f₁)) (J₂ (ψ ≫ f₂)), J ψ))

variable {K : Type} [Fintype K] {Y Y₁ Y₂ : Scheme.{0}}

def IsBoxGen (w : LB.Iso M (extLB M₁ M₂ f₁ f₂)) {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X₁)} {φ₂ : K → (Y₂ ⟶ X₂)}
    {ε : K → ℤ} (h₁ : Y ⟶ Y₁) (h₂ : Y ⟶ Y₂) (t : LB.Gen (LB.LinComb M φ ε)) (t₁ : LB.Gen (LB.LinComb M₁ φ₁ ε))
    (t₂ : LB.Gen (LB.LinComb M₂ φ₂ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J₁ : (Z ⟶ X₁) → M₁.ι) (J₂ : (Z ⟶ X₂) → M₂.ι) (J : (Z ⟶ X) → M.ι),
    Good M₁ z J₁ → Good M₂ z J₂ → Good M z J →
    (∏ a, om w z J₁ J₂ J (r ≫ φ a) ^ ε a) * val t r z J = val t₁ (r ≫ h₁) z J₁ * val t₂ (r ≫ h₂) z J₂

def IsBoxSec (w : LB.Iso M (extLB M₁ M₂ f₁ f₂)) {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X₁)} {φ₂ : K → (Y₂ ⟶ X₂)}
    {ε : K → ℤ} (h₁ : Y ⟶ Y₁) (h₂ : Y ⟶ Y₂) (s : LB.Sec (LB.LinComb M φ ε)) (s₁ : LB.Sec (LB.LinComb M₁ φ₁ ε))
    (s₂ : LB.Sec (LB.LinComb M₂ φ₂ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J₁ : (Z ⟶ X₁) → M₁.ι) (J₂ : (Z ⟶ X₂) → M₂.ι) (J : (Z ⟶ X) → M.ι),
    Good M₁ z J₁ → Good M₂ z J₂ → Good M z J →
    (∏ a, om w z J₁ J₂ J (r ≫ φ a) ^ ε a).val * sval s r z J = sval s₁ (r ≫ h₁) z J₁ * sval s₂ (r ≫ h₂) z J₂

end Vals

section Core

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

variable {X X₁ X₂ Z : Scheme.{0}} {M : LB X} {M₁ : LB X₁} {M₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
  {K : Type} [Fintype K] {Y Y₁ Y₂ : Scheme.{0}}

theorem isLB_extLB (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) : (extLB M₁ M₂ f₁ f₂).IsLB :=
  GlobalTheory.CechPic.isLB_tens (pull_isLB h₁ f₁) (pull_isLB h₂ f₂)

theorem mem_extIdx {x : X} {j₁ : M₁.ι} {j₂ : M₂.ι} (h₁ : f₁ x ∈ M₁.U j₁) (h₂ : f₂ x ∈ M₂.U j₂) :
    x ∈ (extLB M₁ M₂ f₁ f₂).U (extIdx j₁ j₂) := ⟨mem_pull.2 h₁, mem_pull.2 h₂⟩

theorem good_ext {z : Z} {J₁ : (Z ⟶ X₁) → M₁.ι} {J₂ : (Z ⟶ X₂) → M₂.ι} (h₁ : Good M₁ z J₁) (h₂ : Good M₂ z J₂) :
    Good (extLB M₁ M₂ f₁ f₂) z (fun ψ => extIdx (J₁ (ψ ≫ f₁)) (J₂ (ψ ≫ f₂))) :=
  fun ψ => mem_extIdx (h₁ (ψ ≫ f₁)) (h₂ (ψ ≫ f₂))

theorem trF_pull {F : X ⟶ X₁} {ψ : K → (Y ⟶ X)} {φ : K → (Y₁ ⟶ X₁)} {ε : K → ℤ} {h : Y ⟶ Y₁}
    (e : ∀ k, ψ k ≫ F = h ≫ φ k) (r : Z ⟶ Y) (z : Z) (a b : K → (M₁.pull F).ι)
    (ha : r z ∈ LB.wchart (M₁.pull F) ψ a) (hb : r z ∈ LB.wchart (M₁.pull F) ψ b) :
    trF (L := M₁.pull F) ψ ε r z a b = trF (L := M₁) φ ε (r ≫ h) z (fun k => a k ⟨⟩) (fun k => b k ⟨⟩) := by
  unfold trF
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
  rw [gm_pull_g M₁ F (r ≫ ψ k) z (a k) (b k) (Set.mem_iInter.1 ha k) (Set.mem_iInter.1 hb k), Category.assoc, e,
    Category.assoc]

variable {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X₁)} {φ₂ : K → (Y₂ ⟶ X₂)} {ε : K → ℤ} {h₁ : Y ⟶ Y₁} {h₂ : Y ⟶ Y₂}

theorem exists_extSec (e₁ : ∀ k, φ k ≫ f₁ = h₁ ≫ φ₁ k) (e₂ : ∀ k, φ k ≫ f₂ = h₂ ≫ φ₂ k)
    (s₁ : LB.Sec (LB.LinComb M₁ φ₁ ε)) (s₂ : LB.Sec (LB.LinComb M₂ φ₂ ε)) :
    ∃ s : LB.Sec (LB.LinComb (extLB M₁ M₂ f₁ f₂) φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (jj : K → (extLB M₁ M₂ f₁ f₂).ι), r z ∈ LB.wchart (extLB M₁ M₂ f₁ f₂) φ jj →
      gs r z (LB.wchart (extLB M₁ M₂ f₁ f₂) φ jj) (s.f jj) =
        gs (r ≫ h₁) z (LB.wchart M₁ φ₁ (fun k => (jj k).1 ⟨⟩)) (s₁.f (fun k => (jj k).1 ⟨⟩)) *
          gs (r ≫ h₂) z (LB.wchart M₂ φ₂ (fun k => (jj k).2 ⟨⟩)) (s₂.f (fun k => (jj k).2 ⟨⟩)) := by
  have l₁ : ∀ jj : K → (extLB M₁ M₂ f₁ f₂).ι, LB.wchart (extLB M₁ M₂ f₁ f₂) φ jj ≤
      h₁ ⁻¹ᵁ LB.wchart M₁ φ₁ (fun k => (jj k).1 ⟨⟩) := fun jj =>
    (tens_le₁ _ _ φ jj).trans (GeneratorPullback.pullAlong_le M₁ f₁ h₁ φ₁ φ e₁ _)
  have l₂ : ∀ jj : K → (extLB M₁ M₂ f₁ f₂).ι, LB.wchart (extLB M₁ M₂ f₁ f₂) φ jj ≤
      h₂ ⁻¹ᵁ LB.wchart M₂ φ₂ (fun k => (jj k).2 ⟨⟩) := fun jj =>
    (tens_le₂ _ _ φ jj).trans (GeneratorPullback.pullAlong_le M₂ f₂ h₂ φ₂ φ e₂ _)
  obtain ⟨u, hu⟩ : ∃ u : ∀ jj : K → (extLB M₁ M₂ f₁ f₂).ι, Γ(Y, LB.wchart (extLB M₁ M₂ f₁ f₂) φ jj),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (jj : K → (extLB M₁ M₂ f₁ f₂).ι), r z ∈ LB.wchart (extLB M₁ M₂ f₁ f₂) φ jj →
      gs r z (LB.wchart (extLB M₁ M₂ f₁ f₂) φ jj) (u jj) =
        gs (r ≫ h₁) z (LB.wchart M₁ φ₁ (fun k => (jj k).1 ⟨⟩)) (s₁.f (fun k => (jj k).1 ⟨⟩)) *
          gs (r ≫ h₂) z (LB.wchart M₂ φ₂ (fun k => (jj k).2 ⟨⟩)) (s₂.f (fun k => (jj k).2 ⟨⟩)) :=
    ⟨fun jj => (Y.presheaf.map (homOfLE (l₁ jj)).op).hom ((h₁.app _).hom (s₁.f (fun k => (jj k).1 ⟨⟩))) *
      (Y.presheaf.map (homOfLE (l₂ jj)).op).hom ((h₂.app _).hom (s₂.f (fun k => (jj k).2 ⟨⟩))),
      fun Z r z jj hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z _ hz _).trans (gs_pull r h₁ z _ (l₁ jj hz) _))
        ((gs_res r z _ hz _).trans (gs_pull r h₂ z _ (l₂ jj hz) _)))⟩
  refine ⟨⟨u, fun jj jj' => fn_ext fun y hy => ?_⟩, hu⟩
  refine ((gs_res (𝟙 Y) y _ hy _).trans (hu _ _ y jj hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val ((gm_linComb _ φ ε (𝟙 Y) y jj jj' hy.1 hy.2).trans
        ((trF_tens _ _ φ ε (𝟙 Y) y jj jj' hy.1 hy.2).trans (congrArg₂ (· * ·)
          (trF_pull e₁ (𝟙 Y) y _ _ (tens_le₁ _ _ φ jj hy.1) (tens_le₁ _ _ φ jj' hy.2))
          (trF_pull e₂ (𝟙 Y) y _ _ (tens_le₂ _ _ φ jj hy.1) (tens_le₂ _ _ φ jj' hy.2)))))))
      ((gs_res (𝟙 Y) y _ hy _).trans (hu _ _ y jj' hy.2)))).symm)
  rw [sec_trans s₁ (𝟙 Y ≫ h₁) y (l₁ jj hy.1) (l₁ jj' hy.2), sec_trans s₂ (𝟙 Y ≫ h₂) y (l₂ jj hy.1) (l₂ jj' hy.2),
    Units.val_mul, _root_.mul_mul_mul_comm]

theorem gm_linCombIso' {A B : LB X} (w : LB.Iso A B) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z)
    (b : K → B.ι) (a : K → A.ι) (hz : r z ∈ LB.wchart B φ b ⊓ LB.wchart A φ a) :
    gm r z (LB.wchart B φ b ⊓ LB.wchart A φ a) ((LB.linCombIso w φ ε).s (b, a)) =
      ∏ k, gm (r ≫ φ k) z (B.U (b k) ⊓ A.U (a k)) (w.s (b k, a k)) ^ ε k :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
    ((gm_res r z _ hz _).trans (gm_pull r (φ k) z (B.U (b k) ⊓ A.U (a k))
      ⟨Set.mem_iInter.1 hz.1 k, Set.mem_iInter.1 hz.2 k⟩ _))))

theorem exists_boxSec (w : LB.Iso M (extLB M₁ M₂ f₁ f₂)) (hw : w.IsGen) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) (hM : M.IsLB)
    (e₁ : ∀ k, φ k ≫ f₁ = h₁ ≫ φ₁ k) (e₂ : ∀ k, φ k ≫ f₂ = h₂ ≫ φ₂ k)
    (s₁ : LB.Sec (LB.LinComb M₁ φ₁ ε)) (s₂ : LB.Sec (LB.LinComb M₂ φ₂ ε)) :
    ∃ s : LB.Sec (LB.LinComb M φ ε), IsBoxSec w h₁ h₂ s s₁ s₂ := by
  obtain ⟨t, ht⟩ := exists_extSec e₁ e₂ s₁ s₂
  have hA := linComb_isLB _ hM φ ε
  have hB := linComb_isLB _ (isLB_extLB hM₁ hM₂ f₁ f₂) φ ε
  have hu := linCombIso_isGen w hw φ ε
  refine ⟨secOfIso (u := LB.linCombIso w φ ε) t hu hA hB, fun Z r z J₁ J₂ J hJ₁ hJ₂ hJ => ?_⟩
  have hE := good_ext (f₁ := f₁) (f₂ := f₂) hJ₁ hJ₂
  have mB := hE.mem φ r
  have mA := hJ.mem φ r
  have hm : r z ∈ (LB.LinComb M φ ε).U (fun k => J (r ≫ φ k)) ⊓ (LB.LinComb (extLB M₁ M₂ f₁ f₂) φ ε).U
      (fun k => extIdx (J₁ ((r ≫ φ k) ≫ f₁)) (J₂ ((r ≫ φ k) ≫ f₂))) := ⟨mA, mB⟩
  have E := congrArg (gs r z _) (secOfIso_spec (u := LB.linCombIso w φ ε) t hu hA hB (fun k => J (r ≫ φ k))
    (fun k => extIdx (J₁ ((r ≫ φ k) ≫ f₁)) (J₂ ((r ≫ φ k) ≫ f₂))))
  have E' := (gs_res r z _ hm _).symm.trans (E.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
    ((gs_unit r z _ hm _).trans (congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹)
      ((gm_res r z _ hm _).trans (gm_linCombIso' w φ ε r z _ _ ⟨mB, mA⟩))))))
    ((gs_res r z _ hm _).trans (ht Z r z _ mB)))))
  rw [sval_of s₁ (r ≫ h₁) z J₁ (fun k => J₁ ((r ≫ φ k) ≫ f₁)) (fun k => by rw [Category.assoc, Category.assoc, e₁]),
    sval_of s₂ (r ≫ h₂) z J₂ (fun k => J₂ ((r ≫ φ k) ≫ f₂)) (fun k => by rw [Category.assoc, Category.assoc, e₂])]
  refine (congrArg₂ (· * ·) rfl E').trans ?_
  exact Units.mul_inv_cancel_left _ _

theorem exists_boxGen (w : LB.Iso M (extLB M₁ M₂ f₁ f₂)) (hw : w.IsGen) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) (hM : M.IsLB)
    (e₁ : ∀ k, φ k ≫ f₁ = h₁ ≫ φ₁ k) (e₂ : ∀ k, φ k ≫ f₂ = h₂ ≫ φ₂ k)
    (t₁ : LB.Gen (LB.LinComb M₁ φ₁ ε)) (ht₁ : t₁.IsGen) (t₂ : LB.Gen (LB.LinComb M₂ φ₂ ε)) (ht₂ : t₂.IsGen) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ IsBoxGen w h₁ h₂ t t₁ t₂ := by
  obtain ⟨s, hs⟩ := exists_boxSec w hw hM₁ hM₂ hM e₁ e₂ (Geo.Tor.genSec t₁ ht₁) (Geo.Tor.genSec t₂ ht₂)
  have hv : ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (y : Z) J₁ J₂ J, Good M₁ y J₁ → Good M₂ y J₂ → Good M y J →
      (∏ a, om w y J₁ J₂ J (q ≫ φ a) ^ ε a).val * sval s q y J =
        (val t₁ (q ≫ h₁) y J₁ * val t₂ (q ≫ h₂) y J₂).val :=
    fun Z q y J₁ J₂ J hJ₁ hJ₂ hJ => (hs Z q y J₁ J₂ J hJ₁ hJ₂ hJ).trans
      (congrArg₂ (· * ·) (sval_genSec t₁ ht₁ _ y hJ₁) (sval_genSec t₂ ht₂ _ y hJ₂))
  have hu : ∀ c, IsUnit (s.f c) := fun c => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hM s y c hy
    obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
    obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
    have a : IsUnit (sval s (𝟙 Y) y J) :=
      isUnit_of_mul_isUnit_right ((hv _ (𝟙 Y) y J₁ J₂ J hJ₁ hJ₂ hJ).symm ▸ Units.isUnit _)
    exact (congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart M φ c) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul a)
  refine ⟨⟨fun c => (hu c).unit⟩, fun a b => Units.ext (s.compat a b),
    fun Z q y J₁ J₂ J hJ₁ hJ₂ hJ => Units.ext ?_⟩
  refine Eq.trans ?_ (hv Z q y J₁ J₂ J hJ₁ hJ₂ hJ)
  rw [Units.val_mul]
  exact congrArg₂ (· * ·) rfl (gs_unit q y _ (hJ.mem φ q) _).symm

theorem isBoxGen_of_section {S₀ : Scheme.{0}} (w : LB.Iso M (extLB M₁ M₂ f₁ f₂)) (hw : w.IsGen) (hM₁ : M₁.IsLB)
    (hM₂ : M₂.IsLB) (hM : M.IsLB) (e₁ : ∀ k, φ k ≫ f₁ = h₁ ≫ φ₁ k) (e₂ : ∀ k, φ k ≫ f₂ = h₂ ≫ φ₂ k)
    {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen) {t₁ : LB.Gen (LB.LinComb M₁ φ₁ ε)} (ht₁ : t₁.IsGen)
    {t₂ : LB.Gen (LB.LinComb M₂ φ₂ ε)} (ht₂ : t₂.IsGen) (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J₁ J₂ J, Good M₁ y J₁ → Good M₂ y J₂ → Good M y J →
      (∏ a, om w y J₁ J₂ J (e ≫ φ a) ^ ε a) * val t e y J = val t₁ (e ≫ h₁) y J₁ * val t₂ (e ≫ h₂) y J₂) :
    IsBoxGen w h₁ h₂ t t₁ t₂ := by
  obtain ⟨t', ht', H⟩ := exists_boxGen w hw hM₁ hM₂ hM e₁ e₂ t₁ ht₁ t₂ ht₂
  intro Z r z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [gen_unique hM p e he hp ht ht' (fun y I hI => ?_) Z r z J hJ]
  · exact H Z r z J₁ J₂ J hJ₁ hJ₂ hJ
  · obtain ⟨I₁, hI₁⟩ := BoxFamily.exists_good_at hM₁ y
    obtain ⟨I₂, hI₂⟩ := BoxFamily.exists_good_at hM₂ y
    exact mul_left_cancel ((h y I₁ I₂ I hI₁ hI₂ hI).trans (H _ e y I₁ I₂ I hI₁ hI₂ hI).symm)

theorem isBoxGen_of_mapsAt (w : LB.Iso M (extLB M₁ M₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ)
    {a : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => p) (fun _ => n))} {p₁ : Y ⟶ X₁} {p₂ : Y ⟶ X₂}
    {t₁ : LB.Gen (LB.LinComb M₁ (K := PUnit) (fun _ => p₁) (fun _ => n))}
    {t₂ : LB.Gen (LB.LinComb M₂ (K := PUnit) (fun _ => p₂) (fun _ => n))}
    (H : ∃ b₁ b₂, MapsAt₂ w p n a b₁ b₂ ∧ LB.Gen.Corr M₁ _ _ _ _ b₁ t₁ ∧ LB.Gen.Corr M₂ _ _ _ _ b₂ t₂) :
    IsBoxGen w (𝟙 Y) (𝟙 Y) a t₁ t₂ := by
  obtain ⟨b₁, b₂, H, c₁, c₂⟩ := H
  intro Z r z J₁ J₂ J hJ₁ hJ₂ hJ
  have hm : r z ∈ p ⁻¹ᵁ (LB.div (extLB M₁ M₂ f₁ f₂) M).U
      (extIdx (f₁ := f₁) (f₂ := f₂) (J₁ ((r ≫ p) ≫ f₁)) (J₂ ((r ≫ p) ≫ f₂)), J (r ≫ p)) :=
    ⟨mem_extIdx (hJ₁ ((r ≫ p) ≫ f₁)) (hJ₂ ((r ≫ p) ≫ f₂)), hJ (r ≫ p)⟩
  have E := congrArg (gm r z _) (H (J₁ ((r ≫ p) ≫ f₁)) (J₂ ((r ≫ p) ≫ f₂)) (J (r ≫ p)))
  rw [Category.comp_id, ← val_corr hJ₁ c₁, ← val_corr hJ₂ c₂, Fintype.prod_unique,
    val_of b₁ r z J₁ (fun _ => J₁ ((r ≫ p) ≫ f₁)) (fun _ => by rw [Category.assoc]),
    val_of b₂ r z J₂ (fun _ => J₂ ((r ≫ p) ≫ f₂)) (fun _ => by rw [Category.assoc])]
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n) (gm_pull r p z _ hm _)))
    (gm_res r z _ hm _))).symm.trans (E.symm.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_res r z _ hm _) (gm_res r z _ hm _))))

end Core

section Sq

variable {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁}
  {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁}
  {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂}

def BoxSq (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we : LB.Iso (L.pull f) (M.pull p))
    (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)) (h₁ : T ⟶ T₁) (h₂ : T ⟶ T₂) :
    Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (J₁ : (Z ⟶ B₁) → M₁.ι) (J₂ : (Z ⟶ B₂) → M₂.ι) (J : (Z ⟶ B) → M.ι)
    (N₁ : (Z ⟶ G₁) → L₁.ι) (N₂ : (Z ⟶ G₂) → L₂.ι) (N : (Z ⟶ G) → L.ι),
    Good M₁ z J₁ → Good M₂ z J₂ → Good M z J → Good L₁ z N₁ → Good L₂ z N₂ → Good L z N →
    om wM z J₁ J₂ J (r ≫ p) * gw we r z (J (r ≫ p)) (fun _ => N (r ≫ f)) =
      gw we₁ (r ≫ h₁) z (J₁ ((r ≫ p) ≫ b₁)) (fun _ => N₁ ((r ≫ f) ≫ g₁)) *
        gw we₂ (r ≫ h₂) z (J₂ ((r ≫ p) ≫ b₂)) (fun _ => N₂ ((r ≫ f) ≫ g₂)) * om wL z N₁ N₂ N (r ≫ f)

end Sq

section Rel

theorem rel_alg {U K : Type} [CommGroup U] [Fintype K] (ε : K → ℤ) (oM oL W W₁ W₂ : K → U)
    (Q : ∀ k, oM k * W k = W₁ k * W₂ k * oL k) {vM vM₁ vM₂ vL vL₁ vL₂ : U}
    (HM : (∏ k, oM k ^ ε k) * vM = vM₁ * vM₂) (HL : (∏ k, oL k ^ ε k) * vL = vL₁ * vL₂)
    (H₁ : vM₁ = (∏ k, W₁ k ^ ε k) * vL₁) (H₂ : vM₂ = (∏ k, W₂ k ^ ε k) * vL₂) : vM = (∏ k, W k ^ ε k) * vL := by
  have e : (∏ k, oM k ^ ε k) * (∏ k, W k ^ ε k) = (∏ k, W₁ k ^ ε k) * (∏ k, W₂ k ^ ε k) * ∏ k, oL k ^ ε k := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← mul_zpow, Q, mul_zpow, mul_zpow]
  apply mul_left_cancel (a := ∏ k, oM k ^ ε k)
  rw [HM, ← _root_.mul_assoc, e, _root_.mul_assoc, HL, H₁, H₂, _root_.mul_mul_mul_comm]

end Rel

section Str

variable {S : Scheme.{0}}

abbrev CubGen (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) := LB.Gen (LB.LinComb L (thφ A (x3 A)) thε)

abbrev SymGen (A : Over S) [GrpObj A] (L : LB A.left) :=
  LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])

variable {A A₁ A₂ : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂]
  {L : LB A.left} {L₁ : LB A₁.left} {L₂ : LB A₂.left}

def StrBox (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) (w : LB.Iso L (extLB L₁ L₂ a₁.left a₂.left))
    (r : LB.Gen (L.pull (eSec A))) (r₁ : LB.Gen (L₁.pull (eSec A₁))) (r₂ : LB.Gen (L₂.pull (eSec A₂)))
    (c : CubGen A L) (c₁ : CubGen A₁ L₁) (c₂ : CubGen A₂ L₂) (s : SymGen A L) (s₁ : SymGen A₁ L₁)
    (s₂ : SymGen A₂ L₂) : Prop :=
  w.IsGen ∧ IsBoxGen w (𝟙 _) (𝟙 _) r r₁ r₂ ∧ IsBoxGen w (a₁ ⊗ₘ a₁ ⊗ₘ a₁).left (a₂ ⊗ₘ a₂ ⊗ₘ a₂).left c c₁ c₂ ∧
    IsBoxGen w a₁.left a₂.left s s₁ s₂

end Str

section Level

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

def TMul (D : DegPre R) {T : Over (Sp R)} (P : T ⟶ D.P.A)
    (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) : Prop :=
  ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') P)).left))
    (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))

def CubAlong (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (c : LB.Gen (Theta G L)) (P : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ D.P.A)
    (w : LB.Iso (L.pull (fstG I e G).left) (D.P.L.pull P.left)) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (jL : thK → L.ι) (jM : thK → D.P.L.ι),
    LB.Coh L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
        ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ≫ thφ G (x3 G) k) jL →
    LB.Coh D.P.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ P)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ P)
        ((Over.map (thick R I e)).map (x 2) ≫ P))).left ≫ thφ D.P.A (x3 D.P.A) k) jM →
    ∀ (V : T.left.Opens)
      (hB : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ P)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ P)
          ((Over.map (thick R I e)).map (x 2) ≫ P))).left ⁻¹ᵁ (Theta D.P.A D.P.L).U jM)
      (hG : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
          ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ⁻¹ᵁ (Theta G L).U jL)
      (hw : ∀ k : thK, V ≤ (psum (thickObj R I e G) x k.down).left ⁻¹ᵁ
        ((D.P.L.pull P.left).U (fun _ => jM k) ⊓ (L.pull (fstG I e G).left).U (fun _ => jL k))),
      res hB (pullU _ _ (D.cub.t.s jM)) =
        (∏ k : thK, res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
          (w.s (fun _ => jM k, fun _ => jL k))) ^ thε k) *
        res hG (pullU _ _ (c.s jL))

def IsBoxFam₂ {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X)
    (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (E : Fam D F k) (E₁ : Fam D₁ F k) (E₂ : Fam D₂ F k) : Prop :=
  ∀ α : D.X, IsBoxSec w (TF (R := R) F ◁ p₁).left (TF (R := R) F ◁ p₂).left (E.s α) (E₁.s (q₁ α)) (E₂.s (q₂ α))

omit [IsDomain R] in

theorem thick_fstG (I : Ideal R) (e : ℕ) {G H : Over (Sp R)} (π : G ⟶ H) :
    (fstG I e G).left ≫ π.left = ((Over.pullback (thick R I e)).map π).left ≫ (fstG I e H).left :=
  (pullback.lift_fst _ _ _).symm

theorem thickMap_nat (I : Ideal R) (e : ℕ) {G H : Over (Sp R)} (π : G ⟶ H) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map π).left =
      ((Over.pullback (thick R I e)).map π).left ≫ thickMap R I e H := by
  have := UnifPullRig.mono_fstG I (e + 1) H
  refine (cancel_mono (fstG I (e + 1) H).left).1 ?_
  refine (Category.assoc _ _ _).trans ((congrArg (thickMap R I e G ≫ ·) (thick_fstG I (e + 1) π).symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π.left) (UnifPullRig.thickMap_fstG I e G)).trans
      ((thick_fstG I e π).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))))))
  exact congrArg (((Over.pullback (thick R I e)).map π).left ≫ ·) (UnifPullRig.thickMap_fstG I e H)

theorem pG_pr {I : Ideal R} {e : ℕ} {D D₁ : DegPre R} {G G₁ : Over (Sp R)} {p : D.P.A ⟶ D₁.P.A} {π : G ⟶ G₁}
    {q : thickObj R I e G ⟶ thickObj R I e D.P.A} {q₁ : thickObj R I e G₁ ⟶ thickObj R I e D₁.P.A}
    (h : q ≫ (Over.pullback (thick R I e)).map p = (Over.pullback (thick R I e)).map π ≫ q₁) :
    ((Over.map (thick R I e)).map q ≫ D.prBe I e) ≫ p =
      (Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map π) ≫
        ((Over.map (thick R I e)).map q₁ ≫ D₁.prBe I e) := by
  have b : D.prBe I e ≫ p = (Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map p) ≫ D₁.prBe I e :=
    Over.OverMorphism.ext (pullback.lift_fst _ _ _).symm
  rw [Category.assoc, b, ← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]

theorem cPoint_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} {q : D.X → D₁.X} (hc : ∀ x, D.c x ≫ p = D₁.c (q x))
    (T : Over (Sp R)) (χ : D.X) : cP D T χ ≫ p = cP D₁ T (q χ) := by
  rw [cP, cP, Category.assoc, hc]

theorem Oφ_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X → D₁.X} (hc : ∀ x, D.c x ≫ p = D₁.c (q x))
    {T T₁ : Over (Sp R)} {P : T ⟶ D.P.A} {P₁ : T₁ ⟶ D₁.P.A} {ρ : T ⟶ T₁} (hp : P ≫ p = ρ ≫ P₁) (x : D.X) (κ : Fin 4) :
    D.Oφ P x κ ≫ p.left = ρ.left ≫ D₁.Oφ P₁ (q x) κ := by
  refine Eq.trans ?_ (WeightPf.Oφ_comp ρ P₁ (q x) κ).symm
  rw [← hp]
  fin_cases κ
  · refine congrArg (fun m : T ⟶ D₁.P.A => m.left) (?_ : (P * cP D _ x) ≫ p = (P ≫ p) * cP D₁ _ (q x))
    rw [MonObj.mul_comp, cPoint_pr hc]
  · exact congrArg (fun m : T ⟶ D₁.P.A => m.left) (cPoint_pr hc _ x)
  · rfl
  · exact congrArg (fun m : T ⟶ D₁.P.A => m.left) (MonObj.one_comp p)

theorem famφB_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X → D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (α : D.X) (a : Fin 4) :
    D.famφB α a ≫ p.left = p.left ≫ D₁.famφB (q α) a := by
  fin_cases a
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · refine congrArg (fun m : D.P.A ⟶ D₁.P.A => m.left)
      (?_ : (𝟙 _ * cP D _ α) ≫ p = p ≫ (𝟙 _ * cP D₁ _ (q α)))
    rw [MonObj.mul_comp, MonObj.comp_mul, cPoint_pr hc, comp_cP, Category.id_comp, Category.comp_id]
  · exact congrArg (fun m : D.P.A ⟶ D₁.P.A => m.left) ((cPoint_pr hc _ α).trans (comp_cP D₁ p _).symm)
  · exact congrArg (fun m : D.P.A ⟶ D₁.P.A => m.left)
      ((MonObj.one_comp p).trans (MonObj.comp_one (M := D₁.P.A) p).symm)

theorem famφ_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X → D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (F : Type) [Field F] [Algebra (FractionRing R) F] (α : D.X) (a : Fin 4) :
    DegPre.famφ D F α a ≫ p.left = (TF (R := R) F ◁ p).left ≫ DegPre.famφ D₁ F (q α) a := by
  have b : DegPre.prB D F ≫ p = (TF (R := R) F ◁ p) ≫ DegPre.prB D₁ F := (whiskerLeft_snd _ _).symm
  fin_cases a
  · exact congrArg (fun m => m.left) b
  · refine congrArg (fun m : DegPre.BF D F ⟶ D₁.P.A => m.left) (?_ : (DegPre.prB D F * cP D _ α) ≫ p =
      (TF (R := R) F ◁ p) ≫ (DegPre.prB D₁ F * cP D₁ _ (q α)))
    rw [MonObj.mul_comp, MonObj.comp_mul, b, cPoint_pr hc, comp_cP]
  · exact congrArg (fun m => m.left) ((cPoint_pr hc (DegPre.BF D F) α).trans (comp_cP D₁ (TF (R := R) F ◁ p) _).symm)
  · exact congrArg (fun m : DegPre.BF D F ⟶ D₁.P.A => m.left) ((MonObj.one_comp p).trans
      (MonObj.comp_one (M := D₁.P.A) (TF (R := R) F ◁ p)).symm)

end Level

end GlobalTheory.ProdUnif
