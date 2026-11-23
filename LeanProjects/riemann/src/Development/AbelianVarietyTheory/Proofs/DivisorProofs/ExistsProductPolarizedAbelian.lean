import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitModelToPlaceModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfProductDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTrivialOfProductDecompositionStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam pull)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

set_option autoImplicit false
noncomputable section

open MonObj

namespace GlobalTheory.PPAS.ProdMk
variable {S : Scheme.{0}}

theorem smooth_tensor {A B : Over S} {g₁ g₂ : ℕ} (h₁ : SmoothOfRelativeDimension g₁ A.hom)
    (h₂ : SmoothOfRelativeDimension g₂ B.hom) : SmoothOfRelativeDimension (g₁ + g₂) (A ⊗ B).hom := by
  have : SmoothOfRelativeDimension g₂ (pullback.fst A.hom B.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g₂).of_isPullback
      (IsPullback.of_hasPullback A.hom B.hom).flip h₂
  rw [Over.tensorObj_hom, add_comm]
  exact smoothOfRelativeDimension_comp g₂ g₁ _ _

theorem lift_one_id_tensorHom {X Y : Over S} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) [IsMonHom f] :
    lift (1 : X ⟶ X) (𝟙 X) ≫ (f ⊗ₘ f) = f ≫ lift (1 : Y ⟶ Y) (𝟙 Y) := by
  ext1 <;> simp [MonObj.one_comp, MonObj.comp_one]

theorem lift_id_one_tensorHom {X Y : Over S} [GrpObj X] [GrpObj Y] (f : X ⟶ Y) [IsMonHom f] :
    lift (𝟙 X) (1 : X ⟶ X) ≫ (f ⊗ₘ f) = f ≫ lift (𝟙 Y) (1 : Y ⟶ Y) := by
  ext1 <;> simp [MonObj.one_comp, MonObj.comp_one]

theorem sqToBase_tensorHom {T : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y) (s : T ⟶ S) :
    sqToBase X s ≫ (f ⊗ₘ f).left =
      ((Over.pullback s).map f ⊗ₘ (Over.pullback s).map f).left ≫ sqToBase Y s := by
  let m : Over.mk (((Over.pullback s).obj X ⊗ (Over.pullback s).obj X).hom ≫ s) ⟶
      Over.mk (((Over.pullback s).obj Y ⊗ (Over.pullback s).obj Y).hom ≫ s) :=
    Over.homMk ((Over.pullback s).map f ⊗ₘ (Over.pullback s).map f).left (by
      simp only [Over.mk_hom]
      rw [← Category.assoc, Over.w])
  have hp : ((Over.pullback s).map f).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ f.left := by
    simp [pullback.lift_fst]
  have e₁ : toBase X s (fst _ _) ≫ f = m ≫ toBase Y s (fst _ _) := by
    ext1
    simp only [toBase, Over.comp_left, Over.homMk_left, m, Category.assoc]
    rw [← Category.assoc ((Over.pullback s).map f ⊗ₘ (Over.pullback s).map f).left, ← Over.comp_left,
      tensorHom_fst, Over.comp_left, Category.assoc, hp]
  have e₂ : toBase X s (snd _ _) ≫ f = m ≫ toBase Y s (snd _ _) := by
    ext1
    simp only [toBase, Over.comp_left, Over.homMk_left, m, Category.assoc]
    rw [← Category.assoc ((Over.pullback s).map f ⊗ₘ (Over.pullback s).map f).left, ← Over.comp_left,
      tensorHom_snd, Over.comp_left, Category.assoc, hp]
  have h : ((Over.pullback s).map f ⊗ₘ (Over.pullback s).map f).left ≫ sqToBase Y s =
      (m ≫ lift (toBase Y s (fst _ _)) (toBase Y s (snd _ _))).left := rfl
  rw [h, sqToBase, ← Over.comp_left, comp_lift, lift_map, e₁, e₂]

theorem lam_add_cls {T : Scheme.{0}} {C D : Over T} [GrpObj C] (c d : Pic C.left) (x y : D ⟶ C) :
    lam (c + d) x y = lam c x y + lam d x y := by
  simp only [lam, map_add]
  abel

theorem relAmple_of_isLimit {T : Scheme.{0}} [IsAffine T] {C B₁ B₂ : Over T} [GrpObj C] [GrpObj B₁]
    [GrpObj B₂] (hB₁ : IsAbelianScheme B₁) (hB₂ : IsAbelianScheme B₂) (q₁ : C ⟶ B₁) (q₂ : C ⟶ B₂)
    (hq : IsLimit (BinaryFan.mk q₁ q₂)) {L₁ : LB B₁.left} (hL₁ : L₁.IsLB) (a₁ : Out.RelAmple B₁ L₁)
    {L₂ : LB B₂.left} (hL₂ : L₂.IsLB) (a₂ : Out.RelAmple B₂ L₂) {L : LB C.left} (hL : L.IsLB)
    (e : cls L hL = pull q₁.left (cls L₁ hL₁) + pull q₂.left (cls L₂ hL₂)) : Out.RelAmple C L :=
  GlobalTheory.T.rel_ample_of_product_decomposition hB₁ hB₂ q₁ q₂ hq hL₁ a₁ hL₂ a₂ hL e

theorem kTriv_of_isLimit {T : Scheme.{0}} {C B₁ B₂ : Over T} [GrpObj C] [GrpObj B₁] [GrpObj B₂]
    (q₁ : C ⟶ B₁) (q₂ : C ⟶ B₂) [IsMonHom q₁] [IsMonHom q₂] (hq : IsLimit (BinaryFan.mk q₁ q₂))
    {L₁ : LB B₁.left} (hL₁ : L₁.IsLB) (k₁ : Out.KTriv B₁ L₁) {L₂ : LB B₂.left} (hL₂ : L₂.IsLB)
    (k₂ : Out.KTriv B₂ L₂) {L : LB C.left} (hL : L.IsLB)
    (e : cls L hL = pull q₁.left (cls L₁ hL₁) + pull q₂.left (cls L₂ hL₂)) : Out.KTriv C L :=
  GlobalTheory.T.k_trivial_of_product_decomposition q₁ q₂ hq hL₁ k₁ hL₂ k₂ hL e

theorem fibre_prod {T : Scheme.{0}} [IsAffine T] {C B₁ B₂ : Over T} [GrpObj C] [GrpObj B₁] [GrpObj B₂]
    (hB₁ : IsAbelianScheme B₁) (hB₂ : IsAbelianScheme B₂) (q₁ : C ⟶ B₁) (q₂ : C ⟶ B₂) [IsMonHom q₁]
    [IsMonHom q₂] (hq : IsLimit (BinaryFan.mk q₁ q₂)) {L₁ : LB B₁.left} (hL₁ : L₁.IsLB)
    (a₁ : Out.RelAmple B₁ L₁) (k₁ : Out.KTriv B₁ L₁) {L₂ : LB B₂.left} (hL₂ : L₂.IsLB)
    (a₂ : Out.RelAmple B₂ L₂) (k₂ : Out.KTriv B₂ L₂) :
    ∃ (L : LB C.left) (hL : L.IsLB), Out.RelAmple C L ∧ Out.KTriv C L ∧
      lam (cls L hL) (fst C C) (snd C C) =
        pull (q₁ ⊗ₘ q₁).left (lam (cls L₁ hL₁) (fst B₁ B₁) (snd B₁ B₁)) +
          pull (q₂ ⊗ₘ q₂).left (lam (cls L₂ hL₂) (fst B₂ B₂) (snd B₂ B₂)) := by
  obtain ⟨L, hL, e⟩ := CechPic.cls_surj (pull q₁.left (cls L₁ hL₁) + pull q₂.left (cls L₂ hL₂))
  refine ⟨L, hL, relAmple_of_isLimit hB₁ hB₂ q₁ q₂ hq hL₁ a₁ hL₂ a₂ hL e,
    kTriv_of_isLimit q₁ q₂ hq hL₁ k₁ hL₂ k₂ hL e, ?_⟩
  rw [e, lam_add_cls, CechPic.lam_pull, CechPic.lam_pull, CechPic.pull_lam, CechPic.pull_lam,
    tensorHom_fst, tensorHom_snd, tensorHom_fst, tensorHom_snd]

theorem isPrincipalPol_tensor {A B : Over S} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) {c₁ : Pic (A ⊗ A).left} {c₂ : Pic (B ⊗ B).left}
    (h₁ : IsPrincipalPol A c₁) (h₂ : IsPrincipalPol B c₂) :
    IsPrincipalPol (A ⊗ B) (pull (fst A B ⊗ₘ fst A B).left c₁ + pull (snd A B ⊗ₘ snd A B).left c₂) := by
  refine ⟨?_, ?_, fun Ω _ _ s => ?_⟩
  · rw [map_add, ← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left,
      lift_one_id_tensorHom, lift_one_id_tensorHom, Over.comp_left, Over.comp_left, CechPic.pull_comp,
      CechPic.pull_comp, h₁.1, h₂.1, map_zero, map_zero, add_zero]
  · rw [map_add, ← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left,
      lift_id_one_tensorHom, lift_id_one_tensorHom, Over.comp_left, Over.comp_left, CechPic.pull_comp,
      CechPic.pull_comp, h₁.2.1, h₂.2.1, map_zero, map_zero, add_zero]
  · obtain ⟨L₁, hL₁, a₁, k₁, e₁⟩ := h₁.2.2 Ω s
    obtain ⟨L₂, hL₂, a₂, k₂, e₂⟩ := h₂.2.2 Ω s
    have hq := (isLimitMapConeBinaryFanEquiv (Over.pullback s) (fst A B) (snd A B))
      (isLimitOfPreserves (Over.pullback s) (tensorProductIsBinaryProduct A B))
    obtain ⟨L, hL, a, k, e⟩ := fibre_prod
      (PolPull.isAbelianScheme_of_isGrpPullback hA (isGrpPullback_pullback A s))
      (PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B s))
      ((Over.pullback s).map (fst A B)) ((Over.pullback s).map (snd A B)) hq hL₁ a₁ k₁ hL₂ a₂ k₂
    refine ⟨L, hL, a, k, ?_⟩
    rw [e, map_add, ← CechPic.pull_comp, ← CechPic.pull_comp, sqToBase_tensorHom, sqToBase_tensorHom,
      CechPic.pull_comp, CechPic.pull_comp, e₁, e₂]

end GlobalTheory.PPAS.ProdMk

namespace GlobalTheory.PPAS

def prod {S : Scheme.{0}} (P₁ P₂ : PPAS S) : PPAS S where
  A := P₁.A ⊗ P₂.A
  isAb := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P₁.isAb P₂.isAb
  g := P₁.g + P₂.g
  smoothDim := ProdMk.smooth_tensor P₁.smoothDim P₂.smoothDim
  c := pull (fst P₁.A P₂.A ⊗ₘ fst P₁.A P₂.A).left P₁.c + pull (snd P₁.A P₂.A ⊗ₘ snd P₁.A P₂.A).left P₂.c
  isPol := ProdMk.isPrincipalPol_tensor P₁.isAb P₂.isAb P₁.isPol P₂.isPol

theorem isProd_prod {S : Scheme.{0}} (P₁ P₂ : PPAS S) : (prod P₁ P₂).IsProd P₁ P₂ :=
  ⟨fst P₁.A P₂.A, snd P₁.A P₂.A, inferInstanceAs (IsMonHom (fst P₁.A P₂.A)),
    inferInstanceAs (IsMonHom (snd P₁.A P₂.A)),
    ⟨tensorProductIsBinaryProduct P₁.A P₂.A⟩, rfl, rfl⟩

theorem exists_isProd : ∀ (S : Scheme.{0}) (P₁ P₂ : PPAS S), ∃ P : PPAS S, P.IsProd P₁ P₂ :=
  fun _ P₁ P₂ => ⟨prod P₁ P₂, isProd_prod P₁ P₂⟩

end GlobalTheory.PPAS
