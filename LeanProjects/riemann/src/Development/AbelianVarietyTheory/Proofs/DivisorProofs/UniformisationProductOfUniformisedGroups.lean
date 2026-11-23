import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrBoxOfIsSumDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExternalTensorRigidifiedCubicalProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreProductSumPolarisedAbelianVariStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionProductOverThickeningOfSumDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TMulOfBox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmCharHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingBoxProductOfRestrictedIsosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigAlongBox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastLast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatBox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyLinearIndependentProductDegenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionModIdealPowBoxProductEqBoxProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothDimTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamDimOfExpBij
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpBijOfBasisCard

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.ProdUnifExists

open GlobalTheory.ProdUnif

section Main

open ReciprocityTheory.ChartRestriction.G.DVR

section Generic

variable {X X₁ X₂ : Scheme.{0}} {M : LB X} {M₁ : LB X₁} {M₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
  {K : Type} [Fintype K] {ε : K → ℤ} {Y Y₁ Y₂ W W₁ W₂ : Scheme.{0}}
  {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X₁)} {φ₂ : K → (Y₂ ⟶ X₂)} {ψ : K → (W ⟶ X)} {ψ₁ : K → (W₁ ⟶ X₁)}
  {ψ₂ : K → (W₂ ⟶ X₂)} {ρ₁ : Y ⟶ Y₁} {ρ₂ : Y ⟶ Y₂} {σ₁ : W ⟶ W₁} {σ₂ : W ⟶ W₂} {h : Y ⟶ W} {h₁ : Y₁ ⟶ W₁}
  {h₂ : Y₂ ⟶ W₂}

theorem corr_box (hM : M.IsLB) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) {w : LB.Iso M (extLB M₁ M₂ f₁ f₂)}
    (e : ∀ a, h ≫ ψ a = φ a) (e₁ : h ≫ σ₁ = ρ₁ ≫ h₁) (e₂ : h ≫ σ₂ = ρ₂ ≫ h₂)
    {s : LB.Gen (LB.LinComb M φ ε)} {s₁ : LB.Gen (LB.LinComb M₁ φ₁ ε)} {s₂ : LB.Gen (LB.LinComb M₂ φ₂ ε)}
    {t : LB.Gen (LB.LinComb M ψ ε)} {t₁ : LB.Gen (LB.LinComb M₁ ψ₁ ε)} {t₂ : LB.Gen (LB.LinComb M₂ ψ₂ ε)}
    (Hs : IsBoxGen w ρ₁ ρ₂ s s₁ s₂) (Ht : IsBoxGen w σ₁ σ₂ t t₁ t₂)
    (H₁ : LB.Gen.Corr M₁ _ _ _ _ (LB.pullGen M₁ _ _ t₁ h₁) s₁) (H₂ : LB.Gen.Corr M₂ _ _ _ _ (LB.pullGen M₂ _ _ t₂ h₂) s₂) :
    LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ t h) s := by
  refine corr_of_val hM fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
  rw [val_pull hJ, Category.id_comp]
  have a := Hs _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have b := Ht _ h y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [e₁, e₂, ← val_pull hJ₁, ← val_pull hJ₂, val_corr hJ₁ H₁, val_corr hJ₂ H₂] at b
  simp only [Category.id_comp] at a
  simp only [e] at b
  exact mul_left_cancel (b.trans a.symm)

theorem secScal_box (hM : M.IsLB) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) {w : LB.Iso M (extLB M₁ M₂ f₁ f₂)}
    (e : ∀ a, h ≫ ψ a = φ a) (e₁ : h ≫ σ₁ = ρ₁ ≫ h₁) (e₂ : h ≫ σ₂ = ρ₂ ≫ h₂)
    {s : LB.Sec (LB.LinComb M φ ε)} {s₁ : LB.Sec (LB.LinComb M₁ φ₁ ε)} {s₂ : LB.Sec (LB.LinComb M₂ φ₂ ε)}
    {t : LB.Sec (LB.LinComb M ψ ε)} {t₁ : LB.Sec (LB.LinComb M₁ ψ₁ ε)} {t₂ : LB.Sec (LB.LinComb M₂ ψ₂ ε)}
    (Hs : IsBoxSec w ρ₁ ρ₂ s s₁ s₂) (Ht : IsBoxSec w σ₁ σ₂ t t₁ t₂)
    {R : Type} [CommRing R] {π : Y ⟶ Sp R} {π₁ : Y₁ ⟶ Sp R} {π₂ : Y₂ ⟶ Sp R} (c₁ : ρ₁ ≫ π₁ = π) (c₂ : ρ₂ ≫ π₂ = π)
    {r₁ r₂ : R} (H₁ : GeneratorPullback.SecScal M₁ φ₁ ε s₁ ψ₁ ε t₁ h₁ (scal π₁ r₁))
    (H₂ : GeneratorPullback.SecScal M₂ φ₂ ε s₂ ψ₂ ε t₂ h₂ (scal π₂ r₂)) :
    GeneratorPullback.SecScal M φ ε s ψ ε t h (scal π (r₁ * r₂)) := by
  refine BoxFamScalar.secScal_of_pointwise hM fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
  have a := Hs _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have b := Ht _ h y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [e₁, e₂, BoxFamScalar.sval_of_secScal H₁ ρ₁ y hJ₁, BoxFamScalar.sval_of_secScal H₂ ρ₂ y hJ₂,
    BoxFamScalar.gs_scal π₁, BoxFamScalar.gs_scal π₂, c₁, c₂] at b
  simp only [Category.id_comp] at a ⊢
  simp only [e] at b
  have m : scal π (r₁ * r₂) = scal π r₁ * scal π r₂ := by simp only [scal, map_mul]
  rw [m, gs_mul _ y ⊤ trivial]
  refine (Units.mul_right_inj _).1 (b.trans ?_)
  rw [_root_.mul_mul_mul_comm, ← a, mul_left_comm]

end Generic

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D : DegData R I}
  {A₁ A₂ A : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
  {p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A} {p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A} {q₁ : D.toPre.X →+ D₁.toPre.X}
  {q₂ : D.toPre.X →+ D₂.toPre.X} {a₁ : A.A ⟶ A₁.A} {a₂ : A.A ⟶ A₂.A}

theorem exists_gt (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂)
    (w : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (hw : w.IsGen)
    (hc : IsBoxGen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (φ₁ := thφ D₁.toPre.P.A (x3 D₁.toPre.P.A))
      (φ₂ := thφ D₂.toPre.P.A (x3 D₂.toPre.P.A)) (ε := thε) w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left
      D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t)
    (e : ℕ) (g₁ : GtCoord I D₁.toPre e G₁) (g₂ : GtCoord I D₂.toPre e G₂) :
    ∃ g : GtCoord I D.toPre e (G₁ ⊗ G₂),
      g.q ≫ (Over.pullback (thick R I e)).map p₁ = (Over.pullback (thick R I e)).map (fst G₁ G₂) ≫ g₁.q ∧
      g.q ≫ (Over.pullback (thick R I e)).map p₂ = (Over.pullback (thick R I e)).map (snd G₁ G₂) ≫ g₂.q ∧
      (∀ h : D₁.toPre.X → D.toPre.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) →
        ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X,
          TorusHomOf h τ ∧ g.i ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂) = τ ≫ g₁.i) ∧
      (∀ h : D₂.toPre.X → D.toPre.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) →
        ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
          TorusHomOf h τ ∧ g.i ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂) = τ ≫ g₂.i) ∧
      ∀ x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left)
        (Y₂ := (thickObj R I e G₂).left) w ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left (g.t x) (g₁.t (q₁ x)) (g₂.t (q₂ x)) := by
  obtain ⟨q, i, q_hom, q_flat, q_surj, q_aff, i_hom, hker, hq₁, hq₂, hi₁, hi₂⟩ :=
    GlobalTheory.T.torusExtension_product_over_thickening_of_sumData R I e D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ G₁ G₂ g₁ g₂ hD
  have := hD.hom₁
  have := hD.hom₂
  have hp₁ := pG_pr hq₁
  have hp₂ := pG_pr hq₂
  choose t ht H using fun x : D.toPre.X => exists_boxGen w hw D₁.toPre.P.isLB D₂.toPre.P.isLB D.toPre.P.isLB
    (Oφ_pr hD.c_pr₁ hp₁ x) (Oφ_pr hD.c_pr₂ hp₂ x) (g₁.t (q₁ x)) (g₁.t_gen _) (g₂.t (q₂ x)) (g₂.t_gen _)
  have e₂ : (Over.map (thick R I e)).map η[thickObj R I e (G₁ ⊗ G₂)] ≫
      ((Over.map (thick R I e)).map q ≫ D.toPre.prBe I e) = 1 := by
    rw [← Category.assoc, ← Functor.map_comp, IsMonHom.one_hom]
    refine Over.OverMorphism.ext ((cubeMapOf (isGrpPullback_pullback D.toPre.P.A (thick R I e))).e_comm.trans ?_)
    show thick R I e ≫ η[D.toPre.P.A].left = (𝟙 _ ≫ thick R I e) ≫ η[D.toPre.P.A].left
    rw [Category.id_comp]
  have aq : ((fst (splitTorus _ D.toPre.X) (thickObj R I e (G₁ ⊗ G₂)) ≫ i) * snd _ _) ≫ q = snd _ _ ≫ q := by
    rw [MonObj.mul_comp, Category.assoc, hker.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  have aO : (Over.map (thick R I e)).map (lift (fst (splitTorus _ D.toPre.X) (thickObj R I e (G₁ ⊗ G₂)) ≫ i)
        (snd _ _) ≫ μ[thickObj R I e (G₁ ⊗ G₂)]) ≫ ((Over.map (thick R I e)).map q ≫ D.toPre.prBe I e) =
      (Over.map (thick R I e)).map (snd (splitTorus _ D.toPre.X) (thickObj R I e (G₁ ⊗ G₂))) ≫
        ((Over.map (thick R I e)).map q ≫ D.toPre.prBe I e) := by
    rw [← Category.assoc, ← Functor.map_comp, ← Hom.mul_def, aq, Functor.map_comp, Category.assoc]
  choose j₁ hj₁ using fun y : D₁.toPre.X => hD.xsum.2 (y, 0)
  choose j₂ hj₂ using fun y : D₂.toPre.X => hD.xsum.2 (0, y)
  obtain ⟨τ₁, hτ₁, hκ₁⟩ := hi₁ j₁ (fun y => congrArg Prod.fst (hj₁ y)) (fun y => congrArg Prod.snd (hj₁ y))
  obtain ⟨τ₂, hτ₂, hκ₂⟩ := hi₂ j₂ (fun y => congrArg Prod.fst (hj₂ y)) (fun y => congrArg Prod.snd (hj₂ y))
  have hj : ∀ χ, j₁ (q₁ χ) + j₂ (q₂ χ) = χ := fun χ => hD.xsum.1 (by
    rw [map_add, hj₁, hj₂, Prod.mk_add_mk, add_zero, zero_add]; rfl)
  exact ⟨⟨q, q_hom, q_flat, q_surj, q_aff, i, i_hom, hker, t, ht,
    GlobalTheory.ProdUnif.tMul_of_box R _ _ _ p₁ p₂ q₁ q₂ hD w hc _ _ _ _ g₁.pG g₂.pG _ _ hp₁ hp₂ t g₁.t g₂.t H g₁.t_mul g₂.t_mul,
    fun χ => GlobalTheory.ProdUnifUnit.unit_box R _ _ _ p₁ p₂ q₁ q₂ w _ (thick R I e) _ _ _ _ _ _ g₁.pG g₂.pG χ (t χ) _ _ inferInstance
      inferInstance (H χ) e₂ (g₁.t_unit _) (g₂.t_unit _),
    fun χ => GlobalTheory.ProdUnifWeight.weight_box₂ R _ _ _ p₁ p₂ q₁ q₂ w _ (thick R I e) _ _ _ _ _ _ g₁.pG g₂.pG χ (t χ) _ _ inferInstance
      inferInstance (H χ) i g₁.i g₂.i j₁ j₂ τ₁ τ₂ (hj χ) hτ₁ hτ₂ hκ₁ hκ₂ aO (g₁.t_weight _) (g₂.t_weight _)⟩,
    hq₁, hq₂, hi₁, hi₂, H⟩

theorem thickMap_pG (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂) (U₁ : UnifPre I D₁ A₁ G₁)
    (U₂ : UnifPre I D₂ A₂ G₂) (gt : ∀ e, GtCoord I D.toPre e (G₁ ⊗ G₂))
    (h₁ : ∀ e, (gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left)
    (h₂ : ∀ e, (gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left) (e : ℕ) :
    thickMap R I e (G₁ ⊗ G₂) ≫ (gt (e + 1)).pG.left = (gt e).pG.left := by
  have := hD.lim
  have h : LevelCompat.thickMapOver I e (G₁ ⊗ G₂) ≫ (gt (e + 1)).pG = (gt e).pG := SumDeg.pt_ext p₁ p₂
    (Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (thickMap R I e (G₁ ⊗ G₂) ≫ ·) (h₁ (e + 1))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (U₁.gt (e + 1)).pG.left) (thickMap_nat I e (fst G₁ G₂))).trans
        ((Category.assoc _ _ _).trans ((congrArg (((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ ·) (U₁.gt_q e)).trans (h₁ e).symm)))))))
    (Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (thickMap R I e (G₁ ⊗ G₂) ≫ ·) (h₂ (e + 1))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (U₂.gt (e + 1)).pG.left) (thickMap_nat I e (snd G₁ G₂))).trans
        ((Category.assoc _ _ _).trans ((congrArg (((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ ·) (U₂.gt_q e)).trans (h₂ e).symm)))))))
  exact congrArg (fun z => z.left) h

set_option maxHeartbeats 1600000 in

theorem exists_pre (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂) (hA : IsSumPolAV A A₁ A₂ a₁ a₂)
    (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂)
    (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left))
    (hM : StrBox p₁ p₂ wM D.toPre.rig D₁.toPre.rig D₂.toPre.rig D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t
      D.toPre.sym D₁.toPre.sym D₂.toPre.sym) :
    ∃ (U : UnifPre I D A (G₁ ⊗ G₂)) (wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)),
      IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ ∧ wL.IsGen ∧
      (∀ e x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left)
        (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x))) ∧
      ∀ e, BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
        (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left := by
  obtain ⟨wM_gen, mr, mc, ms⟩ := hM
  obtain ⟨gen, gen_hom, gen₁, gen₂, ext⟩ := GlobalTheory.T.exists_genericFibre_product_sumPolarisedAbelianVariety R I D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ A a₁ a₂ hA
  obtain ⟨L, c, s, wL, s_gen, s_rig, hwLgen, lr, lc, ls⟩ := GlobalTheory.T.exists_externalTensor_rigidified_cubical_product _ G₁ G₂ U₁.LG U₂.LG U₁.cubG U₂.cubG U₁.symG U₂.symG
    U₁.symG_gen U₂.symG_gen U₁.symG_rig U₂.symG_rig
  choose gt hq₁ hq₂ hi₁ hi₂ ht using fun e => exists_gt hD wM wM_gen mc e (U₁.gt e) (U₂.gt e)
  have hp₁ : ∀ e, (gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left :=
    fun e => congrArg (fun z => z.left) (pG_pr (hq₁ e))
  have hp₂ : ∀ e, (gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left :=
    fun e => congrArg (fun z => z.left) (pG_pr (hq₂ e))
  choose w w_gen Q using fun e => GlobalTheory.T.exists_generating_boxProduct_of_restrictedIsos (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
    (T₂ := (thickObj R I e G₂).left) wM wL (U₁.w e) (U₂.w e) D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB L.isLB
    U₁.LG.isLB U₂.LG.isLB (hp₁ e) (hp₂ e) (thick_fstG I e _) (thick_fstG I e _) wM_gen hwLgen (U₁.w_gen e) (U₂.w_gen e)
  have gq := thickMap_pG hD U₁ U₂ gt hp₁ hp₂
  have := U₁.smooth
  have := U₂.smooth
  have := U₁.separated
  have := U₂.separated
  refine ⟨{
      smooth := inferInstanceAs (Smooth (pullback.fst G₁.hom G₂.hom ≫ G₁.hom))
      separated := inferInstanceAs (IsSeparated (pullback.fst G₁.hom G₂.hom ≫ G₁.hom))
      gen := gen
      gen_hom := gen_hom
      LG := L
      cubG := c
      symG := s
      symG_gen := s_gen
      symG_rig := s_rig
      ext := ext L.L wL L.isLB hwLgen
      gt := gt
      gt_q := gq
      gt_t := fun e χ => corr_box (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left)
        (Y₂ := (thickObj R I e G₂).left) (W := (thickObj R I (e + 1) (G₁ ⊗ G₂)).left)
        (W₁ := (thickObj R I (e + 1) G₁).left) (W₂ := (thickObj R I (e + 1) G₂).left)
        D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB (LevelCompat.thickMap_Oφ (gt e) (gt (e + 1)) (gq e) χ)
        (thickMap_nat I e _) (thickMap_nat I e _) (ht e χ) (ht (e + 1) χ) (U₁.gt_t e _) (U₂.gt_t e _)
      w := w
      w_gen := w_gen
      w_rig := fun e => GlobalTheory.ProdUnif.rigAlong_box (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
        (T₂ := (thickObj R I e G₂).left) wM wL (U₁.w e) (U₂.w e) D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB L.isLB
        U₁.LG.isLB U₂.LG.isLB (hp₁ e) (hp₂ e) (thick_fstG I e _) (thick_fstG I e _) (w e) (Q e)
        (eSec (thickObj R I e (G₁ ⊗ G₂))) (eSec (thickObj R I e G₁)) (eSec (thickObj R I e G₂)) (thick R I e)
        L.rig U₁.LG.rig U₂.LG.rig D.toPre.rig D₁.toPre.rig D₂.toPre.rig
        (BoxSymmetry.eSec_comp_hom ((Over.pullback (thick R I e)).map (fst G₁ G₂))) (BoxSymmetry.eSec_comp_hom ((Over.pullback (thick R I e)).map (snd G₁ G₂)))
        (UnifPullRig.eSec_fstG I e _) (UnifPullRig.eSec_pG I (gt e)) (UnifPullRig.eSec_fstG I e _)
        (UnifPullRig.eSec_pG I (U₁.gt e)) (UnifPullRig.eSec_fstG I e _) (UnifPullRig.eSec_pG I (U₂.gt e)) lr mr
        (U₁.w_rig e) (U₂.w_rig e)
      w_even := fun e => by
        have := (gt e).q_hom
        have := (U₁.gt e).q_hom
        have := (U₂.gt e).q_hom
        exact GlobalTheory.ProdUnif.even_box₂ (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
          (T₂ := (thickObj R I e G₂).left) wM wL (U₁.w e) (U₂.w e) D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB
          L.isLB U₁.LG.isLB U₂.LG.isLB (hp₁ e) (hp₂ e) (thick_fstG I e _) (thick_fstG I e _) (w e) (Q e)
          (ι[thickObj R I e (G₁ ⊗ G₂)]).left (ι[thickObj R I e G₁]).left (ι[thickObj R I e G₂]).left
          s U₁.symG U₂.symG D.toPre.sym D₁.toPre.sym D₂.toPre.sym
          (EvenPull.inv_left_comp ((Over.pullback (thick R I e)).map (fst G₁ G₂))) (EvenPull.inv_left_comp ((Over.pullback (thick R I e)).map (snd G₁ G₂)))
          (EvenPull.inv_fst _ (G₁ ⊗ G₂)) (EvenPull.inv_hom_fst _ _ (gt e).q) (EvenPull.inv_fst _ G₁)
          (EvenPull.inv_hom_fst _ _ (U₁.gt e).q) (EvenPull.inv_fst _ G₂) (EvenPull.inv_hom_fst _ _ (U₂.gt e).q) ls ms
          (U₁.w_even e) (U₂.w_even e)
      w_cub := fun e => GlobalTheory.T.thickeningProductIso_preserves_cubicalStructure R I D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D p₁ p₂ q₁ q₂ hD wM L.L c.t wL L.isLB mc lc e (gt e) (hp₁ e)
        (hp₂ e) (w e) (Q e)
      w_compat := fun e => GlobalTheory.ProdUnif.compat_box₂ (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
        (T₂ := (thickObj R I e G₂).left) wM wL (U₁.w e) (U₂.w e) D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB L.isLB
        U₁.LG.isLB U₂.LG.isLB (hp₁ e) (hp₂ e) (thick_fstG I e _) (thick_fstG I e _) (w e) (Q e)
        (T' := (thickObj R I (e + 1) (G₁ ⊗ G₂)).left) (T₁' := (thickObj R I (e + 1) G₁).left)
        (T₂' := (thickObj R I (e + 1) G₂).left) (w (e + 1)) (U₁.w (e + 1)) (U₂.w (e + 1)) (Q (e + 1))
        (thickMap R I e (G₁ ⊗ G₂)) (thickMap R I e G₁) (thickMap R I e G₂) (thickMap_nat I e _) (thickMap_nat I e _)
        (UnifPullRig.thickMap_fstG I e _) (gq e) (UnifPullRig.thickMap_fstG I e _) (U₁.gt_q e)
        (UnifPullRig.thickMap_fstG I e _) (U₂.gt_q e) (U₁.w_compat e) (U₂.w_compat e) },
    wL, ⟨gen₁, gen₂, ⟨wL, hwLgen⟩, hq₁, hq₂, hi₁, hi₂⟩, hwLgen, ht, Q⟩

set_option maxHeartbeats 1600000 in

theorem expands_box (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂)
    {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U : UnifPre I D A (G₁ ⊗ G₂)}
    {wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)} (hwM : wM.IsGen)
    {wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)} (hwL : wL.IsGen)
    (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂)
    (ht : ∀ e x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left)
        (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x)))
    (Q : ∀ e, BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
        (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left) {k : ℕ} {s : U.SecK k} {s₁ : U₁.SecK k} {s₂ : U₂.SecK k}
    (hs : IsBoxSec (Y := pullback (G₁ ⊗ G₂).hom (jK R)) (Y₁ := pullback G₁.hom (jK R)) (Y₂ := pullback G₂.hom (jK R))
      wL ((Over.pullback (jK R)).map (fst G₁ G₂)).left ((Over.pullback (jK R)).map (snd G₁ G₂)).left s s₁ s₂)
    {E : Fam D.toPre (FractionRing R) k} {E₁ : Fam D₁.toPre (FractionRing R) k} {E₂ : Fam D₂.toPre (FractionRing R) k}
    (hE : IsBoxFam₂ p₁ p₂ q₁ q₂ wM (FractionRing R) k E E₁ E₂) (H₁ : U₁.Expands k s₁ E₁) (H₂ : U₂.Expands k s₂ E₂) :
    U.Expands k s E := by
  obtain ⟨r₁, hr₁, σ₁, f₁, a₁, b₁, c₁⟩ := H₁
  obtain ⟨r₂, hr₂, σ₂, f₂, a₂, b₂, c₂⟩ := H₂
  have := hD.hom₁
  have := hD.hom₂
  obtain ⟨σ, hσ⟩ := exists_boxSec (φ := fun _ : Fin 1 => 𝟙 (G₁ ⊗ G₂).left) (h₁ := (fst G₁ G₂).left)
    (h₂ := (snd G₁ G₂).left) wL hwL U₁.LG.isLB U₂.LG.isLB U.LG.isLB
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) σ₁ σ₂
  choose f hf using fun α => exists_boxSec wM hwM D₁.toPre.P.isLB D₂.toPre.P.isLB D.toPre.P.isLB
    (famφB_pr hD.c_pr₁ α) (famφB_pr hD.c_pr₂ α) (f₁ (q₁ α)) (f₂ (q₂ α))
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, σ, f, ?_, fun α => ?_, fun e => ?_⟩
  · refine secScal_box U.LG.isLB U₁.LG.isLB U₂.LG.isLB (fun _ => Category.comp_id _)
      (pullback.lift_fst _ _ _).symm (pullback.lift_fst _ _ _).symm hs hσ ?_ ?_ a₁ a₂
    · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (Over.w ((Over.pullback (jK R)).map (fst G₁ G₂))))
    · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (Over.w ((Over.pullback (jK R)).map (snd G₁ G₂))))
  · refine secScal_box D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB (fun a => ?_)
      (congrArg (fun m => m.left) (whiskerLeft_snd (TF (R := R) (FractionRing R)) p₁).symm)
      (congrArg (fun m => m.left) (whiskerLeft_snd (TF (R := R) (FractionRing R)) p₂).symm) (hE α) (hf α)
      (Over.w _) (Over.w _) (b₁ _) (b₂ _)
    fin_cases a
    · exact Category.comp_id _
    · refine congrArg (fun m : DegPre.BF D.toPre (FractionRing R) ⟶ D.toPre.P.A => m.left)
        (?_ : DegPre.prB D.toPre (FractionRing R) ≫ (𝟙 _ * cP D.toPre _ α) =
          DegPre.prB D.toPre (FractionRing R) * cP D.toPre _ α)
      rw [MonObj.comp_mul, Category.comp_id, comp_cP]
    · exact congrArg (fun m => m.left) (comp_cP D.toPre (DegPre.prB D.toPre (FractionRing R)) α)
    · exact congrArg (fun m : DegPre.BF D.toPre (FractionRing R) ⟶ D.toPre.P.A => m.left)
        (MonObj.comp_one (M := D.toPre.P.A) (DegPre.prB D.toPre (FractionRing R)))
  · exact GlobalTheory.T.expansionModIdealPow_boxProduct_eq_boxProduct R I D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D p₁ p₂ q₁ q₂ A U hD.xsum wM wL e k
      (congrArg (fun z => z.left) (pG_pr (hU.q_pr₁ e))) (congrArg (fun z => z.left) (pG_pr (hU.q_pr₂ e))) (ht e) (Q e)
      σ σ₁ σ₂ f f₁ f₂ hσ hf (c₁ e) (c₂ e)

theorem exists_unif (hR : AdmBase R I) (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂)
    (hA : IsSumPolAV A A₁ A₂ a₁ a₂) (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) :
    ∃ U : Unif I D A (G₁ ⊗ G₂), IsProdUnif U₁.toUnifPre U₂.toUnifPre U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ := by
  obtain ⟨wM, hM, hψ⟩ := GlobalTheory.ProdUnif.exists_strBox_of_isSumDeg R _ _ _ p₁ p₂ q₁ q₂ hD
  obtain ⟨U, wL, hU, hwL, ht, Q⟩ := exists_pre hD hA U₁.toUnifPre U₂.toUnifPre wM hM
  refine ⟨⟨U, fun k hk => ?_⟩, hU⟩
  classical
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hf₁, hd₁⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D₁ (FractionRing R) k hk
  obtain ⟨hf₂, hd₂⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D₂ (FractionRing R) k hk
  obtain ⟨hf, hd⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) k hk
  have hg := GlobalTheory.ProdDim.g_eq_add _ D.toPre.P D₁.toPre.P D₂.toPre.P p₁ p₂ inferInstance hD.lim
  have hg' := GlobalTheory.ProdDim.g_eq_add _ A A₁ A₂ a₁ a₂ inferInstance hA.lim
  have hr : D.toPre.rank = D₁.toPre.rank + D₂.toPre.rank := by
    show Module.finrank ℤ D.toPre.X = Module.finrank ℤ D₁.toPre.X + Module.finrank ℤ D₂.toPre.X
    rw [(AddEquiv.ofBijective _ hD.xsum).toIntLinearEquiv.finrank_eq, Module.finrank_prod]
  have n₁ := GlobalTheory.ProdUnif.famDim_of_expBij R I D₁ A₁ G₁ U₁.toUnifPre k hk (U₁.expand k hk)
  have n₂ := GlobalTheory.ProdUnif.famDim_of_expBij R I D₂ A₂ G₂ U₂.toUnifPre k hk (U₂.expand k hk)
  let b₁ := Module.finBasisOfFinrankEq (FractionRing R) (Fam D₁.toPre (FractionRing R) k) n₁
  let b₂ := Module.finBasisOfFinrankEq (FractionRing R) (Fam D₂.toPre (FractionRing R) k) n₂
  choose σ₁ hσ₁ using fun l => ((U₁.expand k hk).2 (b₁ l)).exists
  choose σ₂ hσ₂ using fun l => ((U₂.expand k hk).2 (b₂ l)).exists
  choose b hb using fun a : Fin (k ^ A₁.g) × Fin (k ^ A₂.g) =>
    GlobalTheory.T.exists_boxFamily_productDegeneration R _ _ _ p₁ p₂ q₁ q₂ hD wM hM.1 hM.2.1 hψ (FractionRing R) k (b₁ a.1) (b₂ a.2)
  choose σ hσ using fun a : Fin (k ^ A₁.g) × Fin (k ^ A₂.g) =>
    exists_boxSec (Y := pullback (G₁ ⊗ G₂).hom (jK R)) (Y₁ := pullback G₁.hom (jK R)) (Y₂ := pullback G₂.hom (jK R))
      (φ := fun _ : Fin 1 => pullback.fst (G₁ ⊗ G₂).hom (jK R))
      (h₁ := ((Over.pullback (jK R)).map (fst G₁ G₂)).left) (h₂ := ((Over.pullback (jK R)).map (snd G₁ G₂)).left)
      wL hwL U₁.LG.isLB U₂.LG.isLB U.LG.isLB (fun _ => (pullback.lift_fst _ _ _).symm)
      (fun _ => (pullback.lift_fst _ _ _).symm) (σ₁ a.1) (σ₂ a.2)
  have hli := GlobalTheory.T.boxFamily_linearIndependent_productDegeneration R _ _ _ p₁ p₂ q₁ q₂ hD wM (FractionRing R) k _ _ b₁ b₂ b b₁.linearIndependent
    b₂.linearIndependent hb
  have hc : Fintype.card (Fin (k ^ A₁.g) × Fin (k ^ A₂.g)) = k ^ A₁.g * k ^ A₂.g := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hcard : Fintype.card (Fin (k ^ A₁.g) × Fin (k ^ A₂.g)) =
      Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) := by
    rw [hc, ← n₁, ← n₂, hd, hd₁, hd₂, hr, hg, ← pow_add, add_add_add_comm]
  haveI : Nonempty (Fin (k ^ A₁.g) × Fin (k ^ A₂.g)) := ⟨⟨0, pow_pos hk _⟩, ⟨0, pow_pos hk _⟩⟩
  refine GlobalTheory.ProdUnif.expBij_of_basis_card R I D A _ U k hR hk _ (basisOfLinearIndependentOfCardEqFinrank hli hcard) σ
    (by rw [hc, hg', pow_add]) (fun a => ?_)
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact expands_box hD hM.1 hwL hU ht Q (hσ a) (hb a) (hσ₁ _) (hσ₂ _)

end Main

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), IsProdUnif U₁.toUnifPre U₂.toUnifPre U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ := by
  intro R _ _ _ hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  exact exists_unif hR.1 hD hA U₁ U₂

end GlobalTheory.ProdUnifExists
