import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

variable {R : Type} [CommRing R] [IsDomain R] {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A)
  [IsMonHom p₁] [IsMonHom p₂] (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left))

theorem isBoxGen_cub (hw : w.IsGen) :
    IsBoxGen w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D.P.isAb _) (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2)
  have he : e.left ≫ (snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (ε := thε)
    (fun a => (CubeMap.ofHom p₁).psum_comm a.down) (fun a => (CubeMap.ofHom p₂).psum_comm a.down)
    D.cub.isGen D₁.cub.isGen D₂.cub.isGen _ e.left he sj fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have C : IsCub (cubV D.cub s I) := isCub_cubV D.cub hI
  have C₁ : IsCub (cubV D₁.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₁) := isCub_cubV D₁.cub hI₁
  have C₂ : IsCub (cubV D₂.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₂) := isCub_cubV D₂.cub hI₂
  have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1 1 (om w s I₁ I₂ I)
  rw [_root_.mul_one, _root_.mul_one] at p
  have o₁ : e.left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₁.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₁ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have o₂ : e.left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₂.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₂ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have v₁ := (congrArg (fun m => val D₁.cub.t m s I₁) o₁).trans (C₁.face 1 1)
  have v₂ := (congrArg (fun m => val D₂.cub.t m s I₂) o₂).trans (C₂.face 1 1)
  exact (congrArg₂ (· * ·) p (C.face 1 1)).trans (Eq.trans (by simp) (congrArg₂ (· * ·) v₁ v₂).symm)

theorem isBoxGen_sym (hw : w.IsGen) : IsBoxGen w p₁.left p₂.left D.sym D₁.sym D₂.sym := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (inv_comp p₁) (inv_comp p₂)
    D.sym_gen D₁.sym_gen D₂.sym_gen D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2
    fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have q := prod_sym (eSec D.P.A) (om w s I₁ I₂ I)
  have o : eSec D.P.A ≫ (ι[D.P.A]).left = eSec D.P.A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[D.P.A] ≫ ι[D.P.A] = η[D.P.A])
  rw [o, mul_inv_cancel] at q
  rw [eSec_comp, eSec_comp, val_sym_zero D₁ hI₁, val_sym_zero D₂ hI₂]
  exact congrArg₂ (· * ·) q (val_sym_zero D hI)

theorem exists_strBox_of_isSumDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), StrBox p₁ p₂ w D.rig D₁.rig D₂.rig D.cub.t D₁.cub.t D₂.cub.t D.sym D₁.sym D₂.sym ∧ ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x)) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ h
  have := h.hom₁
  have := h.hom₂
  obtain ⟨w, hw, hr, hψ⟩ := h.w
  exact ⟨w, ⟨hw, isBoxGen_of_mapsAt w _ _ hr, isBoxGen_cub p₁ p₂ w hw, isBoxGen_sym p₁ p₂ w hw⟩,
    fun x => isBoxGen_of_mapsAt w _ _ (hψ x)⟩

end GlobalTheory.ProdUnif
