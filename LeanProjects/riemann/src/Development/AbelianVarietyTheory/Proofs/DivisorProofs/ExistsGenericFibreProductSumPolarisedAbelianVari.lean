import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdGen

theorem isMonHom_of_lift {S : Scheme.{0}} {H A A₁ A₂ : Over S} [GrpObj H] [GrpObj A] [GrpObj A₁] [GrpObj A₂]
    (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsMonHom a₁] [IsMonHom a₂] [IsIso (lift a₁ a₂)] (f : H ⟶ A)
    [IsMonHom (f ≫ a₁)] [IsMonHom (f ≫ a₂)] : IsMonHom f := by
  have ext : ∀ {T : Over S} (a b : T ⟶ A), a ≫ a₁ = b ≫ a₁ → a ≫ a₂ = b ≫ a₂ → a = b :=
    fun a b h₁ h₂ => (cancel_mono (lift a₁ a₂)).1 (by rw [comp_lift, comp_lift, h₁, h₂])
  constructor
  · refine ext _ _ ?_ ?_ <;> rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine ext _ _ ?_ ?_ <;>
      rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        tensorHom_comp_tensorHom]

theorem exists_iso_prod {S S' : Scheme.{0}} (j : S' ⟶ S) (G₁ G₂ : Over S) {A A₁ A₂ : Over S'}
    (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsIso (lift a₁ a₂)] (e₁ : (Over.pullback j).obj G₁ ≅ A₁)
    (e₂ : (Over.pullback j).obj G₂ ≅ A₂) :
    ∃ e : (Over.pullback j).obj (G₁ ⊗ G₂) ≅ A,
      e.hom ≫ a₁ = (Over.pullback j).map (fst G₁ G₂) ≫ e₁.hom ∧
      e.hom ≫ a₂ = (Over.pullback j).map (snd G₁ G₂) ≫ e₂.hom := by
  have h₁ : inv (lift a₁ a₂) ≫ a₁ = fst A₁ A₂ := by rw [IsIso.inv_comp_eq, lift_fst]
  have h₂ : inv (lift a₁ a₂) ≫ a₂ = snd A₁ A₂ := by rw [IsIso.inv_comp_eq, lift_snd]
  refine ⟨prodComparisonIso (Over.pullback j) G₁ G₂ ≪≫ (e₁ ⊗ᵢ e₂) ≪≫ (asIso (lift a₁ a₂)).symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, h₁, tensorIso_hom, tensorHom_fst,
      prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst_assoc]
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, h₂, tensorIso_hom, tensorHom_snd,
      prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd_assoc]

open GlobalTheory.CechPic in

theorem cls_extLB {X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (hL : L.IsLB) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (hw : w.IsGen) :
    cls L hL = pull f₁ (cls L₁ h₁) + pull f₂ (cls L₂ h₂) :=
  (cls_eq_iff hL (isLB_extLB h₁ h₂ f₁ f₂)).2 ⟨w, hw⟩

open GlobalTheory.CechPic in

theorem exists_gen_prod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (A : PolAV (Sp (FractionRing R))) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ gen : (Over.pullback (jK R)).obj (G₁ ⊗ G₂) ≅ A.A, IsMonHom gen.hom ∧ gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom ∧ gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom ∧ ∀ (L : LB (G₁ ⊗ G₂).left) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → wL.IsGen → ∃ w : LB.Iso (A.L.pull gen.hom.left) (L.pull (pullback.fst (G₁ ⊗ G₂).hom (jK R))), w.IsGen := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ A a₁ a₂ hA
  haveI := hA.hom₁
  haveI := hA.hom₂
  haveI := hA.lim
  haveI := U₁.gen_hom
  haveI := U₂.gen_hom
  obtain ⟨e, e₁, e₂⟩ := exists_iso_prod (jK R) G₁ G₂ a₁ a₂ U₁.gen U₂.gen
  haveI : IsMonHom (e.hom ≫ a₁) := by rw [e₁]; infer_instance
  haveI : IsMonHom (e.hom ≫ a₂) := by rw [e₂]; infer_instance
  refine ⟨e, isMonHom_of_lift a₁ a₂ e.hom, e₁, e₂, fun L wL hL hwL => ?_⟩
  obtain ⟨wA, hwA⟩ := hA.w
  have cA := cls_extLB A.isLB A₁.isLB A₂.isLB wA hwA
  have cL := cls_extLB hL U₁.LG.isLB U₂.LG.isLB wL hwL
  have c₁ : pull U₁.gen.hom.left (cls _ A₁.isLB) = pull (pullback.fst G₁.hom (jK R)) (cls _ U₁.LG.isLB) :=
    (cls_eq_iff (pull_isLB A₁.isLB _) (pull_isLB U₁.LG.isLB _)).2 U₁.ext
  have c₂ : pull U₂.gen.hom.left (cls _ A₂.isLB) = pull (pullback.fst G₂.hom (jK R)) (cls _ U₂.LG.isLB) :=
    (cls_eq_iff (pull_isLB A₂.isLB _) (pull_isLB U₂.LG.isLB _)).2 U₂.ext
  have l₁ : e.hom.left ≫ a₁.left = ((Over.pullback (jK R)).map (fst G₁ G₂)).left ≫ U₁.gen.hom.left :=
    congrArg (fun z => z.left) e₁
  have l₂ : e.hom.left ≫ a₂.left = ((Over.pullback (jK R)).map (snd G₁ G₂)).left ≫ U₂.gen.hom.left :=
    congrArg (fun z => z.left) e₂
  have m₁ : ((Over.pullback (jK R)).map (fst G₁ G₂)).left ≫ pullback.fst G₁.hom (jK R) =
      pullback.fst (G₁ ⊗ G₂).hom (jK R) ≫ (fst G₁ G₂).left := pullback.lift_fst _ _ _
  have m₂ : ((Over.pullback (jK R)).map (snd G₁ G₂)).left ≫ pullback.fst G₂.hom (jK R) =
      pullback.fst (G₁ ⊗ G₂).hom (jK R) ≫ (snd G₁ G₂).left := pullback.lift_fst _ _ _
  have d₁ : pull e.hom.left (pull a₁.left (cls _ A₁.isLB)) =
      pull (pullback.fst (G₁ ⊗ G₂).hom (jK R)) (pull (fst G₁ G₂).left (cls _ U₁.LG.isLB)) :=
    (pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) l₁).trans ((pull_comp _ _ _).trans
      ((congrArg _ c₁).trans ((pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) m₁).trans
        (pull_comp _ _ _))))))
  have d₂ : pull e.hom.left (pull a₂.left (cls _ A₂.isLB)) =
      pull (pullback.fst (G₁ ⊗ G₂).hom (jK R)) (pull (snd G₁ G₂).left (cls _ U₂.LG.isLB)) :=
    (pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) l₂).trans ((pull_comp _ _ _).trans
      ((congrArg _ c₂).trans ((pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) m₂).trans
        (pull_comp _ _ _))))))
  exact (cls_eq_iff (pull_isLB A.isLB _) (pull_isLB hL _)).1
    ((congrArg (pull e.hom.left) cA).trans ((map_add _ _ _).trans ((congrArg₂ (· + ·) d₁ d₂).trans
      ((map_add _ _ _).symm.trans (congrArg (pull (pullback.fst (G₁ ⊗ G₂).hom (jK R))) cL).symm))))

end GlobalTheory.ProdGen
