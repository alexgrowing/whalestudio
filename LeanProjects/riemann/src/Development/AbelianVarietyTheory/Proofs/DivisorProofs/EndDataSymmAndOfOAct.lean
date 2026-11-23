import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.RosatiSymmetry

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

theorem padd_comm' {T : Over S} (x y : T ⟶ A) : padd A x y = padd A y x := by
  show x * y = y * x
  exact mul_comm x y

abbrev sw : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)

theorem sw_padd (x y : A ⊗ A ⟶ A) : sw A ≫ padd A x y = padd A (sw A ≫ x) (sw A ≫ y) := by
  simp only [padd, comp_lift_assoc]

theorem formEq_sw (f g : A ⟶ A) (Y : Scheme.{0}) (p : Y ⟶ (A ⊗ A).left) :
    FormEq (fun k => p ≫ (sw A).left ≫ rosatiφ A g f k) (fun k => - rosatiε k)
      (fun k => p ≫ rosatiφ A f g k) rosatiε := by
  intro U _ h
  have e0 : (sw A).left ≫ (padd A (fst A A ≫ g) (snd A A)).left = (padd A (fst A A) (snd A A ≫ g)).left := by
    rw [← Over.comp_left, sw_padd, padd_comm']; simp only [lift_fst_assoc, lift_snd]
  have e1 : (sw A).left ≫ (fst A A ≫ g).left = (snd A A ≫ g).left := by
    rw [← Over.comp_left, lift_fst_assoc]
  have e2 : (sw A).left ≫ (snd A A).left = (fst A A).left := by
    rw [← Over.comp_left, lift_snd]
  have e3 : (sw A).left ≫ (padd A (fst A A) (snd A A ≫ f)).left = (padd A (fst A A ≫ f) (snd A A)).left := by
    rw [← Over.comp_left, sw_padd, padd_comm']; simp only [lift_fst, lift_snd_assoc]
  have e4 : (sw A).left ≫ (fst A A).left = (snd A A).left := by
    rw [← Over.comp_left, lift_fst]
  have e5 : (sw A).left ≫ (snd A A ≫ f).left = (fst A A ≫ f).left := by
    rw [← Over.comp_left, lift_snd_assoc]
  simp only [Fin.prod_univ_six, rosatiφ, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.head_cons, e0, e1, e2, e3, e4, e5]
  simp only [neg_neg, zpow_neg, zpow_one]
  ac_rfl

theorem formEq_sw' (f g : A ⟶ A) :
    FormEq (fun k => (sw A).left ≫ rosatiφ A g f k) (fun k => - rosatiε k) (rosatiφ A f g) rosatiε := by
  simpa only [Category.id_comp] using formEq_sw A f g _ (𝟙 _)

theorem rosatiAdj_symm (L : LB A.left) (hL : L.IsLB) (f g : A ⟶ A) (h : RosatiAdj A L f g) : RosatiAdj A L g f := by
  intro s
  obtain ⟨U, hs, t, ht⟩ := h s
  refine ⟨U, hs, ?_⟩
  have hW : (A ⊗ A).hom ⁻¹ᵁ U ≤ (sw A).left ⁻¹ᵁ ((A ⊗ A).hom ⁻¹ᵁ U) := by
    intro x hx
    show ((sw A).left ≫ (A ⊗ A).hom) x ∈ U
    rw [Over.w]; exact hx
  let σ := (sw A).left.resLE ((A ⊗ A).hom ⁻¹ᵁ U) ((A ⊗ A).hom ⁻¹ᵁ U) hW
  have hσ : σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (sw A).left := Scheme.Hom.resLE_comp_ι _ _
  have hF : FormEq (fun k => σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g k) (fun k => - rosatiε k)
      (fun k => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A g f k) rosatiε := by
    have e : (fun k => σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g k) =
        fun k => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (sw A).left ≫ rosatiφ A f g k := by
      funext k; rw [← Category.assoc, hσ, Category.assoc]
    rw [e]; exact formEq_sw A g f _ _
  obtain ⟨t', ht', -⟩ := exists_gen hL hF (LB.invGen L _ _ (LB.pullGen L _ _ t σ))
    (DVR.invGen_isGen L _ _ _ (DVR.pullGen_isGen L _ _ t ht σ))
  exact ⟨t', ht'⟩

end GlobalTheory.Mum.RosatiSymmetry

namespace GlobalTheory.Mum.RosatiSymmetry
variable {R : Type} [CommRing R] [IsDomain R]

theorem val_tau_symm (D : DegPre R) {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
    (r : Z ⟶ (TK R).left) (a b : D.X) : val (D.tau a b) r z J = val (D.tau b a) r z J := by
  simp only [DegPre.tau, val_mul hJ, val_inv]
  have e : val (D.psi (a + b)) r z J = val (D.psi (b + a)) r z J := by rw [add_comm]
  rw [e, mul_right_comm (val (D.psi (b + a)) r z J)]

theorem tauBal_symm (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (a a' : D.X → D.X) (H : D.TauBal f g a a') :
    D.TauBal g f a' a := by
  intro u' hu' hn y y'
  have hL := D.P.isLB
  obtain ⟨u, hu, hv⟩ := exists_gen hL (formEq_sw' D.P.A f g)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u' (sw D.P.A).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ u' hu' _))
  have hz : zero2 D.P.A ≫ (sw D.P.A).left = zero2 D.P.A := by
    rw [zero2, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hp : D.pt2 y' y ≫ (sw D.P.A).left = D.pt2 y y' := by
    rw [DegPre.pt2, DegPre.pt2, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hnu : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) := by
    refine corr_of_val hL fun z J hJ => ?_
    have h1 := val_corr hJ hn (𝟙 _)
    rw [val_pull hJ, val_one] at h1
    rw [val_pull hJ, val_one, hv _ _ _ _ hJ, val_inv, val_pull hJ, Category.assoc, hz, h1, inv_one]
  have H' := H u hu hnu y' y
  refine corr_of_val hL fun z J hJ => ?_
  have h2 := val_corr hJ H' (𝟙 _)
  rw [val_mul hJ, val_pull hJ, hv _ _ _ _ hJ, val_inv, val_pull hJ, Category.assoc, hp] at h2
  rw [val_mul hJ, val_pull hJ, val_tau_symm D hJ _ (a' y) y', ← h2, val_tau_symm D hJ _ (a y') y]
  group

end GlobalTheory.Mum.RosatiSymmetry

namespace GlobalTheory.Mum

theorem endData_symm_and_ofOAct : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R),
    (∀ (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X), EndData D a a' h h' → EndData D a' a h' h) ∧
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.X] (o : D.OAct O) (x : O),
      EndData D (o.onB.act x) (o.onB.act (star x)) (DistribMulAction.toAddMonoidHom D.X x)
        (DistribMulAction.toAddMonoidHom D.X (star x)) := by
  intro R _ _ D
  refine ⟨fun a a' h h' ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h2, h1, RosatiSymmetry.rosatiAdj_symm D.P.A D.P.L D.P.isLB a a' h3,
    h5, h4, RosatiSymmetry.tauBal_symm D a a' h h' h6⟩, fun O _ _ _ o x => ?_⟩
  exact ⟨o.onB.hom x, o.onB.hom (star x), o.onB.rosati x, fun y => o.c_lin x y, fun y => o.c_lin (star x) y,
    o.tau_bal x⟩

end GlobalTheory.Mum
