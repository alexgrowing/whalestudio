import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

noncomputable section

open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericFibreUnif

theorem exists_isGrpPullback_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (χ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t) (z : Sp (FractionRing R) ⟶ Xo.XF c), z ≫ Y.j = jK R ≫ χ → letI := H.starRing; ∃ ψ : P.A.A.left ⟶ Y.oF.t.G.left, IsGrpPullback P.A.A Y.oF.t.G z ψ ∧ LBIso P.A.L (Y.oF.t.PP.L.pull ψ) ∧ (∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ = ψ ≫ (Y.oF.t.act.act a).left) ∧ ψ ≫ Y.m.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y R _ _ I χ t m P z hz
  letI := H.starRing
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  set k : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hk
  have gpG : IsGrpPullback P.A.A t.G (jK R) k :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  have n₀ : IsGrpPullback P.A.A Y.t.G (jK R ≫ χ) (k ≫ m.φ) := gpG.comp m.cart
  have hw : (k ≫ m.φ) ≫ Y.t.G.hom = (P.A.A.hom ≫ z) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    refine n₀.1.w.trans ?_
    rw [← hz, Category.assoc]; rfl
  let ψ : P.A.A.left ⟶ Y.oF.t.G.left := Y.m.cart.1.lift (k ≫ m.φ) (P.A.A.hom ≫ z) hw
  have hψ₁ : ψ ≫ Y.m.φ = k ≫ m.φ := Y.m.cart.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ Y.oF.t.G.hom = P.A.A.hom ≫ z := Y.m.cart.1.lift_snd _ _ _
  have n : IsGrpPullback P.A.A Y.t.G (z ≫ (Y.jQ ≫ pullback.fst _ _)) (ψ ≫ Y.m.φ) :=
    n₀.congr hz.symm hψ₁.symm
  have cart : IsGrpPullback P.A.A Y.oF.t.G z ψ := Y.m.cart.cancel n hψ₂
  have actA : ∀ x, (P.oA.act x).left ≫ k = k ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [hk, ← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have B₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull k) :=
    LBIso.chartPull (chartPullSame P.A.L (fun _ => 𝟙 _) (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left
        (fun _ => hgi.symm))
      (chartPullSame P.U.LG.L (fun _ => k) (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left
        (fun _ => rfl)) P.U.ext
  have B₁' : LBIso P.A.L (t.PP.L.pull k) := by
    rw [← P.bundle]
    exact LBIso.chartPull (chartPullUnpull P.A.L (𝟙 _) rfl) (chartPullId _) B₁
  obtain ⟨w₂, -, g₂, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have B₂ : LBIso (t.PP.L.pull k) (Y.t.PP.L.pull (ψ ≫ Y.m.φ)) :=
    LBIso.chartPull (chartPullPull t.PP.L k k rfl)
      (chartPullSame Y.t.PP.L (fun _ => ψ ≫ Y.m.φ) (fun _ => m.φ) _ k (fun _ => hψ₁.trans (Category.assoc _ _ _)))
      ⟨w₂, g₂⟩
  obtain ⟨w₃, -, g₃, -⟩ := rigIso_congr rfl Y.m.cm Y.m.lin rfl rfl
  have B₃ : LBIso (Y.oF.t.PP.L.pull ψ) (Y.t.PP.L.pull (ψ ≫ Y.m.φ)) :=
    LBIso.chartPull (chartPullPull Y.oF.t.PP.L ψ ψ rfl)
      (chartPullSame Y.t.PP.L (fun _ => ψ ≫ Y.m.φ) (fun _ => Y.m.φ) _ ψ (fun _ => rfl)) ⟨w₃, g₃⟩
  have BL : LBIso P.A.L (Y.oF.t.PP.L.pull ψ) :=
    LBIso.trans P.A.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB Y.oF.t.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) B₁' B₂) (LBIso.symm B₃)
  refine ⟨ψ, cart, BL, fun a => ?_, hψ₁.trans (Category.assoc _ _ _)⟩
  apply Y.m.cart.1.hom_ext
  · calc ((P.oA.act a).left ≫ ψ) ≫ Y.m.φ = (P.oA.act a).left ≫ k ≫ m.φ := by rw [Category.assoc, hψ₁]
      _ = k ≫ m.φ ≫ (Y.t.act.act a).left := by rw [← Category.assoc, actA, Category.assoc, m.act a]
      _ = (ψ ≫ (Y.oF.t.act.act a).left) ≫ Y.m.φ := by
        rw [Category.assoc ψ, Y.m.act a, ← Category.assoc ψ, hψ₁]; exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (P.oA.act a), Category.assoc, Over.w (Y.oF.t.act.act a), hψ₂]

end GlobalTheory.GenericFibreUnif
