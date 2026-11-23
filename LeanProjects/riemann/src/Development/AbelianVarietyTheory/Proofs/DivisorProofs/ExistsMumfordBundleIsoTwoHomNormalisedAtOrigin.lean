import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarised

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

theorem exists_lamVal_origin_two : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b], LBIso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left) → ∃ w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left), w.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1 := by
  intro S B₀ B _ _ _ _ M₀ M hM₀ hM a b _ _ H
  obtain ⟨w₀, hw₀⟩ := H
  let F : (G2 B₀).left ⟶ (G2 B).left := (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left
  let e : (𝟙_ (Over S)).left ⟶ (G2 B₀).left := (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1).left
  let q : (𝟙_ (Over S)).left ⟶ B.left := (1 : 𝟙_ (Over S) ⟶ B).left
  let q' : (𝟙_ (Over S)).left ⟶ B₀.left := (1 : 𝟙_ (Over S) ⟶ B₀).left
  have eF : e ≫ F = (lift (1 : 𝟙_ (Over S) ⟶ B) 1).left := by
    show (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1 ≫ lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b)).left = _
    rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, MonObj.one_comp]
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ F) ≫ (psum B (x2 B) I.down).left = q := fun I => by
    rw [eF]
    exact congrArg (fun z => z.left) (GlobalTheory.PolDeg.NormIso.lift_one_psum B (T := 𝟙_ (Over S)) I.down)
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B₀ (x2 B₀) I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (GlobalTheory.PolDeg.NormIso.lift_one_psum B₀ (T := 𝟙_ (Over S)) I.down)
  obtain ⟨w, hw, hv⟩ := GlobalTheory.PolDeg.NormIso.exists_normalised M M₀ hM hM₀ (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B₀ (x2 B₀) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) F e (toUnit (G2 B₀)).left
    (congrArg (fun z => z.left) (toUnit_unique (lift (1 : 𝟙_ (Over S) ⟶ B₀) 1 ≫ toUnit (G2 B₀)) (𝟙 _))) q q' hq hq'
    w₀ hw₀
  refine ⟨w, hw, fun T z J J' hJ hJ' => ?_⟩
  have hp : (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left = (toUnit T).left ≫ e := by
    show _ = (toUnit T ≫ lift (1 : 𝟙_ (Over S) ⟶ B₀) 1).left
    rw [comp_lift, MonObj.comp_one]
  have key : ∀ (p : T.left ⟶ (G2 B₀).left) (j : (abelian₂ B M).ι) (k : (abelian₂ B₀ M₀).ι),
      (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ F ≫ (psum B (x2 B) I.down).left)) = j →
      (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B₀ (x2 B₀) I.down).left)) = k →
      GlobalTheory.PolDeg.lamVal w p z J J' = gw (L := abelian₂ B M) (L' := abelian₂ B₀ M₀) w p z j k := by
    rintro p _ _ rfl rfl
    rfl
  rw [hp]
  refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
    (funext fun I => ?_)).trans (hv T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
  · rw [← hq I, Category.assoc, Category.assoc]
  · rw [← hq' I, Category.assoc]

end GlobalTheory.Mum.Two
