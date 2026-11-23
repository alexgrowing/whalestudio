import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointEndomorphismsCubeLBOfDenseFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.MatchBundle

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R]

theorem pull_one (D : DegPre R) (T : Over (Sp R)) : CechPic.pull (1 : T ⟶ D.P.A).left (cls D.P.L D.P.isLB) = 0 := by
  have h : CechPic.pull (eSec D.P.A) (cls D.P.L D.P.isLB) = 0 :=
    (cls_pull D.P.isLB _ (pull_isLB D.P.isLB _)).symm.trans
      ((cls_eq_zero_iff (pull_isLB D.P.isLB _)).2 ⟨D.rig, D.rig_gen⟩)
  have e : (1 : T ⟶ D.P.A).left = (toUnit T).left ≫ eSec D.P.A := rfl
  rw [e, pull_comp, h, map_zero]

theorem cls_eq_lam (D : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O)
    (h : TraceFormTwistIso D oa w0) : cls D.P.L D.P.isLB = lam (cls D.P.L D.P.isLB) (𝟙 _) (oa.onB.act w0) := by
  obtain ⟨u, hu, -⟩ := h
  have h₀ := (cls_eq_zero_iff (LB.isLB_linComb D.P.isLB _ _)).2 ⟨u, hu⟩
  rw [cls_linComb D.P.isLB, Fin.sum_univ_four] at h₀
  have h₁ : (1 : ℤ) • CechPic.pull (𝟙 D.P.A * oa.onB.act w0).left (cls D.P.L D.P.isLB) +
      (-2 : ℤ) • CechPic.pull (𝟙 D.P.A.left) (cls D.P.L D.P.isLB) +
      (-1 : ℤ) • CechPic.pull (oa.onB.act w0).left (cls D.P.L D.P.isLB) +
      (2 : ℤ) • CechPic.pull (1 : D.P.A ⟶ D.P.A).left (cls D.P.L D.P.isLB) = 0 := h₀
  rw [lam, Over.id_left]
  rw [pull_one] at h₁ ⊢
  rw [pull_id] at h₁ ⊢
  linear_combination (norm := abel) -h₁

theorem cls_eq_lam_pull {V : Type} [CommRing V] [IsDomain V] {f : R →+* V} {D : DegPre R} {D' : DegPre V}
    (hD : IsPullDeg f D D') (a : D.P.A ⟶ D.P.A) (a' : D'.P.A ⟶ D'.P.A)
    (ha : a' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf f)).map a)
    (h : cls D.P.L D.P.isLB = lam (cls D.P.L D.P.isLB) (𝟙 _) a) :
    cls D'.P.L D'.P.isLB = lam (cls D'.P.L D'.P.isLB) (𝟙 _) a' := by
  have gp := pull_grp hD
  have e : cls D'.P.L D'.P.isLB =
      CechPic.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf f)) (cls D.P.L D.P.isLB) :=
    ((cls_eq_iff D'.P.isLB (pull_isLB D.P.isLB _)).2 ⟨hD.w, hD.w_gen⟩).trans (cls_pull D.P.isLB _ _)
  have p1 : (pushHom gp _ (𝟙 D'.P.A)).left = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf f) := Category.id_comp _
  have q : pushHom gp _ a' = pushHom gp _ (𝟙 D'.P.A) ≫ a := Over.OverMorphism.ext (by
    rw [Over.comp_left, p1]
    have a₂ : ((Over.pullback (specOf f)).map a).left ≫ pullback.fst D.P.A.hom (specOf f) =
        pullback.fst _ _ ≫ a.left := pullback.lift_fst _ _ _
    show a'.left ≫ hD.e.hom.left ≫ _ = (hD.e.hom.left ≫ _) ≫ _
    rw [← Category.assoc, ← Over.comp_left, ha, Over.comp_left, Category.assoc, a₂, Category.assoc])
  have k := congrArg (CechPic.pull (pushHom gp _ (𝟙 D'.P.A)).left) h
  rw [pull_lam, Category.comp_id, ← q, p1] at k
  rw [e, lam_pull_of_isGrpPullback gp]
  exact k

theorem lbIso_of_match : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → LBIso D₁.toPre.P.L (D₂.toPre.P.L.pull b.left) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ _ C _ V _ _ _ _ _ f₁ f₂ _ _ _ _ D₁ D₂ hD₁ hD₂ _ _ b φ' _ _ hM hact
  letI := H.starRing
  obtain ⟨a₁, a₂, h₁, h₂, hb⟩ := hact H.w0
  have k := cls_eq_lam C.P.D.toPre C.P.oD H.w0 C.P.w0
  have k₁ := cls_eq_lam_pull hD₁ _ a₁ h₁ k
  have k₂ := cls_eq_lam_pull hD₂ _ a₂ h₂ k
  have hL₁ := D₁.toPre.P.isLB
  have hL₂ := D₂.toPre.P.isLB
  have i₁ : (abelian₂ D₁.toPre.P.A D₁.toPre.P.L).IsLB := LB.isLB_linComb hL₁ _ _
  have i₂ : (abelian₂ D₂.toPre.P.A D₂.toPre.P.L).IsLB := LB.isLB_linComb hL₂ _ _
  have m := ((cls_eq_iff i₁ (pull_isLB i₂ _)).2 hM.2.2.1).trans (cls_pull i₂ _ _)
  have c₁ : cls _ i₁ = lam (cls _ hL₁) (fst _ _) (snd _ _) := cls_cube_two hL₁ _ _ _
  have c₂ : cls _ i₂ = lam (cls _ hL₂) (fst _ _) (snd _ _) := cls_cube_two hL₂ _ _ _
  rw [c₁, c₂] at m
  have m' := congrArg (CechPic.pull (lift (𝟙 D₁.toPre.P.A) a₁).left) m
  simp only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.id_comp] at m'
  refine (cls_eq_iff hL₁ (pull_isLB hL₂ _)).1 ?_
  rw [cls_pull hL₂, k₁, m', hb]
  conv_rhs => rw [k₂, pull_lam, Category.comp_id]

end GlobalTheory.UCanon.MatchBundle
