import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

private theorem rosatiAdj_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} {L : LB A.left}
    (gp : IsGrpPullback A' A f Φ) {a b : A ⟶ A} {a' b' : A' ⟶ A'}
    (ha : a'.left ≫ Φ = Φ ≫ a.left) (hb : b'.left ≫ Φ = Φ ≫ b.left) (hr : Out.RosatiAdj A L a b) :
    Out.RosatiAdj A' (L.pull Φ) a' b' := by
  let Φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left :=
    (lift (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt gp.1.w (fst A' A')) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt gp.1.w (snd A' A'))).left
  have f₁ : (fst A' A').left ≫ Φ = Φ₂ ≫ (fst A A).left :=
    (congrArg (fun q => q.left) (lift_fst (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt gp.1.w (fst A' A'))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt gp.1.w (snd A' A')))).symm
  have f₂ : (snd A' A').left ≫ Φ = Φ₂ ≫ (snd A A).left :=
    (congrArg (fun q => q.left) (lift_snd (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt gp.1.w (fst A' A'))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushPt gp.1.w (snd A' A')))).symm
  have f₃ : (fst A' A' ≫ a').left ≫ Φ = Φ₂ ≫ (fst A A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, f₁, Category.assoc]
  have f₄ : (snd A' A' ≫ b').left ≫ Φ = Φ₂ ≫ (snd A A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, f₂, Category.assoc]
  have hψ : ∀ i, Out.rosatiφ A' a' b' i ≫ Φ = Φ₂ ≫ Out.rosatiφ A a b i := fun i => by
    fin_cases i
    exacts [ArcPull.mul_push gp Φ₂ f₃ f₂, f₃, f₂, ArcPull.mul_push gp Φ₂ f₁ f₄, f₁, f₄]
  have w₂ : Φ₂ ≫ (A ⊗ A).hom = (A' ⊗ A').hom ≫ f := by
    rw [← Over.w (fst A A), ← Category.assoc, ← f₁, Category.assoc, gp.1.w, ← Category.assoc, Over.w]
  intro s
  obtain ⟨U, hU, t, ht⟩ := hr (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le' : (A' ⊗ A').hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ Φ₂ ⁻¹ᵁ ((A ⊗ A).hom ⁻¹ᵁ U) := fun y hy =>
    (congrArg (fun q => q y ∈ U) w₂).mpr hy
  have hι : Φ₂.resLE _ _ le' ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = ((A' ⊗ A').hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ Φ₂ :=
    Scheme.Hom.resLE_comp_ι Φ₂ le'
  refine gen_chartPull (chartPullLinComb L Φ _ _ _ (Φ₂.resLE _ _ le') fun k => ?_) t ht
  rw [Category.assoc, hψ, ← Category.assoc, ← hι, Category.assoc]

theorem UpperTheory.rosati_action_pullback :
    ∀ (O : Type) [CommRing O] (c : O →+* O) (S S' : Scheme.{0}) (f : S' ⟶ S) (P : Out.PolAV S) (j : OAct O P.A),
        IsRosati c P j → ∃ (P' : Out.PolAV S') (j' : OAct O P'.A) (ψ : P'.A.left ⟶ P.A.left),
          IsActPull j' j f ψ ∧ IsRosati c P' j' := by
  intro O _ c S S' f P j hj
  have hc := P.isAb.comm
  have hc' := (StrictPull.polPull P f).isAb.comm
  let j' : OAct O (StrictPull.polPull P f).A := OAct.pullback f P.A j
  have h : IsActPull j' j f (pullback.fst P.A.hom f) := exists_isActPull f j
  refine ⟨StrictPull.polPull P f, j', pullback.fst P.A.hom f, h, fun a => ?_⟩
  exact rosatiAdj_pull (A' := (StrictPull.polPull P f).A) h.1 (h.2 a) (h.2 (c a)) (hj a)
