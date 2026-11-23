import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolPartPull

def torusExtPull {k Ω : Type} [Field k] [Field Ω] (f : Sp Ω ⟶ Sp k) (G : Over (Sp k)) [GrpObj G]
    (T : TorusExtension G) : TorusExtension ((Over.pullback f).obj G) :=
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  haveI : IsMonHom (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose.hom :=
    (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose_spec.1
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := (Over.pullback f).obj T.B
    grpB := inferInstance
    isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
    q := (Over.pullback f).map T.q
    q_hom := inferInstance
    q_flat := MorphismProperty.of_isPullback (P := @Flat) (GlobalTheory.SS.isPullback_overPullback_map_left f T.q) T.q_flat
    q_surjective :=
      MorphismProperty.of_isPullback (P := @Surjective) (GlobalTheory.SS.isPullback_overPullback_map_left f T.q) T.q_surjective
    q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact)
      (GlobalTheory.SS.isPullback_overPullback_map_left f T.q) T.q_quasiCompact
    i := (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose.hom ≫ (Over.pullback f).map T.i
    i_hom := inferInstance
    isKernel := by
      refine IsPullback.of_iso (T.isKernel.map (Over.pullback f))
        (GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X).choose.symm (Iso.refl _)
        (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · exact toUnit_unique _ _
      · simp
      · simp }

def oActIso {O : Type} [CommRing O] {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom]
    (a : OAct O A) : OAct O B where
  act x := e.inv ≫ a.act x ≫ e.hom
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one]; simp
  mul x y := by rw [a.mul]; simp
  add x y := by rw [a.add, MonObj.mul_comp, MonObj.comp_mul]

theorem pbMap_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

theorem rosatiAdj_pull {K K' : Type} [Field K] [Field K'] (f : K →+* K') {P : Out.PolAV (Sp K)}
    {P' : Out.PolAV (Sp K')} {ψ : P'.A.left ⟶ P.A.left} (hψ : IsGrpPullback P'.A P.A (spMap f) ψ)
    (hL : LBIso (P.L.pull ψ) P'.L) {a b : P.A ⟶ P.A} {a' b' : P'.A ⟶ P'.A} (ha : a'.left ≫ ψ = ψ ≫ a.left)
    (hb : b'.left ≫ ψ = ψ ≫ b.left) (hr : Out.RosatiAdj P.A P.L a b) : Out.RosatiAdj P'.A P'.L a' b' := by
  haveI := P.isAb.comm
  haveI := P'.isAb.comm
  let U₂ := lift (pushPt hψ.1.w (fst P'.A P'.A)) (pushPt hψ.1.w (snd P'.A P'.A))
  have u₁ : U₂.left ≫ (fst P.A P.A).left = (fst P'.A P'.A).left ≫ ψ := TripleDescent.lift_left_fst _ _
  have u₂ : U₂.left ≫ (snd P.A P.A).left = (snd P'.A P'.A).left ≫ ψ := TripleDescent.lift_left_snd _ _
  have v₁ : (fst P'.A P'.A ≫ a').left ≫ ψ = U₂.left ≫ (fst P.A P.A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, ← u₁, Category.assoc]
  have v₂ : (snd P'.A P'.A ≫ b').left ≫ ψ = U₂.left ≫ (snd P.A P.A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, ← u₂, Category.assoc]
  have hφ : ∀ k, Out.rosatiφ P'.A a' b' k ≫ ψ = U₂.left ≫ Out.rosatiφ P.A a b k := fun k => by
    fin_cases k
    exacts [ArcPull.mul_push hψ U₂.left v₁ u₂.symm, v₁, u₂.symm, ArcPull.mul_push hψ U₂.left u₁.symm v₂, u₁.symm, v₂]
  obtain ⟨t, ht⟩ := RosatiDescent.exists_gen_of_rosatiAdj hr
  obtain ⟨w, hw⟩ := LBIso.symm hL
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : LB.Gen (LB.LinComb P.L (fun k => Out.rosatiφ P'.A a' b' k ≫ ψ) Out.rosatiε), t₁.IsGen := by
    rw [show (fun k => Out.rosatiφ P'.A a' b' k ≫ ψ) = fun k => U₂.left ≫ Out.rosatiφ P.A a b k from funext hφ]
    exact ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
  obtain ⟨a₀, ha₀⟩ := exists_down ((isGen_iff w).1 hw) P.isLB P'.isLB t₁ ht₁
  exact fun s => ⟨⊤, trivial, _, DVR.pullGen_isGen _ _ _ a₀ ha₀ _⟩

end GlobalTheory.PolPartPull

namespace GlobalTheory.PolPartPull

theorem polPart_of_isActPull : ∀ (O : Type) [CommRing O] (c : O →+* O) (K K' : Type) [Field K] [Field K'] (f : K →+* K') (G : Over (Sp K)) [GrpObj G] (i : OAct O G) (G' : Over (Sp K')) [GrpObj G'] (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i (spMap f) φ → PolPart c i → PolPart c i' := by
  intro O _ c K K' _ _ f G _ i G' _ i' φ h hP
  obtain ⟨T, P, e, j, hm, heq, hr⟩ := hP
  haveI := P.isAb.comm
  haveI := hm
  obtain ⟨P', ψ, -, hψ, hL⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.allSixLaws.1.polBaseChange f P
  obtain ⟨ge, hgm, hgg⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap f)) h.1
  obtain ⟨β, hβm, hβ⟩ := grpPullback_iso (isGrpPullback_pullback P.A (spMap f)) hψ
  haveI := hgm
  haveI := hβm
  have hgi : ∀ a, ge.hom ≫ i'.act a = (Over.pullback (spMap f)).map (i.act a) ≫ ge.hom := fun a => by
    apply Over.OverMorphism.ext
    apply h.1.1.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, h.2 a, hgg, ← Category.assoc, hgg,
        pbMap_fst]
    · rw [Over.w, Over.w]
  have h2 : ∀ a, i'.act a ≫ ge.inv = ge.inv ≫ (Over.pullback (spMap f)).map (i.act a) := fun a => by
    rw [Iso.comp_inv_eq, Category.assoc, ← hgi, Iso.inv_hom_id_assoc]
  let j' : OAct O P'.A := oActIso β (OAct.pullback (spMap f) P.A j)
  have hj : ∀ a, (j'.act a).left ≫ ψ = ψ ≫ (j.act a).left := fun a => by
    show (β.inv ≫ (Over.pullback (spMap f)).map (j.act a) ≫ β.hom).left ≫ ψ = _
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hβ, pbMap_fst, ← hβ, ← Category.assoc,
      ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  let T' := torusExtOfIso ge (torusExtPull (spMap f) G T)
  have e1 : T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom =
      ge.inv ≫ (Over.pullback (spMap f)).map (T.q ≫ e.hom) ≫ β.hom := by
    show (ge.inv ≫ (Over.pullback (spMap f)).map T.q) ≫ (Over.pullback (spMap f)).map e.hom ≫ β.hom = _
    rw [Functor.map_comp, Category.assoc, Category.assoc]
  refine ⟨T', P', (Over.pullback (spMap f)).mapIso e ≪≫ β, j', ?_, fun a => ?_, fun a =>
    rosatiAdj_pull f hψ hL (hj a) (hj (c a)) (hr a)⟩
  · show IsMonHom (T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom)
    rw [e1]
    infer_instance
  · show i'.act a ≫ T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom =
      (T'.q ≫ ((Over.pullback (spMap f)).mapIso e ≪≫ β).hom) ≫ j'.act a
    rw [e1]
    show i'.act a ≫ ge.inv ≫ (Over.pullback (spMap f)).map (T.q ≫ e.hom) ≫ β.hom =
      (ge.inv ≫ (Over.pullback (spMap f)).map (T.q ≫ e.hom) ≫ β.hom) ≫ β.inv ≫
        (Over.pullback (spMap f)).map (j.act a) ≫ β.hom
    rw [← Category.assoc (i'.act a), h2]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, heq a]

end GlobalTheory.PolPartPull
