import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiabelianExtensionDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

theorem exists_torusExtension_pull {S : Scheme.{0}} {K : Type} [Field K] {f : Sp K ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] {G B : Over S} [GrpObj G] [GrpObj B] {G' : Over (Sp K)} [GrpObj G']
    (P : Out.PolAV (Sp K)) {F : G'.left ⟶ G.left} {p : P.A.left ⟶ B.left} (hF : IsGrpPullback G' G f F)
    (hB : IsGrpPullback P.A B f p) (q : G ⟶ B) [IsMonHom q] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (i : splitTorus S X ⟶ G) [IsMonHom i] (hk : IsPullback i (toUnit _) q (η[B])) :
    ∃ (T : TorusExtension G') (e : T.B ≅ P.A), IsMonHom (T.q ≫ e.hom) ∧ (T.q ≫ e.hom).left ≫ p = F ≫ q.left := by
  obtain ⟨i', hi, -⟩ := GlobalTheory.UU.existsUnique_torusCompat hF.1 i
  have w : (F ≫ q.left) ≫ B.hom = G'.hom ≫ f := by rw [Category.assoc, Over.w, hF.1.w]
  let q' : G' ⟶ P.A := Over.homMk (hB.1.lift _ _ w) (hB.1.lift_snd _ _ w)
  have hq : q'.left ≫ p = F ≫ q.left := hB.1.lift_fst _ _ w
  have sq : IsPullback F q'.left q.left p := by
    refine IsPullback.of_bot ?_ hq.symm hB.1
    rw [Over.w, Over.w]; exact hF.1
  have ker : IsPullback i' (toUnit _) q' (η[P.A]) := by
    have k₀ : IsPullback i.left (splitTorus S X).hom q.left (η[B]).left := by
      have := hk.map (Over.forget S)
      rw [← Rosenlicht.toUnit_left]
      exact this
    have k₁ := (SplitTorus.isPullback_bcMap f X).paste_horiz k₀
    have e₁ : SplitTorus.bcMap f X ≫ i.left = i'.left ≫ F := GlobalTheory.UU.torusCompat_iff.1 hi
    have e₂ := GlobalTheory.UU.eSec_comp_of_isGrpPullback hB
    have w' : i'.left ≫ q'.left = (splitTorus (Sp K) X).hom ≫ (η[P.A]).left := by
      refine hB.1.hom_ext ?_ ?_
      · rw [Category.assoc, hq, ← Category.assoc, ← e₁, k₁.w]
        exact (congrArg (_ ≫ ·) e₂.symm).trans (Category.assoc _ _ _).symm
      · rw [Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
        exact (Category.comp_id _).symm
    rw [e₁] at k₁
    have k₂ : IsPullback i'.left (splitTorus (Sp K) X).hom q'.left (η[P.A]).left :=
      IsPullback.of_right (k₁.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        (by simp) (by simpa using e₂.symm)) w' sq
    rw [← Rosenlicht.toUnit_left] at k₂ w'
    exact IsPullback.of_map (Over.forget (Sp K)) (Over.OverMorphism.ext w') k₂
  have hq' := GlobalTheory.UU.isMonHom_of_over_isMonHom hF hB q q' hq
  refine ⟨{ X := X
            B := P.A
            isAbelian := P.isAb
            q := q'
            i := i'
            q_hom := hq'
            i_hom := hi.isMonHom hF
            q_flat := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
            isKernel := ker }, Iso.refl _, ?_, ?_⟩
  · exact (Category.comp_id q').symm ▸ hq'
  · exact (congrArg (fun z => z.left ≫ p) (Category.comp_id q')).trans hq

theorem polPart_closedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Formalism.L2.Pj.CDVR) (t : SAB H (Sp W.V)) (P : PELUnif (IsLocalRing.maximalIdeal W.V) t), ∃ (G₀ : Over (Sp (IsLocalRing.ResidueField W.V))) (_ : GrpObj G₀) (i₀ : OAct (𝓞 E) G₀) (φ₀ : G₀.left ⟶ t.G.left), IsActPull i₀ t.act (spMap (IsLocalRing.residue W.V)) φ₀ ∧ PolPart (H.bar : 𝓞 E →+* 𝓞 E) i₀ := by
  intro E _ _ _ H W t P
  letI := H.starRing
  obtain ⟨t₀, ⟨m⟩⟩ := exists_sab (spMap (IsLocalRing.residue W.V)) t
  refine ⟨t₀.G, inferInstance, t₀.act, m.φ, ⟨m.cart, m.act⟩, ?_⟩
  let r : W.V ⧸ IsLocalRing.maximalIdeal W.V ^ (0 + 1) →+* IsLocalRing.ResidueField W.V :=
    Ideal.Quotient.lift _ (IsLocalRing.residue W.V) fun a ha => by
      rw [zero_add, pow_one] at ha
      exact (IsLocalRing.residue_eq_zero_iff a).2 ha
  have hr : spMap r ≫ Out.thick W.V (IsLocalRing.maximalIdeal W.V) 0 = spMap (IsLocalRing.residue W.V) :=
    (Spec.map_comp _ _).symm

  have hG := isGrpPullback_pullback t.G (Out.thick W.V (IsLocalRing.maximalIdeal W.V) 0)
  have w : m.φ ≫ t.G.hom = (t₀.G.hom ≫ spMap r) ≫ Out.thick W.V (IsLocalRing.maximalIdeal W.V) 0 := by
    rw [Category.assoc, hr]; exact m.cart.1.w
  have hF := IsGrpPullback.cancel hG (m.cart.congr hr.symm (hG.1.lift_fst _ _ w).symm) (hG.1.lift_snd _ _ w)

  obtain ⟨P', g, hg, -, mul, s, hs⟩ := GlobalTheory.allSixLaws.1.polBaseChange _ _ (spMap (IsLocalRing.residue W.V)) P.D.toPre.P
  have pg : IsGrpPullback P'.A P.D.toPre.P.A (spMap (IsLocalRing.residue W.V)) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
    exact (congrArg (fun a => a.left) (mul T x y)).symm⟩
  obtain ⟨o, ho⟩ := polOActPull _ _ _ _ P' g pg ⟨s, hs⟩ (𝓞 E) P.oD.onB
  have hA := isGrpPullback_pullback P.D.toPre.P.A (Out.thick W.V (IsLocalRing.maximalIdeal W.V) 0)
  have w' : g ≫ P.D.toPre.P.A.hom = (P'.A.hom ≫ spMap r) ≫ Out.thick W.V (IsLocalRing.maximalIdeal W.V) 0 := by
    rw [Category.assoc, hr]; exact hg.w
  have hB := IsGrpPullback.cancel hA (pg.congr hr.symm (hA.1.lift_fst _ _ w').symm) (hA.1.lift_snd _ _ w')
  have := (P.U.gt 0).q_hom
  have := (P.U.gt 0).i_hom
  have := (P.U.gt 0).q_flat
  have := (P.U.gt 0).q_surj
  have := (P.U.gt 0).q_affine
  obtain ⟨T, e, he, hq⟩ := exists_torusExtension_pull P' hF hB (P.U.gt 0).q (P.U.gt 0).i (P.U.gt 0).isKernel
  refine ⟨T, P', e, ofRingAct o.toRingAct, he, fun a => ?_, fun a => o.rosati a⟩
  refine Over.OverMorphism.ext (pg.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have hq₁ : (T.q ≫ e.hom).left ≫ g = hG.1.lift _ _ w ≫ (P.U.gt 0).q.left ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hq, Category.assoc, hA.1.lift_fst]
  have hl : (t₀.act.act a).left ≫ hG.1.lift _ _ w = hG.1.lift _ _ w ≫
      ((Over.pullback (Out.thick W.V (IsLocalRing.maximalIdeal W.V) 0)).map (t.act.act a)).left := by
    refine hG.1.hom_ext ?_ ?_
    · rw [Category.assoc, hG.1.lift_fst, m.act, Category.assoc]
      erw [pullback.lift_fst]
      rw [← Category.assoc, hG.1.lift_fst]
    · rw [Category.assoc, hG.1.lift_snd, Category.assoc, Over.w, hG.1.lift_snd, Over.w_assoc]
  have hlin := congrArg (fun z => z.left) (P.lin.q_lin 0 a)
  simp only [Over.comp_left] at hlin
  have hb : ((Over.pullback (Out.thick W.V (IsLocalRing.maximalIdeal W.V) 0)).map (P.oD.onB.act a)).left ≫
      pullback.fst _ _ = pullback.fst _ _ ≫ (P.oD.onB.act a).left := pullback.lift_fst _ _ _
  calc (t₀.act.act a ≫ T.q ≫ e.hom).left ≫ g
      = (t₀.act.act a).left ≫ (T.q ≫ e.hom).left ≫ g := Category.assoc _ _ _
    _ = ((T.q ≫ e.hom).left ≫ g) ≫ (P.oD.onB.act a).left := by
      rw [hq₁, ← Category.assoc, hl, Category.assoc, Category.assoc, Category.assoc, ← hb]
      exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hlin).trans (Category.assoc _ _ _)))
    _ = ((T.q ≫ e.hom) ≫ o.act a).left ≫ g := by
      rw [Category.assoc, ← ho]; exact (Category.assoc _ _ _).symm

end GlobalTheory.CurveRootGeometry

end
