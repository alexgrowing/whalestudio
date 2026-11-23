import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPoint

theorem eq_spMap_of_injective {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (i : A →+* B)
    (hi : Function.Injective i) (x : Sp A ⟶ Sp K) (ρ : K →+* A) (h : spMap i ≫ x = spMap (i.comp ρ)) :
    x = spMap ρ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  have h' : Spec.map (φ ≫ CommRingCat.ofHom i) = Spec.map (CommRingCat.ofHom (i.comp ρ)) := by
    rw [Spec.map_comp]; exact h
  have h2 := Spec.map_injective h'
  congr 1
  ext k
  exact hi (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) k)

theorem sumsAt_of_halfRing {K F : Type} [CommRing K] [CommRing F] {X Y : Scheme.{0}} (s : X ⟶ Sp K) (κ : K →+* F)
    (bF : F →+* ℂ) (j : pullback s (spMap κ) ⟶ Y) (χ : Sp ℂ⟦X⟧ ⟶ Y) (y : Sp ℂ⸨X⸩ ⟶ pullback s (spMap κ))
    (hj : y ≫ j = spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) ≫ χ)
    (hs : y ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ X)
    (hT : spMap (Conv.halfRing T).val.toRingHom ≫ yT = y ≫ pullback.fst _ _)
    (U : Y.Opens) (f : Γ(Y, U)) (hU : ⊤ ≤ χ ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ∀ z : Sp ℂ ⟶ pullback s (spMap κ),
      z ≫ pullback.fst _ _ = spMap (Conv.ev T w hw).toRingHom ≫ yT → z ≫ pullback.snd _ _ = spMap bF →
      ⊤ ≤ (z ≫ j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (z ≫ j) U f) := by
  have hval : (Conv.halfRing T).val.toRingHom.comp ((algebraMap ℂ (Conv.halfRing T)).comp bF) =
      (algebraMap ℂ ℂ⸨X⸩).comp bF := RingHom.ext fun _ => rfl
  have hover : yT ≫ s = spMap ((algebraMap ℂ (Conv.halfRing T)).comp bF) ≫ spMap κ := by
    rw [← spMap_comp]
    refine eq_spMap_of_injective (Conv.halfRing T).val.toRingHom Subtype.val_injective _ _ ?_
    rw [← Category.assoc, hT, Category.assoc, pullback.condition, ← Category.assoc, hs, ← spMap_comp,
      ← RingHom.comp_assoc, hval]
  let yF : Sp (Conv.halfRing T) ⟶ pullback s (spMap κ) := pullback.lift yT _ hover
  have hgen : spMap (Conv.halfRing T).val.toRingHom ≫ yF = y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hT]
    · rw [Category.assoc, pullback.lift_snd, hs, ← spMap_comp, hval]
  obtain ⟨T', hle, hw'⟩ := Conv.exists_sumsAt_halfCurve (yT := yF ≫ j) (χ := χ) rfl (RingHom.id _) (by
    rw [RingHom.id_comp, RingHom.id_comp, ← hj, ← hgen, Category.assoc, ← Category.assoc (spMap _) (spMap _),
      ← spMap_comp]
    rfl) hU
  refine ⟨T', hle, fun w hw hw2 z hz1 hz2 => ?_⟩
  have hz : z = spMap (Conv.ev T w hw).toRingHom ≫ yF := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hz1]
    · rw [Category.assoc, pullback.lift_snd, hz2, ← spMap_comp]
      congr 2
      ext x
      exact ((Conv.ev T w hw).commutes (bF x)).symm
  have hzj : z ≫ j = Conv.halfCurve (yF ≫ j) w := by
    rw [hz, Conv.halfCurve_eq _ hw, Category.assoc]
    rfl
  rw [hzj]
  exact ⟨(hw' w hw2).1, (hw' w hw2).2 f⟩

theorem point_sumsAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), ∀ (U : Y.X.Opens) (f : Γ(Y.X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u K.i (K.Pw w) → yF ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (yF ≫ Y.j) U f) := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K U f hU
  obtain ⟨T', hle, h⟩ := sumsAt_of_halfRing Xo.s _ bF Y.j χ C.yF C.yF_j C.yF_over Ψ.yT Ψ.yT_gen U f hU
  refine ⟨max T' K.T, fun w hw z hz1 hz2 => ?_⟩
  have h1 : T' < w.im := (le_max_left _ _).trans_lt hw
  have h2 : Ψ.T < w.im := hle.trans_lt h1
  exact h w h2 h1 z (hz1.trans ((K.u_eq w ((le_max_right _ _).trans_lt hw)).trans (Ψ.yw_eq w h2))) hz2

end GlobalTheory.ArcPoint
