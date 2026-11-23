import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftW

theorem one_left_eq {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] :
    (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem one_left_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have e := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at e
  have hxx : x₀ * x₀ = x₀ := by
    ext
    exact e
  have h1 : x₀ = 1 := mul_eq_right.mp hxx
  exact congrArg Over.Hom.left h1

theorem liftW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ (X : LieG P.Gt) (u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left), ITie P π X u0 →
    ∃ w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left,
      w ≫ Y.m.φ = spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ u0 ∧
      w ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ yy ∧
      spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left ∧
      LieTie P ψ X w := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ _ yb yy P π ψ hP X u0 hI
  obtain ⟨xG, hC, hπ⟩ := hI
  obtain ⟨-, -, -, hψ, hφ, -⟩ := hP
  have w0 : (spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ xG.1.left) ≫ P.G.hom =
      spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := by
    rw [Category.assoc, Over.w xG.1, spMap_spMap]
    refine (spMap_spMap _ _).trans (congrArg _ ?_)
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let u' : specO ℂ_[p] (DualNumber ℂ_[p]) ⟶ P.A.A :=
    Over.homMk (P.gen_pull.1.lift _ _ w0) (P.gen_pull.1.lift_snd _ _ w0)
  have hfst : u'.left ≫ P.gen = spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ xG.1.left :=
    P.gen_pull.1.lift_fst _ _ w0
  have hsnd : u'.left ≫ P.A.A.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) :=
    P.gen_pull.1.lift_snd _ _ w0
  refine ⟨u'.left ≫ ψ, ?_, ?_, ?_, ⟨xG, u', hC, rfl, hfst⟩⟩
  · rw [Category.assoc, hφ, ← Category.assoc, hfst, Category.assoc, hπ]
  · rw [Category.assoc, hψ.1.w, ← Category.assoc, hsnd]
  · have hA : spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ u'.left =
        (1 : Over.mk (𝟙 _) ⟶ P.A.A).left := by
      refine P.gen_pull.1.hom_ext ?_ ?_
      · rw [Category.assoc, hfst, one_left_comp_of_isGrpPullback P.gen_pull, one_left_eq, ← Category.assoc,
          spMap_spMap]
        have h2 : spMap (TrivSqZeroExt.fstHom 𝓞_ℂ_[p] 𝓞_ℂ_[p] 𝓞_ℂ_[p]).toRingHom ≫ xG.1.left =
            (specO 𝓞_ℂ_[p] 𝓞_ℂ_[p]).hom ≫ η[P.G].left := by
          have := congrArg Over.Hom.left xG.2
          rwa [Over.comp_left, Over.comp_left, Over.toUnit_left] at this
        have e1 : (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom.comp (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) =
            (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (TrivSqZeroExt.fstHom 𝓞_ℂ_[p] 𝓞_ℂ_[p] 𝓞_ℂ_[p]).toRingHom := by
          ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
        have e2 : spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (specO 𝓞_ℂ_[p] 𝓞_ℂ_[p]).hom =
            spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := by
          refine (spMap_spMap _ _).trans (congrArg _ ?_)
          ext s
          simp
        rw [e1, ← spMap_spMap, Category.assoc, h2, ← Category.assoc, e2]
        dsimp only [Over.mk_hom]
        first | (erw [Category.id_comp]) | (simp only [Category.id_comp]) | (exact congrArg (· ≫ _) (Category.id_comp _)) | (congr 1; exact Category.id_comp _) | rfl
      · rw [Category.assoc, hsnd, Over.w, spMap_spMap]
        dsimp only [Over.mk_hom]
        have e3 : (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom.comp (algebraMap ℂ_[p] (DualNumber ℂ_[p])) =
            RingHom.id _ := by
          ext s
          simp [TrivSqZeroExt.algebraMap_eq_inl]
        rw [e3]
        exact Spec.map_id _
    rw [← Category.assoc, hA, one_left_comp_of_isGrpPullback hψ, one_left_eq, one_left_eq]
    dsimp only [Over.mk_hom]
    first | (erw [Category.id_comp]) | (simp only [Category.id_comp]) | (exact congrArg (· ≫ _) (Category.id_comp _)) | (congr 1; exact Category.id_comp _) | rfl
end GlobalTheory.FlatModel.LiftW
