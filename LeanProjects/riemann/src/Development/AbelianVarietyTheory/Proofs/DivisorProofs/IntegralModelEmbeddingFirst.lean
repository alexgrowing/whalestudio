import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.EigLift

theorem one_left_comp {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk _ hw
  have h2 := h.2 T 1 1 x₀ x₀ rfl rfl
  have h3 : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, _root_.mul_one]
    rfl
  have h4 : x₀ = 1 := by simpa using h3
  exact congrArg CommaMorphism.left h4

theorem comp_prod {B : Scheme.{0}} {G : Over B} [GrpObj G] {X Y : Over B} (z : X ⟶ Y) (L : List (Y ⟶ G)) :
    z ≫ L.prod = (L.map (z ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one z
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem sp_fst_alg (K : Type) [CommRing K] :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
  rw [← sp_comp]
  have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
    ext x; simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]
  simp [spMap]

theorem sp_fst_eps {K : Type} [CommRing K] (q : K) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (epsMul q) = spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
  rw [← sp_comp]
  have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (epsMul q) = (TrivSqZeroExt.fstHom K K K).toRingHom := by
    apply RingHom.ext; intro x
    show (epsMul q x).fst = x.fst
    simp [epsMul]
  rw [this]

theorem sp_eps_alg {K : Type} [CommRing K] (q : K) :
    spMap (epsMul q) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap K (DualNumber K)) := by
  rw [← sp_comp]
  have : (epsMul q).comp (algebraMap K (DualNumber K)) = algebraMap K (DualNumber K) := by
    apply RingHom.ext; intro x
    show epsMul q (algebraMap K (DualNumber K) x) = _
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]

end GlobalTheory.FlatModel.EigLift

namespace GlobalTheory.FlatModel.EigLift

theorem char_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l l' : Level H}
    {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F) (hI : OverIncl r hle)
    (σ : E →+* ℂ) {A : Type} [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A) (hβ : ξ ≫ Y.s = spMap β)
    {K : Type} [CommRing K] (φ : A →+* K) (io : c.F →+* K) (yy : Sp K ⟶ Xo'.XF c')
    (hyy : yy ≫ Y.j = spMap φ ≫ ξ) (hio : yy ≫ r ≫ pullback.snd _ _ = spMap io) (a : 𝓞 E) :
    φ (β (embV c' W σ a)) = io (embK c σ a) := by
  set κ : c'.F →+* K := (Spec.preimage (yy ≫ pullback.snd _ _)).hom with hκdef
  have hκ : spMap κ = yy ≫ pullback.snd _ _ := by
    simp only [spMap, hκdef, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have h1 : spMap (κ.comp (c'.V W).subtype) = spMap (φ.comp β) := by
    rw [sp_comp, sp_comp, hκ, Category.assoc, ← hjs, ← Category.assoc, hyy, Category.assoc, hβ]
  have h2 : spMap (κ.comp (IntermediateField.inclusion hle).toRingHom) = spMap io := by
    rw [sp_comp, hκ, Category.assoc, ← hI, hio]
  have k1 : κ.comp (c'.V W).subtype = φ.comp β := by
    have := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h1)
    simpa using this
  have k2 : κ.comp (IntermediateField.inclusion hle).toRingHom = io := by
    have := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h2)
    simpa using this
  calc φ (β (embV c' W σ a)) = κ ((embV c' W σ a : c'.V W) : c'.F) := (RingHom.congr_fun k1 _).symm
    _ = κ (IntermediateField.inclusion hle (embK c σ a)) := congrArg κ (Subtype.ext rfl)
    _ = io (embK c σ a) := RingHom.congr_fun k2 _

end GlobalTheory.FlatModel.EigLift

namespace GlobalTheory.FlatModel

open EigLift in

theorem lift_tan_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g m : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U : Fin m → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W σ))) (bcV Y.t φ e) (fun k b => φ (U k b))) → ∀ (K : Type) [CommRing K] (φ : A →+* K) (io : c.F →+* K) (y : letI := io.toAlgebra; FrPt Xo c K) (yy : Sp K ⟶ Xo'.XF c'), yy ≫ Y.j = spMap φ ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y = yy ≫ r) → ∀ (k : Fin m) (w : Sp (DualNumber K) ⟶ Y.oF.t.G.left), IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e) (fun b => φ (U k b)) (w ≫ Y.m.φ) → (letI := io.toAlgebra; IsTanAt y.x (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ)) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hI σ A _ ξ β hβ g m e U hB hEig K _ φ io y yy hyy hpt k w hw
  letI := io.toAlgebra
  haveI : IsOpenImmersion Y.j := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
  have hc := Y.m.cart.1
  have hcw : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := hc.w
  have hνw : ν.φ ≫ Xo.univ.t.G.hom = Y.oF.t.G.hom ≫ r ≫ pullback.fst _ _ := ν.cart.1.w
  have hx : y.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hpt, GlobalTheory.AllWt.ptF, pullback.lift_fst]
  have hio : yy ≫ r ≫ pullback.snd _ _ = spMap io := by
    rw [← Category.assoc, ← hpt, GlobalTheory.AllWt.ptF, pullback.lift_snd]
  have hχ : ∀ a, φ (β (embV c' W σ a)) = io (embK c σ a) := fun a =>
    char_eq Y r hle hI σ ξ β hβ φ io yy hyy hio a
  obtain ⟨u, hu, hwu⟩ := hw
  have hwb : w ≫ Y.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ yy := by
    rw [← cancel_mono Y.j, Category.assoc, ← hcw, ← Category.assoc, ← hwu, Over.w, Category.assoc]
    rfl
  have hT : ∀ i, IsTanAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e i) := by
    rw [hyy]
    exact (isTanBasis_bc hB φ).1
  have hz : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (tEpsG (yy ≫ Y.j)).hom = (Over.mk (yy ≫ Y.j)).hom := by
    show spMap _ ≫ spMap (algebraMap K (DualNumber K)) ≫ yy ≫ Y.j = yy ≫ Y.j
    rw [← Category.assoc, sp_fst_alg, Category.id_comp]
  let z : Over.mk (yy ≫ Y.j) ⟶ tEpsG (yy ≫ Y.j) := Over.homMk _ hz
  have hzu : ∀ i, z ≫ u i = 1 := fun i => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hu i, ← Category.assoc]
    show (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (epsMul _)) ≫ _ = _
    rw [sp_fst_eps]
    exact (hT i).2
  have hprod : z ≫ (List.ofFn u).prod = 1 := by
    rw [comp_prod, List.map_ofFn]
    have : ((z ≫ ·) ∘ u) = fun _ => 1 := funext hzu
    rw [this]
    simp
  have h0 : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w ≫ Y.m.φ = (1 : Over.mk (yy ≫ Y.j) ⟶ Y.t.G).left := by
    rw [← hwu, ← hprod]
    rfl
  have hw0 : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left := by
    apply hc.hom_ext
    · rw [Category.assoc, h0, one_left_comp Y.m.cart (Over.mk yy)]
      rfl
    · rw [Category.assoc, hwb, ← Category.assoc, sp_fst_alg, Category.id_comp, Over.w]
      rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hνw, ← Category.assoc, hwb, hx]
    simp only [Category.assoc]
  · rw [← Category.assoc, hw0, one_left_comp ν.cart (Over.mk yy), hx]
  · intro a
    have hE : IsEigG Y.t (φ.comp (β.comp (embV c' W σ))) (w ≫ Y.m.φ) :=
      hEig K φ k (w ≫ Y.m.φ) (by rw [← hyy]; exact ⟨u, hu, hwu⟩)
    have key : w ≫ (Y.oF.t.act.act a).left = spMap (epsMul (io (embK c σ a))) ≫ w := by
      apply hc.hom_ext
      · rw [Category.assoc, Category.assoc, Y.m.act a, ← Category.assoc, hE a]
        simp only [RingHom.comp_apply, hχ a, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w, hwb, ← Category.assoc, sp_eps_alg]
    show w ≫ ν.φ ≫ _ = spMap (epsMul (io (embK c σ a))) ≫ w ≫ ν.φ
    rw [← ν.act a, ← Category.assoc, key, Category.assoc]

end GlobalTheory.FlatModel
