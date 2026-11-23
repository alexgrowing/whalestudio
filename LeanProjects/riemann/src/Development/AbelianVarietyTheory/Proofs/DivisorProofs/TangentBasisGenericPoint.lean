import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
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

noncomputable section

namespace GlobalTheory.FlatModel.LiftGen

theorem one_left_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] (P : Over S) :
    (1 : P ⟶ G).left = P.hom ≫ eSec G := by
  rw [CategoryTheory.Hom.one_def]
  simp [eSec]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem epsMul_comp_alg {R : Type} [CommRing R] (c : R) :
    (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [epsMul]

theorem fst_comp_epsMul {R : Type} [CommRing R] (c : R) :
    (TrivSqZeroExt.fstHom R R R).toRingHom.comp (epsMul c) = (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun z => ?_
  simp [epsMul]

theorem fst_comp_dualMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun z => ?_
  simp [dualMap]

theorem exists_lift_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ cf : Fin g → L, ∃ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left,
      IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) cf (w ≫ Y.m.φ) ∧ IsTanAtG Y.oF.t yL w := by
  intro E _ _ _ H Dw l' Xo' c' W Y A _ ξ g e he L _ io yL hyL cf
  have hv : ∀ i, IsTanAtG Y.t (yL ≫ Y.j) (bcV Y.t io e i) := by
    intro i
    obtain ⟨h1, h2⟩ := he.1 i
    constructor
    · show (spMap (dualMap io) ≫ e i) ≫ Y.t.G.hom = _
      rw [Category.assoc, h1, ← Category.assoc, PullbackSections.spMap_comp_spMap, dualMap_comp_alg,
        ← PullbackSections.spMap_comp_spMap, Category.assoc, hyL]
    · show spMap _ ≫ spMap (dualMap io) ≫ e i = _
      rw [← Category.assoc, PullbackSections.spMap_comp_spMap, fst_comp_dualMap, ← PullbackSections.spMap_comp_spMap, Category.assoc, h2,
        one_left_eq, one_left_eq]
      simp only [Over.mk_hom]
      rw [hyL, Category.assoc]
  let u : Fin g → (tEpsG (yL ≫ Y.j) ⟶ Y.t.G) := fun i =>
    Over.homMk (spMap (epsMul (cf i)) ≫ bcV Y.t io e i) (by
      show (spMap (epsMul (cf i)) ≫ bcV Y.t io e i) ≫ Y.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL ≫ Y.j
      rw [Category.assoc, (hv i).1, ← Category.assoc, PullbackSections.spMap_comp_spMap, epsMul_comp_alg])
  let wG : Sp (DualNumber L) ⟶ Y.t.G.left := ((List.ofFn u).prod).left
  have hcomb : IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) cf wG := ⟨u, fun i => rfl, rfl⟩
  have hwG : wG ≫ Y.t.G.hom = (spMap (algebraMap L (DualNumber L)) ≫ yL) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    have := Over.w ((List.ofFn u).prod)
    simpa [wG, Model.j] using this
  let w : Sp (DualNumber L) ⟶ Y.oF.t.G.left := Y.m.cart.1.lift wG _ hwG
  have hwφ : w ≫ Y.m.φ = wG := Y.m.cart.1.lift_fst _ _ _
  have hwh : w ≫ Y.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL := Y.m.cart.1.lift_snd _ _ _
  refine ⟨w, hwφ ▸ hcomb, hwh, ?_⟩

  let δ : Over.mk (yL ≫ Y.j) ⟶ tEpsG (yL ≫ Y.j) := Over.homMk (spMap (TrivSqZeroExt.fstHom L L L).toRingHom) (by
    show spMap _ ≫ spMap (algebraMap L (DualNumber L)) ≫ yL ≫ Y.j = yL ≫ Y.j
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (algebraMap L (DualNumber L)) = RingHom.id L := by
      refine RingHom.ext fun z => ?_
      simp
    rw [this, spMap_id']
    exact Category.id_comp _)
  have hδu : ∀ i, δ ≫ u i = 1 := by
    intro i
    refine Over.OverMorphism.ext ?_
    show spMap _ ≫ spMap (epsMul (cf i)) ≫ bcV Y.t io e i = _
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap, fst_comp_epsMul]
    exact (hv i).2
  have hδ : δ ≫ (List.ofFn u).prod = 1 := by
    have h := map_list_prod (Formalism.L2.Pj.preHom (G := Y.t.G) δ) (List.ofFn u)
    rw [List.map_ofFn] at h
    refine (congrArg _ rfl).trans (h.trans ?_)
    have hf : (⇑(Formalism.L2.Pj.preHom (G := Y.t.G) δ) ∘ u) = fun _ => 1 := by
      funext i
      exact hδu i
    rw [hf, List.ofFn_const, List.prod_replicate, one_pow]
  refine Y.m.cart.1.hom_ext ?_ ?_
  · show (spMap _ ≫ w) ≫ Y.m.cm.F = _
    rw [Category.assoc, hwφ]
    have h1 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ wG = (δ ≫ (List.ofFn u).prod).left := rfl
    rw [h1, hδ, one_left_eq, one_left_eq, Category.assoc, Y.m.cm.e_comm, Y.m.base]
    rfl
  · rw [Category.assoc, hwh, Over.w (1 : Over.mk yL ⟶ Y.oF.t.G), ← Category.assoc, PullbackSections.spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (algebraMap L (DualNumber L)) = RingHom.id L := by
      refine RingHom.ext fun z => ?_
      simp
    rw [this, spMap_id']
    exact Category.id_comp _

end GlobalTheory.FlatModel.LiftGen
