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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel.BaseChangeComb

theorem comp_listProd' {B : Scheme.{0}} {G : Over B} [GrpObj G] {T T' : Over B} (f : T' ⟶ T) (L : List (T ⟶ G)) :
    f ≫ L.prod = (L.map (f ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one f
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem dualMap_comp_epsMul' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

theorem bc_comb_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Fin g → R) (σ : 𝓞 E →+* R) (u : Sp (DualNumber R) ⟶ t.G.left),
    (IsCombAtG t x e U u → IsCombAtG t (spMap φ ≫ x) (bcV t φ e) (fun b => φ (U b)) (spMap (dualMap φ) ≫ u)) ∧
    (IsEigG t σ u → IsEigG t (φ.comp σ) (spMap (dualMap φ) ≫ u)) := by
  intro E _ _ _ H X t R S _ _ φ x g e U σ u
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · obtain ⟨w, hw, hp⟩ := h
    have he : spMap (dualMap φ) ≫ (tEpsG x).hom = (tEpsG (spMap φ ≫ x)).hom := by
      show spMap (dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
        spMap (algebraMap S (DualNumber S)) ≫ spMap φ ≫ x
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
      congr 2
      apply RingHom.ext
      intro r
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    let bc : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) he
    refine ⟨fun i => bc ≫ w i, fun i => ?_, ?_⟩
    · show spMap (dualMap φ) ≫ (w i).left = spMap (epsMul (φ (U i))) ≫ spMap (dualMap φ) ≫ e i
      rw [hw i, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, dualMap_comp_epsMul']
    · have hl : (List.ofFn fun i => bc ≫ w i) = (List.ofFn w).map (bc ≫ ·) := by
        rw [List.map_ofFn]
        rfl
      rw [hl, ← comp_listProd', Over.comp_left, hp]
      rfl
  · show (spMap (dualMap φ) ≫ u) ≫ (t.act.act a).left = spMap (epsMul (φ (σ a))) ≫ spMap (dualMap φ) ≫ u
    rw [Category.assoc, h a, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, dualMap_comp_epsMul']

end GlobalTheory.FlatModel.BaseChangeComb

end
