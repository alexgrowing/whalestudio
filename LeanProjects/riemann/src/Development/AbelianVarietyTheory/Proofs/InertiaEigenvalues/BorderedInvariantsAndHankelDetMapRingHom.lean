import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsPowMulVecFirstBasisVector

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.InvMap

variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ}

theorem mom_glMap (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by
  have hp : (Y.1.map φ) ^ i = (Y.1 ^ i).map φ := by
    have := map_pow φ.mapMatrix Y.1 i
    simpa only [RingHom.mapMatrix_apply] using this.symm
  simp only [mom, glMap, hp, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]

theorem inv_glMap (Y : Gl r k) : GlobalTheory.JR.inv (glMap φ Y) = (GlobalTheory.JR.inv Y).map φ := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, glMap, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    exact mom_glMap φ Y i

theorem sec_map (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · ext i j
    simp only [sec, companion, glMap, Inv.map, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  · funext i
    simp only [sec, glMap]
    split_ifs <;> simp

theorem Delta_map (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  rw [Delta, Delta, RingHom.map_det]
  congr 1
  ext i j
  simp only [hankel, sec_map, mom_glMap, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]

open Matrix MeasureTheory Filter Topology in
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ} in
private theorem mom_glMap_eq_map_mom (ψ : k →+* k') (Y : _root_.GlobalTheory.JR.Gl r k) (n : ℕ) :
    _root_.GlobalTheory.JR.mom (_root_.GlobalTheory.JR.Step.glMap ψ Y) n = ψ (_root_.GlobalTheory.JR.mom Y n) := by
  unfold _root_.GlobalTheory.JR.mom _root_.GlobalTheory.JR.Step.glMap
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_pow]
  rfl

open Matrix MeasureTheory Filter Topology in
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ} in
private theorem sec_map_eq_glMap_sec (ψ : k →+* k') (a : _root_.GlobalTheory.JR.Inv r k) :
    _root_.GlobalTheory.JR.sec (a.map ψ) = _root_.GlobalTheory.JR.Step.glMap ψ (_root_.GlobalTheory.JR.sec a) := by
  unfold _root_.GlobalTheory.JR.sec _root_.GlobalTheory.JR.Inv.map _root_.GlobalTheory.JR.Step.glMap
  simp only [_root_.GlobalTheory.JR.ImgSec.companion_map, Prod.mk.injEq, true_and, and_true]
  funext i
  split_ifs <;> simp

open Matrix MeasureTheory Filter Topology in
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ} in

theorem _root_.GlobalTheory.JR.Step.InvMap.inv_and_Delta_map : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ),
    (∀ Y : _root_.GlobalTheory.JR.Gl r k, _root_.GlobalTheory.JR.inv (_root_.GlobalTheory.JR.Step.glMap φ Y) = (_root_.GlobalTheory.JR.inv Y).map φ) ∧
      (∀ a : _root_.GlobalTheory.JR.Inv r k, _root_.GlobalTheory.JR.Delta (a.map φ) = φ (_root_.GlobalTheory.JR.Delta a)) := by
  intro k k' _ _ φ r
  refine ⟨fun Y => ?_, fun a => ?_⟩
  · unfold _root_.GlobalTheory.JR.inv _root_.GlobalTheory.JR.Inv.map
    simp only [mom_glMap_eq_map_mom]
    refine Prod.ext ?_ rfl
    funext i
    simp [_root_.GlobalTheory.JR.Step.glMap, Matrix.charpoly_map]
  · unfold _root_.GlobalTheory.JR.Delta
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.JR.hankel, sec_map_eq_glMap_sec, mom_glMap_eq_map_mom]

end GlobalTheory.JR.Step.InvMap
