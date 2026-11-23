import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolGrp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpUniMul

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolGrp

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLoUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) (h' : IsLoUni l') : IsLoUni (l * l') := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with hc | hc
    · rw [(h a c).1 hc, zero_mul]
    · rw [(h' c b).1 (lt_of_le_of_lt hc hab), mul_zero]
  · subst hab
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(h a a).2 rfl, (h' a a).2 rfl, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc' | hc'
      · rw [(h' c a).1 hc', mul_zero]
      · rw [(h a c).1 hc', zero_mul]
    · simp

theorem isUpUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) (h' : IsUpUni l') : IsUpUni (l * l') := by
  first | exact GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul .. | (apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h h' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R

theorem isLoUni_one : IsLoUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne, fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isUpUni_one : IsUpUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isLoUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) : IsLoUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_lo (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [hb hc', mul_zero]
    · rw [(h a c).1 hc', zero_mul]
  · simp

theorem isUpUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) : IsUpUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_up (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [(h a c).1 hc', zero_mul]
    · rw [hb hc', mul_zero]
  · simp

end Uni

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def stZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) : Subgroup (Formalism.L2.SG.PairVal.GLR D) where
  carrier := stZSet M δ u u' Z L
  one_mem' := by
    refine ⟨1, ?_, isLoUni_one, 1, isUpUni_one, by simp, fun p => ⟨1, 1, intLow_one _, intUp_one _, fun Z' => ?_⟩⟩
    · simp [Matrix.nonsing_inv_mul L hL]
    · simp [zhatOM_zhatOM]
  mul_mem' := by
    rintro x y ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩ ⟨y', hy, hyl, by', hby, hyZ, hyp⟩
    refine ⟨x' * y', ?_, ?_, by' * bx, isUpUni_mul hby hbx, ?_, fun p => ?_⟩
    · rw [Units.val_mul, hx, hy, Units.val_mul]
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L * (L⁻¹ * (y' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) * (y' : Formalism.L2.SG.PairVal.MatR D) * L := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv L hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    · rw [Units.val_mul]
      exact isLoUni_mul hxl hyl
    · rw [Units.val_mul]
      calc (x' : Formalism.L2.SG.PairVal.MatR D) * (y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) * ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * by') * bx := by
            simp only [Matrix.mul_assoc]
        _ = ZhatOM Z := by rw [hyZ, hxZ]
    · obtain ⟨l1, ρ1, hl1, hρ1, h1⟩ := hxp p
      obtain ⟨l2, ρ2, hl2, hρ2, h2⟩ := hyp p
      refine ⟨l1 * l2, ρ2 * ρ1, intLow_mul _ hl1 hl2, intUp_mul _ hρ2 hρ1, fun Z' => ?_⟩
      have e : ((x' * y' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) *
            ZhatOM (ZhatOM ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * by')) * bx := by
        rw [zhatOM_zhatOM, Units.val_mul]
        simp only [Matrix.mul_assoc]
      rw [e, h1, h2]
      simp only [Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩
    obtain ⟨hxi, hxi1, hxi2⟩ := isLoUni_inv hxl
    obtain ⟨hbi, hbi1, hbi2⟩ := isUpUni_inv hbx
    have hZ : ((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx⁻¹ = ZhatOM Z := by
      rw [Matrix.coe_units_inv]
      calc (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ZhatOM Z * bx⁻¹ =
          (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx) * bx⁻¹ := by rw [hxZ]
        _ = ZhatOM Z := by
          simp only [← Matrix.mul_assoc]
          rw [hxi1, Matrix.one_mul, Matrix.mul_assoc, hbi2, Matrix.mul_one]
    refine ⟨x'⁻¹, ?_, by rw [Matrix.coe_units_inv]; exact hxi, bx⁻¹, hbi, hZ, fun p => ?_⟩
    · rw [Matrix.coe_units_inv, Matrix.coe_units_inv, hx]
      have hLi := Matrix.nonsing_inv_mul L hL
      have hiL := Matrix.mul_nonsing_inv L hL
      refine Matrix.inv_eq_left_inv ?_
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * L * (L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * (L * L⁻¹) * (x' : Formalism.L2.SG.PairVal.MatR D)) * L := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hiL, Matrix.mul_one, hxi1, Matrix.mul_one, hLi]
    · obtain ⟨l, ρ, hl, hρ, h⟩ := hxp p
      obtain ⟨hli, hli1, hli2⟩ := intLow_inv _ hl
      obtain ⟨hρi, hρi1, hρi2⟩ := intUp_inv _ hρ
      refine ⟨l⁻¹, ρ⁻¹, hli, hρi, fun Z' => ?_⟩
      have h2 := h (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹))
      have e : (x' : Formalism.L2.SG.PairVal.MatR D) *
          ZhatOM (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹)) * bx =
          ZhatOM Z' := by
        rw [zhatOM_zhatOM, Matrix.coe_units_inv]
        simp only [← Matrix.mul_assoc]
        rw [hxi2, Matrix.one_mul, Matrix.mul_assoc, hbi1, Matrix.mul_one]
      rw [e, zhatOM_zhatOM] at h2
      rw [h2]
      simp only [← Matrix.mul_assoc]
      rw [hli1, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hρi2, Matrix.mul_one]

theorem mem_CZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) (a : Formalism.L2.SG.PairVal.GLR D) :
    a ∈ CZ M δ u u' Z L ↔ a ∈ stZSet M δ u u' Z L := by
  have e : CZ M δ u u' Z L = stZ M δ u u' Z L hL := by
    unfold CZ
    exact Subgroup.closure_eq (stZ M δ u u' Z L hL)
  rw [e]
  rfl

end Formalism.L2.SG.Pf.ZsVolGrp

end
