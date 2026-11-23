import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierFlatCharacterDatumFiniteField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTwistFactorEqUnitMulFlatFourier
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000

namespace GlobalTheory.FlatForm

open GlobalTheory.FlatConj

theorem gaussGL_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ) :
    gaussGL ψ⁻¹ ξ⁻¹ r = (starRingEnd ℂ) (gaussGL ψ ξ r) := by
  unfold gaussGL
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, AddChar.inv_apply, AddChar.map_neg_eq_conj]
  congr 1
  set u := Matrix.GeneralLinearGroup.det x
  have h1 : ((ξ u : ℂˣ) : ℂ) ^ Fintype.card kˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  have h2 : ‖((ξ u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 Fintype.card_ne_zero
  rw [MonoidHom.inv_apply, inv_inv, Units.val_inv_eq_inv_val, map_inv₀, ← Complex.inv_eq_conj h2, inv_inv]

theorem gaussGL_mul_inv {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) :
    gaussGL ψ ξ r * gaussGL ψ⁻¹ ξ⁻¹ r = (Fintype.card k : ℂ) ^ (r ^ 2) := by
  obtain ⟨hnorm, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul k ψ ξ r hψ hξ (gaussGL ψ ξ r) rfl
  rw [gaussGL_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  push_cast
  rfl

theorem gaussGL_ne_zero {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussGL ψ ξ r ≠ 0 := fun h => by
  have := gaussGL_mul_inv ψ ξ r hψ hξ
  rw [h, zero_mul] at this
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) this.symm

theorem fourier_flat (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r t : ℕ) (hψ : ψ.IsPrimitive)
    (hξ : ξ ≠ 1) (u : Matrix (Fin (r + t)) (Fin r) k) :
    (∑ y : Matrix (Fin r) (Fin (r + t)) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
      ψ (Matrix.trace (y * u))) = ((Fintype.card k : ℂ) ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹) *
      (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  have hmul := gaussGL_mul_inv ψ ξ r hψ hξ
  have hne := gaussGL_ne_zero ψ ξ r hψ hξ
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hC : q ^ ((r + t) * r) * (gaussGL ψ ξ r)⁻¹ = q ^ (r * t) * G := by
    have hG' : gaussGL ψ⁻¹ ξ⁻¹ r = G := rfl
    rw [hG'] at hmul
    rw [show (r + t) * r = r * t + r ^ 2 by ring, pow_add, ← hmul]
    field_simp
  rw [hC]
  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dif_neg (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dif_neg, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dif_pos hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

theorem gaussP_ne_zero {E : Type} [Field E] [NumberField E] (PP : Pl E) (ψ : AddChar (kP PP) ℂ) (ξ : (kP PP)ˣ →* ℂˣ) (r : ℕ)
    (hψ : ψ.IsPrimitive) (hξ : ξ ≠ 1) : gaussP PP ψ ξ r ≠ 0 :=
  @gaussGL_ne_zero (kP PP) (resField PP) (resFintype PP) ψ ξ r hψ hξ

theorem omegaQ_eq_gauss_mul_flat_transform (D : D7) [inst : ∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (r n : ℕ) (hrn : r ≤ n)
    (hQ : ∀ PP ∈ Q, (ψP PP).IsPrimitive ∧ ξ PP ≠ 1) (ub : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaQ Q r ξ (-1) ub = (∏ PP ∈ Q, ((Nat.card (kP PP) : ℂ) ^ (n * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹))⁻¹ *
      ∑ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)),
        omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) *
          ∏ PP : ↥Q, ψP PP.1 (Matrix.trace (y PP * ub PP.1)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain rfl : inst = fun PP => resFintype PP := Subsingleton.elim _ _
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => resFintype PP
  let fl : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP) → ℂ := fun PP y =>
    if h : IsUnit (topL r y).det then ((ξ PP h.unit : ℂˣ) : ℂ) else 0
  let fq : ∀ PP : Pl D.host.E, Matrix (Fin (r + t)) (Fin r) (kP PP) → ℂ := fun PP u =>
    if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let C : Pl D.host.E → ℂ := fun PP => (Nat.card (kP PP) : ℂ) ^ ((r + t) * r) * (gaussP PP (ψP PP) (ξ PP) r)⁻¹
  have hC0 : ∀ PP : ↥Q, C PP ≠ 0 := fun PP =>
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
      (inv_ne_zero (gaussP_ne_zero _ _ _ _ (hQ _ PP.2).1 (hQ _ PP.2).2))
  have hCe : ∀ (PP : ↥Q) (u : Matrix (Fin (r + t)) (Fin r) (kP PP.1)),
      (∑ y : Matrix (Fin r) (Fin (r + t)) (kP PP.1), fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * u))) = C PP * fq PP.1 u := by
    intro PP u
    have := @fourier_flat (kP PP.1) (resField PP.1) (resFintype PP.1) (ψP PP.1) (ξ PP.1) r t (hQ _ PP.2).1 (hQ _ PP.2).2 u
    rw [← Nat.card_eq_fintype_card] at this
    exact this
  have hq : omegaQ Q r ξ (-1) ub = ∏ PP : ↥Q, fq PP.1 (ub PP.1) := by
    rw [← Finset.attach_eq_univ]
    unfold omegaQ
    convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => LowZero r (ub PP) ∧ IsUnit (topL r (ub PP)).det)
      (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
  have hf : ∀ y : (∀ PP : ↥Q, Matrix (Fin r) (Fin (r + t)) (kP PP.1)),
      omegaFlat Q r ξ (fun PP => if h : PP ∈ Q then -(y ⟨PP, h⟩) else 0) = ∏ PP : ↥Q, fl PP.1 (-(y PP)) := by
    intro y
    have e0 : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin (r + t)) (kP PP),
        omegaFlat Q r ξ Y = ∏ PP ∈ Q.attach, fl PP.1 (Y PP.1) := by
      intro Y
      unfold omegaFlat
      convert GlobalTheory.FlatFourierQ.dite_prod' Q (fun PP => IsUnit (topL r (Y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [e0, Finset.attach_eq_univ]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [dif_pos PP.2, Subtype.coe_eta]
  have hprod : (∏ PP ∈ Q, C PP) = ∏ PP : ↥Q, C PP := (Finset.prod_coe_sort Q C).symm
  show _ = (∏ PP ∈ Q, C PP)⁻¹ * _
  simp only [hf, ← Finset.prod_mul_distrib]
  have hs := Finset.prod_univ_sum (t := fun (PP : ↥Q) => (Finset.univ : Finset (Matrix (Fin r) (Fin (r + t)) (kP PP.1))))
    (f := fun (PP : ↥Q) (y : Matrix (Fin r) (Fin (r + t)) (kP PP.1)) => fl PP.1 (-y) * ψP PP.1 (Matrix.trace (y * ub PP.1)))
  rw [Fintype.piFinset_univ] at hs
  rw [← hs]
  simp only [hCe]
  rw [hprod, Finset.prod_mul_distrib (f := fun PP : ↥Q => C PP) (g := fun PP : ↥Q => fq PP.1 (ub PP.1)), hq, ← mul_assoc, inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun PP _ => hC0 PP), one_mul]

end GlobalTheory.FlatForm
