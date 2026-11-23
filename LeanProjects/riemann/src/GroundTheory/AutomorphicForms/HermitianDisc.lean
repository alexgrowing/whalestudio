import Mathlib
import GroundTheory.AutomorphicForms.HermitianWitt
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix GroundTheory.LocalField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

theorem gram_basis_change {ι : Type*} [Fintype ι] (B : V →ₛₗ[conjHom F E] V →ₗ[E] E)
    (b c : Basis ι E V) :
    gram B c = ((b.toMatrix c).map (conjHom F E))ᵀ * gram B b * b.toMatrix c := by
  ext i j
  rw [gram_apply, sesq_eq_sum B b]
  simp only [Matrix.mul_apply, transpose_apply, map_apply, Basis.toMatrix_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

namespace HermitianForm

variable [Algebra.IsSeparable F E]

theorem det_gram_mem_range (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : (gram h.toSesq b).det ∈ Set.range (algebraMap F E) := by
  apply conj_eq_self_iff.1
  rw [← conjHom_apply, RingHom.map_det, RingHom.mapMatrix_apply, ← det_transpose,
    isHermitianFor_gram h b]

def detUnit (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : Fˣ :=
  Units.mk0 (h.det_gram_mem_range b).choose (by
    intro h0
    have := (h.det_gram_mem_range b).choose_spec
    rw [h0, map_zero] at this
    exact (isUnit_det_gram h b).ne_zero this.symm)

theorem algebraMap_detUnit (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι E V) : algebraMap F E (h.detUnit b) = (gram h.toSesq b).det :=
  (h.det_gram_mem_range b).choose_spec

theorem detUnit_eq_of_det_eq (h : HermitianForm F E V) (h' : HermitianForm F E V')
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Basis ι E V) (b' : Basis ι' E V')
    (hb : (gram h.toSesq b).det = (gram h'.toSesq b').det) : h.detUnit b = h'.detUnit b' := by
  apply Units.ext
  apply (algebraMap F E).injective
  rw [algebraMap_detUnit, algebraMap_detUnit, hb]

theorem detUnit_basis_change (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : Basis ι E V) :
    ∃ u : Eˣ, h.detUnit c = h.detUnit b * normUnits F E u := by
  have hM : IsUnit (b.toMatrix c).det := by
    exact IsUnit.of_mul_eq_one (c.toMatrix b).det
      (by rw [← det_mul, Basis.toMatrix_mul_toMatrix_flip, det_one])
  refine ⟨hM.unit, Units.ext ((algebraMap F E).injective ?_)⟩
  rw [Units.val_mul, map_mul, algebraMap_detUnit, algebraMap_detUnit, coe_normUnits,
    IsUnit.unit_spec, ← mul_conj, gram_basis_change h.toSesq b c, det_mul, det_mul,
    det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, conjHom_apply]
  ring

def disc [FiniteDimensional E V] (h : HermitianForm F E V) : Fˣ ⧸ (normUnits F E).range :=
  QuotientGroup.mk (h.detUnit (Module.finBasis E V))

theorem disc_eq [FiniteDimensional E V] (h : HermitianForm F E V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι E V) : h.disc = QuotientGroup.mk (h.detUnit b) := by
  have hcard : Fintype.card ι = Fintype.card (Fin (finrank E V)) := by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis b]
  set e : ι ≃ Fin (finrank E V) := Fintype.equivOfCardEq hcard
  have h1 : h.detUnit (b.reindex e) = h.detUnit b := by
    apply detUnit_eq_of_det_eq
    have : gram h.toSesq (b.reindex e) = (gram h.toSesq b).submatrix e.symm e.symm := by
      ext i j; simp [gram_apply, Basis.reindex_apply]
    rw [this, det_submatrix_equiv_self]
  obtain ⟨u, hu⟩ := h.detUnit_basis_change (Module.finBasis E V) (b.reindex e)
  rw [disc, ← h1, hu]
  exact QuotientGroup.eq.2 (MonoidHom.mem_range.2 ⟨u, by rw [inv_mul_cancel_left]⟩)

theorem Isometric.disc_eq [FiniteDimensional E V] [FiniteDimensional E V']
    {h : HermitianForm F E V} {h' : HermitianForm F E V'} (H : Isometric h h') :
    h.disc = h'.disc := by
  obtain ⟨e, he⟩ := H
  set b := Module.finBasis E V
  rw [h.disc_eq b, h'.disc_eq (b.map e)]
  congr 1
  apply detUnit_eq_of_det_eq
  congr 1
  ext i j
  simp only [gram_apply, Basis.map_apply, he]

theorem disc_prod [FiniteDimensional E V] [FiniteDimensional E V'] (h : HermitianForm F E V)
    (h' : HermitianForm F E V') : (h.prod h').disc = h.disc * h'.disc := by
  set b := Module.finBasis E V
  set b' := Module.finBasis E V'
  rw [(h.prod h').disc_eq (b.prod b'), h.disc_eq b, h'.disc_eq b', ← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  apply (algebraMap F E).injective
  rw [Units.val_mul, map_mul, algebraMap_detUnit, algebraMap_detUnit, algebraMap_detUnit]
  have : gram (h.prod h').toSesq (b.prod b') =
      fromBlocks (gram h.toSesq b) 0 0 (gram h'.toSesq b') := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [gram_apply, Basis.prod_apply, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply] <;>
      rw [prod_apply] <;>
      simp only [LinearMap.map_zero, LinearMap.zero_apply, add_zero, zero_add]
  rw [this, det_fromBlocks_zero₂₁]

theorem disc_ofUnit (a : Fˣ) : (ofUnit (E := E) a).disc = QuotientGroup.mk a := by
  rw [disc_eq _ (Basis.singleton (Fin 1) E)]
  congr 1
  apply Units.ext
  apply (algebraMap F E).injective
  rw [algebraMap_detUnit, det_unique, gram_apply, Basis.singleton_apply, ofUnit_apply, map_one,
    one_mul, mul_one]

theorem disc_of_finrank_eq_zero [FiniteDimensional E V] (h : HermitianForm F E V)
    (hV : finrank E V = 0) : h.disc = 1 := by
  have : IsEmpty (Fin (finrank E V)) := by rw [hV]; infer_instance
  rw [disc]
  convert QuotientGroup.mk_one (normUnits F E).range
  apply Units.ext
  apply (algebraMap F E).injective
  rw [algebraMap_detUnit, det_isEmpty, Units.val_one, map_one]

end HermitianForm

def diagForm {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) :
    HermitianForm F E (ι → E) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E)
    (fun x y => ∑ i, conj F E (x i) * algebraMap F E (a i) * y i)
    (fun x x' y => by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
  isSymm := ⟨fun x y => by
    simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj,
      conj_algebraMap]
    exact Finset.sum_congr rfl fun i _ => by ring⟩
  nonsingular := by
    have ha : ∀ i, algebraMap F E (a i) ≠ 0 := fun i => by simp
    have key : ∀ (x : ι → E) (j : ι),
        (∑ i, conj F E (x i) * algebraMap F E (a i) * (Pi.single j 1 : ι → E) i) =
          conj F E (x j) * algebraMap F E (a j) := by
      intro x j
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [Pi.single_apply, hij]
      · simp
    constructor
    · intro x y hxy
      funext j
      have h1 := LinearMap.congr_fun hxy (Pi.single j 1)
      simp only [LinearMap.mk₂'ₛₗ_apply, key] at h1
      have h2 := mul_right_cancel₀ (ha j) h1
      rw [← conj_conj (F := F) (x j), h2, conj_conj]
    · intro f
      refine ⟨fun j => conj F E (f (Pi.single j 1) * (algebraMap F E (a j))⁻¹),
        LinearMap.ext fun y => ?_⟩
      simp only [LinearMap.mk₂'ₛₗ_apply, conj_conj]
      conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ f y]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (fun j => if i = j then (1 : E) else 0) = Pi.single i 1 := by
        funext j; simp [Pi.single_apply, eq_comm]
      rw [this, smul_eq_mul]
      field_simp [ha i]

theorem diagForm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) (x y : ι → E) :
    (diagForm (E := E) a).toSesq x y = ∑ i, conj F E (x i) * algebraMap F E (a i) * y i := rfl

end GroundTheory.Automorphic

end
