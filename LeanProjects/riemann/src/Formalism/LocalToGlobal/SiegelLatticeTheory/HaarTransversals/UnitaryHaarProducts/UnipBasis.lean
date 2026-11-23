import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipTool
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical

namespace Formalism.L2.SG.Pf.UnipB

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip

variable {D : D7} (X : HidaSetting D)

abbrev hE (x y : Fin X.B.I.n → X.B.I.E) : X.B.I.E := Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x y

theorem hE_add_right (x y z : Fin X.B.I.n → X.B.I.E) : hE X x (y + z) = hE X x y + hE X x z := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hE_smul_right (x y : Fin X.B.I.n → X.B.I.E) (c : X.B.I.E) : hE X x (c • y) = c * hE X x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_sub_right (x y z : Fin X.B.I.n → X.B.I.E) : hE X x (y - z) = hE X x y - hE X x z := by
  simp only [hE, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hE_zero_right (x : Fin X.B.I.n → X.B.I.E) : hE X x 0 = 0 := by
  simp only [hE, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem hE_sum_right {α : Type*} (s : Finset α) (x : Fin X.B.I.n → X.B.I.E) (y : α → Fin X.B.I.n → X.B.I.E) :
    hE X x (∑ a ∈ s, y a) = ∑ a ∈ s, hE X x (y a) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, hE_zero_right]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hE_add_right, ih]

theorem J_star (i j : Fin X.B.I.n) : star (X.B.I.J i j) = X.B.I.J j i := by
  have h := congrFun (congrFun X.B.I.J_herm j) i
  simpa [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] using h

theorem hE_symm (x y : Fin X.B.I.n → X.B.I.E) : hE X x y = star (hE X y x) := by
  simp only [hE, Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, J_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem star_host_apply {D : D7} (x : D.host.E) :
    (letI := D.host.cmStar; star x) = D.host.conj x := by
  let _ := D.host.cmStar
  have := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  rw [D.host.conjE_apply]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x

theorem hE_crd (v w : (VS D).V) : hE X (X.crd v) (X.crd w) = X.ιE.symm ((VS D).hT v w) := by
  apply X.ιE.injective
  rw [RingEquiv.apply_symm_apply]
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  simp only [hE, Formalism.UG.P.hform_eq_dot, dotProduct, mulVec, Function.comp_apply, map_sum, map_mul,
    LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul,
    starRingEnd_apply, X.ιE_conj, X.J_eq, HidaSetting.crd, crdOf, RingEquiv.apply_symm_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_host_apply]
  ring

variable (u : D.what₂.Word)

theorem hE_ee (a b : Fin D.R.rS) : hE X (X.eR a) (X.eR b) = 0 := by
  simp only [HidaSetting.eR]
  rw [hE_crd, X.ee, map_zero]

theorem hE_ff (a b : Fin D.R.rS) : hE X (X.fR a) (X.fR b) = 0 := by
  simp only [HidaSetting.fR]
  rw [hE_crd, X.ff, map_zero]

theorem hE_ef (a b : Fin D.R.rS) : hE X (X.eR a) (X.fR b) = if a = b then 1 else 0 := by
  simp only [HidaSetting.eR, HidaSetting.fR]
  rw [hE_crd, X.ef]
  split_ifs <;> simp

theorem hE_fe (a b : Fin D.R.rS) : hE X (X.fR a) (X.eR b) = if a = b then 1 else 0 := by
  rw [hE_symm, hE_ef]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem hE_ez (a : Fin D.R.rS) : hE X (X.eR a) (X.zR u) = 0 := by
  simp only [HidaSetting.eR, HidaSetting.zR]
  rw [hE_crd, (X.zu_orth u a).1, map_zero]

theorem hE_fz (a : Fin D.R.rS) : hE X (X.fR a) (X.zR u) = 0 := by
  simp only [HidaSetting.fR, HidaSetting.zR]
  rw [hE_crd, (X.zu_orth u a).2, map_zero]

def Wsub : Submodule X.B.I.E (Fin X.B.I.n → X.B.I.E) where
  carrier := {x | ∀ a, hE X (X.eR a) x = 0 ∧ hE X (X.fR a) x = 0}
  add_mem' := by
    intro x y hx hy a
    rw [hE_add_right, hE_add_right, (hx a).1, (hx a).2, (hy a).1, (hy a).2]
    simp
  zero_mem' := by
    intro a
    simp [hE_zero_right]
  smul_mem' := by
    intro c x hx a
    rw [hE_smul_right, hE_smul_right, (hx a).1, (hx a).2]
    simp

abbrev mW : ℕ := Module.finrank X.B.I.E (Wsub X)

def wb : Module.Basis (Fin (mW X)) X.B.I.E (Wsub X) := Module.finBasis X.B.I.E (Wsub X)

abbrev Kap : Type := Fin D.R.rS ⊕ Fin (mW X) ⊕ Fin D.R.rS

def bv : Kap X → Fin X.B.I.n → X.B.I.E :=
  Sum.elim X.eR (Sum.elim (fun i => ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E)) X.fR)

def lvk : Kap X → ℕ :=
  Sum.elim (fun a => a.1 + 1) (Sum.elim (fun _ => D.R.rS + 1) (fun a => 2 * D.R.rS + 1 - a.1))

theorem lvk_le (k : Kap X) : lvk X k ≤ 2 * D.R.rS + 1 := by
  rcases k with a | i | a
  · have := a.isLt
    simp only [lvk, Sum.elim_inl]
    omega
  · simp only [lvk, Sum.elim_inr, Sum.elim_inl]
    omega
  · have := a.isLt
    simp only [lvk, Sum.elim_inr]
    omega

def pW (x : Fin X.B.I.n → X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  x - ∑ a, hE X (X.fR a) x • X.eR a - ∑ a, hE X (X.eR a) x • X.fR a

theorem pW_mem (x : Fin X.B.I.n → X.B.I.E) : pW X x ∈ Wsub X := by
  show ∀ a, hE X (X.eR a) (pW X x) = 0 ∧ hE X (X.fR a) (pW X x) = 0
  intro a
  constructor
  · simp [pW, hE_sub_right, hE_sum_right, hE_smul_right, hE_ee, hE_ef, mul_boole, Finset.sum_ite_eq]
  · simp [pW, hE_sub_right, hE_sum_right, hE_smul_right, hE_ff, hE_fe, mul_boole, Finset.sum_ite_eq]

theorem pW_add (x y : Fin X.B.I.n → X.B.I.E) : pW X (x + y) = pW X x + pW X y := by
  simp only [pW, hE_add_right, add_smul, Finset.sum_add_distrib]
  abel

theorem pW_smul (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) : pW X (c • x) = c • pW X x := by
  simp only [pW, hE_smul_right, smul_sub, Finset.smul_sum, mul_smul]

def cE : (Fin X.B.I.n → X.B.I.E) →ₗ[X.B.I.E] (Kap X → X.B.I.E) where
  toFun x := Sum.elim (fun a => hE X (X.fR a) x)
    (Sum.elim (fun i => (wb X).repr ⟨pW X x, pW_mem X x⟩ i) (fun a => hE X (X.eR a) x))
  map_add' x y := by
    funext k
    rcases k with a | i | a
    · simp [hE_add_right]
    · have : (⟨pW X (x + y), pW_mem X (x + y)⟩ : Wsub X) = ⟨pW X x, pW_mem X x⟩ + ⟨pW X y, pW_mem X y⟩ :=
        Subtype.ext (pW_add X x y)
      show (wb X).repr ⟨pW X (x + y), pW_mem X (x + y)⟩ i =
        (wb X).repr ⟨pW X x, pW_mem X x⟩ i + (wb X).repr ⟨pW X y, pW_mem X y⟩ i
      rw [this, map_add]
      rfl
    · simp [hE_add_right]
  map_smul' c x := by
    funext k
    rcases k with a | i | a
    · simp [hE_smul_right]
    · have : (⟨pW X (c • x), pW_mem X (c • x)⟩ : Wsub X) = c • ⟨pW X x, pW_mem X x⟩ :=
        Subtype.ext (pW_smul X c x)
      show (wb X).repr ⟨pW X (c • x), pW_mem X (c • x)⟩ i = c * (wb X).repr ⟨pW X x, pW_mem X x⟩ i
      rw [this, map_smul]
      rfl
    · simp [hE_smul_right]

theorem sum_kap {M : Type*} [AddCommMonoid M] (g : Kap X → M) :
    ∑ k, g k = ∑ a, g (Sum.inl a) + ∑ i, g (Sum.inr (Sum.inl i)) + ∑ a, g (Sum.inr (Sum.inr a)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]

theorem cE_recon (x : Fin X.B.I.n → X.B.I.E) : ∑ k, cE X x k • bv X k = x := by
  rw [sum_kap]
  have h := congrArg Subtype.val ((wb X).sum_repr ⟨pW X x, pW_mem X x⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  simp only [cE, bv, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, h]
  simp only [pW]
  abel

theorem wb_mem (i : Fin (mW X)) (a : Fin D.R.rS) :
    hE X (X.eR a) ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E) = 0 ∧
      hE X (X.fR a) ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E) = 0 := by
  have h := (wb X i).2
  exact h a

theorem pW_of_mem {x : Fin X.B.I.n → X.B.I.E} (hx : x ∈ Wsub X) : pW X x = x := by
  have hx' : ∀ a, hE X (X.eR a) x = 0 ∧ hE X (X.fR a) x = 0 := hx
  have h1 : ∀ a, hE X (X.eR a) x = 0 := fun a => (hx' a).1
  have h2 : ∀ a, hE X (X.fR a) x = 0 := fun a => (hx' a).2
  simp only [pW, h1, h2, zero_smul, Finset.sum_const_zero, sub_zero]

theorem cE_bv (k k' : Kap X) : cE X (bv X k) k' = if k' = k then 1 else 0 := by
  have hw1 : ∀ i a, hE X (X.eR a) ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E) = 0 := fun i a => (wb_mem X i a).1
  have hw2 : ∀ i a, hE X (X.fR a) ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E) = 0 := fun i a => (wb_mem X i a).2
  have pe : ∀ a, (⟨pW X (X.eR a), pW_mem X (X.eR a)⟩ : Wsub X) = 0 := fun a => Subtype.ext (by
    simp [pW, hE_fe, hE_ee, ite_smul, Finset.sum_ite_eq'])
  have pf : ∀ a, (⟨pW X (X.fR a), pW_mem X (X.fR a)⟩ : Wsub X) = 0 := fun a => Subtype.ext (by
    simp [pW, hE_ff, hE_ef, ite_smul, Finset.sum_ite_eq'])
  have pw : ∀ i, (⟨pW X ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E), pW_mem X _⟩ : Wsub X) = wb X i :=
    fun i => Subtype.ext (pW_of_mem X (wb X i).2)
  rcases k with a | i | a <;> rcases k' with b | j | b <;>
    simp only [cE, bv, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr, pe, pf, pw,
      map_zero, Finsupp.coe_zero, Pi.zero_apply, Module.Basis.repr_self, Finsupp.single_apply,
      hE_fe, hE_ee, hE_ff, hE_ef, hw1, hw2, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte]
  all_goals split_ifs <;> simp_all

def Bm : Matrix (Fin X.B.I.n) (Kap X) X.B.I.E := Matrix.of fun i k => bv X k i
def Bm' : Matrix (Kap X) (Fin X.B.I.n) X.B.I.E := Matrix.of fun k i => cE X (Pi.single i 1) k

theorem Bm'_mulVec (x : Fin X.B.I.n → X.B.I.E) : Bm' X *ᵥ x = cE X x := by
  have hB : Bm' X = LinearMap.toMatrix' (cE X) := by
    ext k i
    simp only [Bm', Matrix.of_apply, LinearMap.toMatrix'_apply]
    try (congr 2; funext j'; simp [Pi.single_apply])
  rw [hB, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

theorem Bm_mulVec (c : Kap X → X.B.I.E) : Bm X *ᵥ c = ∑ k, c k • bv X k := by
  funext i
  simp only [Bm, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem Bm_mul_Bm' : Bm X * Bm' X = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Bm'_mulVec, Bm_mulVec, cE_recon, Matrix.one_mulVec]

theorem Bm'_mul_Bm : Bm' X * Bm X = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro c
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Bm_mulVec, Bm'_mulVec, map_sum, Matrix.one_mulVec]
  funext k'
  simp [Finset.sum_apply, cE_bv]

def JB : Matrix (Kap X) (Kap X) X.B.I.E := Matrix.of fun k k' => hE X (bv X k) (bv X k')

theorem JB_eq : JB X = (Bm X)ᴴ * X.B.I.J * Bm X := by
  ext k k'
  simp only [JB, Matrix.of_apply, hE, Formalism.UG.hform, Matrix.mul_apply, Matrix.conjTranspose_apply, Bm, starRingEnd_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem JB_herm : (JB X)ᴴ = JB X := by
  ext k k'
  simp only [Matrix.conjTranspose_apply, JB, Matrix.of_apply]
  exact (hE_symm X _ _).symm

theorem JB_graded : Graded (lvk X) (2 * D.R.rS + 2) (JB X) := by
  have hw1 : ∀ a i, hE X (X.eR a) ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E) = 0 := fun a i => (wb_mem X i a).1
  have hw2 : ∀ a i, hE X (X.fR a) ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E) = 0 := fun a i => (wb_mem X i a).2
  have hw3 : ∀ a i, hE X ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E) (X.eR a) = 0 := fun a i => by
    rw [hE_symm, hw1, star_zero]
  have hw4 : ∀ a i, hE X ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E) (X.fR a) = 0 := fun a i => by
    rw [hE_symm, hw2, star_zero]
  intro k k' h
  rcases k with a | i | a <;> rcases k' with b | j | b <;>
    simp only [JB, Matrix.of_apply, bv, Sum.elim_inl, Sum.elim_inr, lvk, hE_ee, hE_ff, hE_ef, hE_fe,
      hw1, hw2, hw3, hw4, ne_eq, not_true_eq_false, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at h ⊢
  all_goals first
    | omega
    | (have ha := a.isLt; have hb := b.isLt; subst h; omega)

theorem JB_e_row (a : Fin D.R.rS) (k : Kap X) :
    JB X (Sum.inl a) k = if k = Sum.inr (Sum.inr a) then 1 else 0 := by
  have hw1 : ∀ a i, hE X (X.eR a) ((wb X i : Wsub X) : Fin X.B.I.n → X.B.I.E) = 0 := fun a i => (wb_mem X i a).1
  rcases k with b | j | b
  · simp [JB, bv, hE_ee]
  · simp [JB, bv, hw1]
  · simp only [JB, Matrix.of_apply, bv, Sum.elim_inl, Sum.elim_inr, hE_ef, Sum.inr.injEq]
    by_cases h : a = b
    · subst h
      simp [hE_ef]
    · simp [hE_ef, h, Ne.symm h]

def JB' : Matrix (Kap X) (Kap X) X.B.I.E := Bm' X * (X.B.I.J)⁻¹ * (Bm' X)ᴴ

theorem J_unit : IsUnit X.B.I.J.det := isUnit_iff_ne_zero.mpr X.B.I.J_det

theorem JB_mul_JB' : JB X * JB' X = 1 := by
  have h1 : Bm X * Bm' X = 1 := Bm_mul_Bm' X
  have hJ : X.B.I.J * (X.B.I.J)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (J_unit X)
  rw [JB_eq, JB']
  calc (Bm X)ᴴ * X.B.I.J * Bm X * (Bm' X * (X.B.I.J)⁻¹ * (Bm' X)ᴴ)
      = (Bm X)ᴴ * (X.B.I.J * ((Bm X * Bm' X) * ((X.B.I.J)⁻¹ * (Bm' X)ᴴ))) := by
        simp only [Matrix.mul_assoc]
    _ = (Bm X)ᴴ * (Bm' X)ᴴ := by
        rw [h1, Matrix.one_mul, ← Matrix.mul_assoc X.B.I.J, hJ, Matrix.one_mul]
    _ = 1 := by
        rw [← Matrix.conjTranspose_mul, Bm'_mul_Bm, Matrix.conjTranspose_one]

theorem JB'_mul_JB : JB' X * JB X = 1 := by
  rw [← Matrix.inv_eq_right_inv (JB_mul_JB' X)]
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse (JB_mul_JB' X))

theorem JB'_eq_inv : JB' X = (JB X)⁻¹ := (Matrix.inv_eq_right_inv (JB_mul_JB' X)).symm

theorem JB'_graded : Graded (lvk X) (2 * D.R.rS + 2) (JB' X) := by
  have hG := JB_graded X
  let K' : Matrix (Kap X) (Kap X) X.B.I.E :=
    Matrix.of fun i k => if lvk X i + lvk X k = 2 * D.R.rS + 2 then JB' X i k else 0
  have hK'def : ∀ i k, K' i k = if lvk X i + lvk X k = 2 * D.R.rS + 2 then JB' X i k else 0 :=
    fun i k => rfl
  have hmul : JB X * K' = 1 := by
    ext i k
    have h1 := congrFun (congrFun (JB_mul_JB' X) i) k
    rw [Matrix.mul_apply] at h1 ⊢
    by_cases hik : lvk X k = lvk X i
    · rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : JB X i j = 0
      · simp [hj]
      · have := hG i j hj
        have hc : lvk X j + lvk X k = 2 * D.R.rS + 2 := by omega
        rw [hK'def, if_pos hc]
    · have hne : i ≠ k := fun h => hik (by rw [h])
      rw [Matrix.one_apply_ne hne]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : JB X i j = 0
      · simp [hj]
      · have := hG i j hj
        have hc : ¬ (lvk X j + lvk X k = 2 * D.R.rS + 2) := by omega
        rw [hK'def, if_neg hc, mul_zero]
  have hK : K' = JB' X :=
    (Matrix.inv_eq_right_inv hmul).symm.trans (Matrix.inv_eq_right_inv (JB_mul_JB' X))
  intro i k h
  rw [← hK] at h
  by_contra hc
  exact h (by rw [hK'def, if_neg hc])

theorem JB'_herm : (JB' X)ᴴ = JB' X := by
  rw [JB'_eq_inv, Matrix.conjTranspose_nonsing_inv, JB_herm]

section Half

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]

theorem half_to_full {lv : ι → ℕ} {T h₀ : ℕ} {J J' : Matrix ι ι K} (hJ : Graded lv T J) (hJ' : Graded lv T J')
    (h : J' * J = 1) (hT : T ≤ 2 * h₀ + 1) {M N : Matrix ι ι K} (hMN : M = sharp J J' N)
    (hN : ∀ i j, lv j ≤ h₀ → lv j < lv i + 1 → (N - 1) i j = 0)
    (hM : ∀ i j, lv j ≤ h₀ → lv j < lv i + 1 → (M - 1) i j = 0) : InPat lv 1 (M - 1) := by
  intro i j hij
  by_cases hj : lv j ≤ h₀
  · exact hM i j hj hij
  · have hM1 : M - 1 = J' * (Nᴴ - 1) * J := by
      rw [hMN, sharp, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]
    rw [hM1, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hp : J' i p = 0
    · simp [hp]
    by_cases hq : J q j = 0
    · simp [hq]
    have e1 := hJ' i p hp
    have e2 := hJ q j hq
    have hz : (N - 1) q p = 0 := hN q p (by omega) (by omega)
    have hz' : (Nᴴ - 1) p q = 0 := by
      rw [← Matrix.conjTranspose_one, ← Matrix.conjTranspose_sub, Matrix.conjTranspose_apply, hz, star_zero]
    simp [hz']

end Half

section Real

variable (v : InfinitePlace X.B.I.F)

theorem phi_star (a : X.B.I.E) : X.B.I.φ v (star a) = star (X.B.I.φ v a) := by
  rw [X.B.I.cm.cmUnram.2.1, starRingEnd_apply]

theorem map_conjTranspose {m p : Type*} (M : Matrix m p X.B.I.E) :
    (M.map (X.B.I.φ v))ᴴ = Mᴴ.map (X.B.I.φ v) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  exact (phi_star X v _).symm

theorem P_unit' : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v)

def Bv : Matrix (Fin X.B.I.n) (Kap X) ℂ := (X.B.I.P v)⁻¹ * (Bm X).map (X.B.I.φ v)
def Bv' : Matrix (Kap X) (Fin X.B.I.n) ℂ := (Bm' X).map (X.B.I.φ v) * X.B.I.P v

theorem Bv'_mul_Bv : Bv' X v * Bv X v = 1 := by
  have h1 : ((1 : Matrix (Kap X) (Kap X) X.B.I.E).map (X.B.I.φ v)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [Bv, Bv']
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (X.B.I.P v), Matrix.mul_nonsing_inv _ (P_unit' X v),
    Matrix.one_mul, ← Matrix.map_mul, Bm'_mul_Bm, h1]

theorem Bv_mul_Bv' : Bv X v * Bv' X v = 1 := by
  have h1 : ((1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [Bv, Bv']
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((Bm X).map (X.B.I.φ v)), ← Matrix.map_mul, Bm_mul_Bm', h1,
    Matrix.one_mul, Matrix.nonsing_inv_mul _ (P_unit' X v)]

theorem Bv_col (k : Kap X) : Bv X v *ᵥ Pi.single k 1 = rv X.B.I v (bv X k) := by
  simp only [rv, Bv]
  rw [← Matrix.mulVec_mulVec]
  congr 1
  funext i
  simp [Matrix.mulVec, Bm]

theorem Bv'_rv (k : Kap X) : Bv' X v *ᵥ rv X.B.I v (bv X k) = Pi.single k 1 := by
  rw [← Bv_col, Matrix.mulVec_mulVec, Bv'_mul_Bv, Matrix.one_mulVec]

def JBv : Matrix (Kap X) (Kap X) ℂ := (JB X).map (X.B.I.φ v)
def JBv' : Matrix (Kap X) (Kap X) ℂ := (JB' X).map (X.B.I.φ v)

theorem JBv_graded : Graded (lvk X) (2 * D.R.rS + 2) (JBv X v) := by
  intro k k' h
  exact JB_graded X k k' (fun h0 => h (by simp [JBv, h0]))

theorem JBv'_graded : Graded (lvk X) (2 * D.R.rS + 2) (JBv' X v) := by
  intro k k' h
  exact JB'_graded X k k' (fun h0 => h (by simp [JBv', h0]))

theorem JBv'_mul : JBv' X v * JBv X v = 1 := by
  have h1 : ((1 : Matrix (Kap X) (Kap X) X.B.I.E).map (X.B.I.φ v)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [JBv, JBv']
  rw [← Matrix.map_mul, JB'_mul_JB, h1]

theorem JBv_mul : JBv X v * JBv' X v = 1 := by
  have h1 : ((1 : Matrix (Kap X) (Kap X) X.B.I.E).map (X.B.I.φ v)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [JBv, JBv']
  rw [← Matrix.map_mul, JB_mul_JB', h1]

theorem JBv_herm : (JBv X v)ᴴ = JBv X v := by
  simp only [JBv]
  rw [map_conjTranspose, JB_herm]

theorem JBv'_herm : (JBv' X v)ᴴ = JBv' X v := by
  simp only [JBv']
  rw [map_conjTranspose, JB'_herm]

theorem Bv_gram : (Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v = JBv X v := by
  have hQ : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (P_unit' X v)
  have hQ' : ((X.B.I.P v)⁻¹)ᴴ * (X.B.I.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
  simp only [Bv, JBv]
  rw [← X.B.I.P_spec v, JB_eq, Matrix.map_mul, Matrix.map_mul, ← map_conjTranspose, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (X.B.I.P v), hQ, Matrix.one_mul, ← Matrix.mul_assoc ((X.B.I.P v)⁻¹)ᴴ, hQ', Matrix.one_mul]

def Mv (s : X.B.I.Ginf) : Matrix (Kap X) (Kap X) ℂ := Bv' X v * uMat (s v) * Bv X v

theorem uMat_eq (s : X.B.I.Ginf) : uMat (s v) = Bv X v * Mv X v s * Bv' X v := by
  simp only [Mv]
  simp only [← Matrix.mul_assoc]
  rw [Bv_mul_Bv', Matrix.one_mul, Matrix.mul_assoc, Bv_mul_Bv', Matrix.mul_one]

theorem Mv_mul (s t : X.B.I.Ginf) : Mv X v (s * t) = Mv X v s * Mv X v t := by
  have hm : ∀ g h : Formalism.REAL.UJ (X.B.I.ε v), uMat (g * h) = uMat g * uMat h := fun g h => by
    simp [uMat]
  simp only [Mv, Pi.mul_apply, hm, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bv X v), Bv_mul_Bv', Matrix.one_mul]

theorem Mv_one : Mv X v 1 = 1 := by
  simp [Mv, uMat, Bv'_mul_Bv]

theorem Mv_unitary (s : X.B.I.Ginf) : (Mv X v s)ᴴ * JBv X v * Mv X v s = JBv X v := by
  have hU : (uMat (s v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (s v) = Formalism.REAL.Jm (X.B.I.ε v) := (s v).2
  have hU' : ∀ Z : Matrix (Fin X.B.I.n) (Kap X) ℂ,
      (uMat (s v))ᴴ * (Formalism.REAL.Jm (X.B.I.ε v) * (uMat (s v) * Z)) = Formalism.REAL.Jm (X.B.I.ε v) * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hU]
  have hB : (Bv' X v)ᴴ * (Bv X v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Bv_mul_Bv', Matrix.conjTranspose_one]
  rw [← Bv_gram]
  simp only [Mv, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bv' X v)ᴴ, hB, Matrix.one_mul, ← Matrix.mul_assoc (Bv X v), Bv_mul_Bv', Matrix.one_mul, hU']

theorem Mv_inv (s : X.B.I.Ginf) : Mv X v s⁻¹ = sharp (JBv X v) (JBv' X v) (Mv X v s) := by
  have h1 : Mv X v s * Mv X v s⁻¹ = 1 := by
    rw [← Mv_mul, mul_inv_cancel, Mv_one]
  have h2 : sharp (JBv X v) (JBv' X v) (Mv X v s) * Mv X v s = 1 := by
    rw [sharp, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (JBv X v), Mv_unitary, JBv'_mul]
  calc Mv X v s⁻¹ = (sharp (JBv X v) (JBv' X v) (Mv X v s) * Mv X v s) * Mv X v s⁻¹ := by
        rw [h2, Matrix.one_mul]
    _ = sharp (JBv X v) (JBv' X v) (Mv X v s) := by
        rw [Matrix.mul_assoc, h1, Matrix.mul_one]

end Real

end Formalism.L2.SG.Pf.UnipB
