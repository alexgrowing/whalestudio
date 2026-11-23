import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)

namespace GlobalTheory.WeilSchrodinger.DblTarget

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix (α ⊕ α) β E) :
    GlobalTheory.WeilM.symp c ξ (GlobalTheory.WeilM.dbl JA) JB x y =
      GlobalTheory.WeilM.symp c ξ JA JB (x.submatrix Sum.inl id) (y.submatrix Sum.inl id) -
      GlobalTheory.WeilM.symp c ξ JA JB (x.submatrix Sum.inr id) (y.submatrix Sum.inr id) := by
  unfold GlobalTheory.WeilM.symp
  rw [← map_sub, ← mul_sub]
  congr 2
  simp only [GlobalTheory.WeilM.hTens, GlobalTheory.WeilM.dbl, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    Matrix.neg_apply, Matrix.submatrix_apply, id, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem symp_reindex {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι') (ξ : E)
    (JA : Matrix ι ι E) (JB : Matrix β β E) (x y : Matrix ι' β E) :
    GlobalTheory.WeilM.symp c ξ (Matrix.reindex e e JA) JB x y =
      GlobalTheory.WeilM.symp c ξ JA JB (x.submatrix e id) (y.submatrix e id) := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← e.sum_comp]
  simp [Matrix.reindex_apply]

variable [Invertible (2 : R)]

variable {c}

def dblRows {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ (GlobalTheory.WeilM.dbl JA) JB) (κ ⊕ κ) where
  e :=
    { toFun := fun x => (Sum.elim (d.e (x.submatrix Sum.inl id)).1 (d.e (x.submatrix Sum.inr id)).1,
        Sum.elim (d.e (x.submatrix Sum.inl id)).2 (-(d.e (x.submatrix Sum.inr id)).2))
      invFun := fun p => Matrix.fromRows (d.e.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
        (d.e.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
      map_add' := fun x y => by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
          simp [Matrix.submatrix_add, add_comm]
      map_smul' := fun r x => by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
          simp [Matrix.submatrix_smul]
      left_inv := fun x => by
        ext (i | i) j <;> simp [Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
      right_inv := fun p => by
        have h1 : ∀ (A B : Matrix α β E), (Matrix.fromRows A B).submatrix Sum.inl id = A := fun A B => by
          ext i j; simp [Matrix.fromRows_apply_inl]
        have h2 : ∀ (A B : Matrix α β E), (Matrix.fromRows A B).submatrix Sum.inr id = B := fun A B => by
          ext i j; simp [Matrix.fromRows_apply_inr]
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;>
          simp [h1, h2] }
  form w w' := by
    rw [symp_dbl, d.form, d.form]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    ring

theorem dblRows_e {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix (α ⊕ α) β E) :
    (dblRows d).e x = (Sum.elim (d.e (x.submatrix Sum.inl id)).1 (d.e (x.submatrix Sum.inr id)).1,
        Sum.elim (d.e (x.submatrix Sum.inl id)).2 (-(d.e (x.submatrix Sum.inr id)).2)) := rfl

theorem isDblCoord_transD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.IsDblCoord c ξ JB JA (transD c d) (transD c (dblRows d)) := by
  intro w₁ w₂
  have h1 : (Matrix.fromCols w₁ w₂)ᵀ.submatrix Sum.inl id = w₁ᵀ := by ext i j; simp [Matrix.fromCols]
  have h2 : (Matrix.fromCols w₁ w₂)ᵀ.submatrix Sum.inr id = w₂ᵀ := by ext i j; simp [Matrix.fromCols]
  change (dblRows d).e (Matrix.fromCols w₁ w₂)ᵀ =
    (Sum.elim (d.e w₁ᵀ).1 (d.e w₂ᵀ).1, Sum.elim (d.e w₁ᵀ).2 (-(d.e w₂ᵀ).2))
  rw [dblRows_e, h1, h2]

def reindexRows {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι') {ξ : E}
    {JA : Matrix ι ι E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (J' : Matrix ι' ι' E) (hJ : Matrix.reindex e e JA = J') :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ J' JB) κ where
  e := (Matrix.reindexLinearEquiv R E e.symm (Equiv.refl β)).trans d.e
  form w w' := by
    rw [← hJ, symp_reindex, d.form]
    rfl

theorem reindexRows_e {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι') {ξ : E}
    {JA : Matrix ι ι E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (J' : Matrix ι' ι' E) (hJ : Matrix.reindex e e JA = J')
    (x : Matrix ι' β E) : (reindexRows e d J' hJ).e x = d.e (x.submatrix e id) := rfl

end Gen

section Grp

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

def ugReindex (e : ι ≃ ι') {J : Matrix ι ι E} {J' : Matrix ι' ι' E} (hJ : Matrix.reindex e e J = J') :
    GlobalTheory.WeilM.UG c J →* GlobalTheory.WeilM.UG c J' where
  toFun g := ⟨Units.map (Matrix.reindexRingEquiv E e).toMonoidHom g.1, by
    have h := g.2
    change ((g : GL ι E) : Matrix ι ι E)ᵀ * J * ((g : GL ι E) : Matrix ι ι E).map c = J at h
    change (Matrix.reindex e e ((g : GL ι E) : Matrix ι ι E))ᵀ * J' *
      (Matrix.reindex e e ((g : GL ι E) : Matrix ι ι E)).map c = J'
    rw [← hJ]
    conv_rhs => rw [← h]
    simp only [Matrix.reindex_apply, Matrix.transpose_submatrix, ← Matrix.submatrix_map,
      Matrix.submatrix_mul_equiv]⟩
  map_one' := by
    ext1
    simp
  map_mul' g h := by
    ext1
    simp

theorem ugReindex_coe (e : ι ≃ ι') {J : Matrix ι ι E} {J' : Matrix ι' ι' E} (hJ : Matrix.reindex e e J = J')
    (g : GlobalTheory.WeilM.UG c J) :
    (((ugReindex e hJ g : GlobalTheory.WeilM.UG c J') : GL ι' E) : Matrix ι' ι' E) =
      Matrix.reindex e e ((g : GL ι E) : Matrix ι ι E) := rfl

theorem continuous_ugReindex [TopologicalSpace E] (e : ι ≃ ι') {J : Matrix ι ι E} {J' : Matrix ι' ι' E}
    (hJ : Matrix.reindex e e J = J') : Continuous (ugReindex (c := c) e hJ) := by
  refine Continuous.subtype_mk (Continuous.comp (Continuous.units_map _ ?_) continuous_subtype_val) _
  exact continuous_id.matrix_submatrix _ _

end Grp

section Transfer

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {c : E →ₐ[R] E} [Invertible (2 : R)]
variable [TopologicalSpace R] [TopologicalSpace E] {C : GlobalTheory.WeilM.TestClass R} {ψ : AddChar R ℂ} {ξ : E}
variable {ι ι' β : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype β] [DecidableEq β]
  {JA : Matrix ι ι E} {JB : Matrix β β E} {κ : Type} [Fintype κ]

theorem rho_transD_reindex (e : ι ≃ ι') (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (J' : Matrix ι' ι' E)
    (hJ : Matrix.reindex e e JA = J') (w : Matrix β ι E) :
    (transD c d).rho ψ w = (transD c (reindexRows e d J' hJ)).rho ψ (w.submatrix id e.symm) := by
  simp only [GlobalTheory.WeilM.Darboux.rho]
  congr 1
  show d.e wᵀ = d.e ((w.submatrix id e.symm)ᵀ.submatrix e id)
  congr 1
  ext i j
  simp

theorem actB_reindex (e : ι ≃ ι') {J' : Matrix ι' ι' E} (hJ : Matrix.reindex e e JA = J') (g : GlobalTheory.WeilM.UG c JA)
    (w : Matrix β ι E) :
    GlobalTheory.WeilM.actB c (ugReindex e hJ g) (w.submatrix id e.symm) = (GlobalTheory.WeilM.actB c g w).submatrix id e.symm := by
  simp only [GlobalTheory.WeilM.actB, ugReindex_coe, Matrix.reindex_apply, Matrix.transpose_submatrix]
  exact Matrix.submatrix_mul_equiv _ _ _ _ _

theorem isUSplitting_reindex (e : ι ≃ ι') (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (J' : Matrix ι' ι' E)
    (hJ : Matrix.reindex e e JA = J') {f : GlobalTheory.WeilM.UG c J' →* Module.End ℂ ((κ → R) → ℂ)}
    (h : GlobalTheory.WeilM.IsUSplitting C ψ (transD c (reindexRows e d J' hJ)) (GlobalTheory.WeilM.actB c) f) :
    GlobalTheory.WeilM.IsUSplitting C ψ (transD c d) (GlobalTheory.WeilM.actB c) (f.comp (ugReindex e hJ)) := by
  refine ⟨⟨fun g φ hφ => h.pres _ φ hφ, fun g w φ hφ => ?_, fun g l hl => h.adm _ l hl⟩, h.unit.comp _,
    h.cont.comp (continuous_ugReindex e hJ)⟩
  simp only [MonoidHom.comp_apply]
  rw [rho_transD_reindex e d J' hJ, rho_transD_reindex e d J' hJ, h.impl _ _ φ hφ, actB_reindex]

theorem siegelRule_reindex (e : ι ≃ ι') (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (J' : Matrix ι' ι' E)
    (hJ : Matrix.reindex e e JA = J') {f : GlobalTheory.WeilM.UG c J' →* Module.End ℂ ((κ → R) → ℂ)} (χ : Eˣ →* Circle)
    {ν : Type} [Fintype ν] [DecidableEq ν] (Cy : Matrix ι ν E)
    (h : GlobalTheory.WeilM.SiegelRule c C ψ ξ JB J' (transD c (reindexRows e d J' hJ)) χ (Cy.submatrix e.symm id) f) :
    GlobalTheory.WeilM.SiegelRule c C ψ ξ JB JA (transD c d) χ Cy (f.comp (ugReindex e hJ)) := by
  intro l hl hinv p t hpt φ hφ
  refine h l hl (fun z φ hφ => ?_) (ugReindex e hJ p) t ?_ φ hφ
  · have hz : (z * Cyᵀ).submatrix id e.symm = z * (Cy.submatrix e.symm id)ᵀ := by
      ext i j
      simp [Matrix.mul_apply]
    have := hinv z φ hφ
    rwa [rho_transD_reindex e d J' hJ, hz] at this
  · rw [ugReindex_coe, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hpt]
    ext i j
    simp [Matrix.mul_apply]

end Transfer

section Hsp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem reindex_dbl_incM (T : HSp D) {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (hA : JA = T.gramᵀ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (GlobalTheory.WeilM.dbl (incM D.host.F JA)) =
      incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ) := by
  subst hA
  rw [GlobalTheory.Doubling.gram_hdbl]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [GlobalTheory.WeilM.dbl, incM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, Matrix.transpose_apply, Matrix.map_apply] <;> simp

end Hsp

section HspCo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev coDbl {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hA : JA = T.gramᵀ) {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA)
      (incM D.host.F JB)) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
      (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) (incM D.host.F JB)) (κ ⊕ κ) :=
  reindexRows finSumFinEquiv (dblRows co) _ (reindex_dbl_incM T hA)

theorem coDbl_rat {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hA : JA = T.gramᵀ) {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA)
      (incM D.host.F JB)) κ)
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i))) :
    ∀ x : Matrix (Fin (GlobalTheory.Doubling.dblSp T).rank) (Fin S.rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (coDbl hA co).e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  intro x
  obtain ⟨y₁, z₁, h₁⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inl) id)
  obtain ⟨y₂, z₂, h₂⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inr) id)
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  have e₁ : ((incM D.host.F x).submatrix finSumFinEquiv id).submatrix Sum.inl id =
      incM D.host.F (x.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
  have e₂ : ((incM D.host.F x).submatrix finSumFinEquiv id).submatrix Sum.inr id =
      incM D.host.F (x.submatrix (finSumFinEquiv ∘ Sum.inr) id) := rfl
  rw [coDbl, reindexRows_e, dblRows_e, e₁, e₂, h₁, h₂]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;> simp

theorem isHeckeChar_one : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩

theorem resEta_one_dblSp (T : HSp D) {χ : (AE D)ˣ →* Circle} {k : ℕ} (hr : ResEta D χ k) :
    ResEta D 1 (GlobalTheory.Doubling.dblSp T).rank :=
  ⟨hr.1, fun η hη a => by
    have h4 := hη.2.2.1 (idF D a)
    have h5 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := Units.ext (by
      change Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) a.1) = _
      have := GlobalTheory.Doubling.t2Space_adeleRing' (F := D.host.F)
      have : Nontrivial (AF D.host.F) :=
        (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, D.sp.cm.deg2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = η a ^ (T.rank + T.rank)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

end HspCo

section UgDbl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ugDbl (T : HSp D) {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (hA : JA = T.gramᵀ) :
    GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA)) →*
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) :=
  ugReindex finSumFinEquiv (reindex_dbl_incM T hA)

theorem ugDbl_coe (T : HSp D) {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (hA : JA = T.gramᵀ)
    (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JA))) :
    (ugDbl T hA g).1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv g.1.1 := rfl

end UgDbl

end GlobalTheory.WeilSchrodinger.DblTarget

end
