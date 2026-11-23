import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.hTens c JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.hTens c JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.hTens c JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.hTens GlobalTheory.WeilM.dbl
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.toCols₁_apply, Matrix.toCols₂_apply, Matrix.zero_apply, Matrix.neg_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, sub_eq_add_neg]

theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB) x y =
      GlobalTheory.WeilM.symp c ξ JA JB x.toCols₁ y.toCols₁ - GlobalTheory.WeilM.symp c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold GlobalTheory.WeilM.symp
  rw [hTens_dbl, mul_sub, map_sub]

theorem toCols₁_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₁ = x.toCols₁ + y.toCols₁ := rfl
theorem toCols₂_add' (x y : Matrix α (β ⊕ β) E) : (x + y).toCols₂ = x.toCols₂ + y.toCols₂ := rfl
theorem toCols₁_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₁ = r • x.toCols₁ := rfl
theorem toCols₂_smul' (r : R) (x : Matrix α (β ⊕ β) E) : (r • x).toCols₂ = r • x.toCols₂ := rfl

variable [Invertible (2 : R)]

def dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA (GlobalTheory.WeilM.dbl JB)) (κ ⊕ κ) where
  e :=
    { toFun := fun x => (Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1, Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2))
      invFun := fun q => Matrix.fromCols (d.e.symm (q.1 ∘ Sum.inl, q.2 ∘ Sum.inl))
        (d.e.symm (q.1 ∘ Sum.inr, -(q.2 ∘ Sum.inr)))
      map_add' := fun x y => by
        ext (i | i) <;> simp [toCols₁_add', toCols₂_add'] <;> abel
      map_smul' := fun r x => by
        ext (i | i) <;> simp [toCols₁_smul', toCols₂_smul']
      left_inv := fun x => by
        conv_rhs => rw [← Matrix.fromCols_toCols x]
        beta_reduce
        congr 1
        · exact d.e.symm_apply_apply x.toCols₁
        · have h : (((Sum.elim (d.e x.toCols₁).1 (d.e x.toCols₂).1) ∘ Sum.inr,
              -((Sum.elim (d.e x.toCols₁).2 (-(d.e x.toCols₂).2)) ∘ Sum.inr)) : (κ → R) × (κ → R)) =
              d.e x.toCols₂ := Prod.ext rfl (funext fun i => neg_neg _)
          exact (congrArg d.e.symm h).trans (d.e.symm_apply_apply _)
      right_inv := fun q => by
        ext (i | i) <;> simp }
  form w w' := by
    rw [symp_dbl, d.form, d.form]
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    ring

theorem isDblCoord_dblD {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {κ : Type} [Fintype κ]
    (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) : GlobalTheory.WeilM.IsDblCoord c ξ JA JB d (dblD c d) := by
  intro w₁ w₂
  simp [dblD]

end Gen

section Reindex

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem symp_submatrix (e : γ ≃ β) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α γ E) :
    GlobalTheory.WeilM.symp c ξ JA (JB.submatrix e e) x y =
      GlobalTheory.WeilM.symp c ξ JA JB (x.submatrix id e.symm) (y.submatrix id e.symm) := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← e.symm.sum_comp]
  simp

variable [Invertible (2 : R)]

def reD (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA J') κ where
  e := (Matrix.reindexLinearEquiv R E (Equiv.refl α) e).trans d.e
  form w w' := by
    rw [h, symp_submatrix, d.form]
    rfl

theorem reD_e (e : γ ≃ β) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {J' : Matrix γ γ E} (h : J' = JB.submatrix e e)
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ) (x : Matrix α γ E) :
    (reD c e h d).e x = d.e (x.submatrix id e.symm) := rfl

end Reindex

section Group

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def reG (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) :
    GlobalTheory.WeilM.UG c J →* GlobalTheory.WeilM.UG c J' :=
  ((Units.map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom).comp (GlobalTheory.WeilM.UG c J).subtype).codRestrict
    (GlobalTheory.WeilM.UG c J') fun g => by
      have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
      show (((g : GL β E) : Matrix β β E).submatrix e e)ᵀ * J' * (((g : GL β E) : Matrix β β E).submatrix e e).map c = J'
      rw [h, Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg]

theorem reG_val (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e) (g : GlobalTheory.WeilM.UG c J) :
    ((reG c e h g : GL γ E) : Matrix γ γ E) = ((g : GL β E) : Matrix β β E).submatrix e e := rfl

end Group

section Host

variable {D : D7}

def JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    Matrix (Fin (GlobalTheory.Doubling.dblSp S).rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E :=
  (GlobalTheory.WeilM.dbl JB).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem incM_JBd (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) :
    incM D.host.F (JBd S JB) =
      (GlobalTheory.WeilM.dbl (incM D.host.F JB)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp [JBd, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.WeilM.dbl, h1, h2]

variable [Invertible (2 : AF D.host.F)]

def ddr {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ) :
    GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F (JBd S JB)))
      (κ ⊕ κ) :=
  reD _ finSumFinEquiv.symm (incM_JBd S JB) (dblD _ co)

end Host

section HostGroup

variable {D : D7}

def omdOf {S T : HSp D} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {X : Type} [AddCommGroup X] [Module ℂ X]
    (omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (JBd S JB)) →* Module.End ℂ X) :
    GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) →* Module.End ℂ X :=
  omd₀.comp ((MonoidHom.inr _ _).comp (reG _ finSumFinEquiv.symm (incM_JBd S JB)))

end HostGroup

end GlobalTheory.DblSchr
