import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV

open scoped TensorProduct

section Alg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem coordRat_toLE_mul (g k : GL (Fin N) E) (v : Fin N → E) : toLE (g * k) v = toLE g (toLE k v) := by
  rw [toLE_apply, toLE_apply, toLE_apply, Units.val_mul, Matrix.mulVec_mulVec]

theorem coordRat_toLE_inv_apply (g : GL (Fin N) E) (v : Fin N → E) : toLE g⁻¹ (toLE g v) = v := by
  rw [← coordRat_toLE_mul, inv_mul_cancel, toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem coordRat_toLE_apply_inv (g : GL (Fin N) E) (v : Fin N → E) : toLE g (toLE g⁻¹ v) = v := by
  rw [← coordRat_toLE_mul, mul_inv_cancel, toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem coordRat_toLE_symm (g : GL (Fin N) E) (v : Fin N → E) : (toLE g).symm v = toLE g⁻¹ v := by
  apply (toLE g).injective
  rw [LinearEquiv.apply_symm_apply, coordRat_toLE_apply_inv]

theorem coordRat_inFr {a b : ℕ} (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (co γ : GL (Fin a) E) (co' γ' : GL (Fin b) E) (z : (Fin a → E) →ₗ[E] (Fin b → E)) (v : Fin a → E) :
    inFr (toStdCo σ J co) (toStdCo σ J' co') (inFr (stdG σ J γ) (stdG σ J' γ') z) v =
      toLE (co' * γ' * co'⁻¹)⁻¹ (inFr (toStdCo σ J co) (toStdCo σ J' co') z (toLE (co * γ * co⁻¹) v)) := by
  simp only [inFr, toStdCo, stdG, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, coordRat_toLE_symm, LinearEquiv.symm_apply_apply,
    _root_.mul_inv_rev, inv_inv, coordRat_toLE_mul, coordRat_toLE_inv_apply, coordRat_toLE_apply_inv]

end Alg

theorem seamHom_inFr_stdG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E) (γ' : GL (Fin (D.R.N (i + 1))) D.host.E)
      (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))),
      seamGL t.seam g.1 = A.crd i (Nat.le_of_succ_le hi) * γ * (A.crd i (Nat.le_of_succ_le hi))⁻¹ →
      seamGL t.seam g'.1 = A.crd (i + 1) hi * γ' * (A.crd (i + 1) hi)⁻¹ → ∀ z : HomE D.host.E (D.R.N i) (D.R.N (i + 1)),
      seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z) =
      g'.1.toLinearMap ∘ₗ seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi))
        (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
          (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)) ∘ₗ g.1.symm.toLinearMap) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi γ γ' g g' hg hg' z
  have hS : ∀ {p q : ℕ} (x : HomE D.host.E p q) (w : Sp t.X.E p),
      (fun l => t.seam.iE (seamHom t.seam x w l)) = x (fun k => t.seam.iE (w k)) :=
    fun x w => funext (seamHom_apply t.seam x w)
  have hG : ∀ {n : ℕ} (h : Sp t.X.E n ≃ₗ[t.X.E] Sp t.X.E n) (v : Sp t.X.E n),
      (fun l => t.seam.iE (h v l)) = toLE (seamGL t.seam h) (fun l => t.seam.iE (v l)) := by
    intro n h v
    rw [toLE_apply, seamGL_mulVec]
  have hw : ∀ {n : ℕ} (h : Sp t.X.E n ≃ₗ[t.X.E] Sp t.X.E n) (v : Sp t.X.E n),
      (fun l => t.seam.iE (h.symm v l)) = toLE (seamGL t.seam h)⁻¹ (fun l => t.seam.iE (v l)) := by
    intro n h v
    apply (toLE (seamGL t.seam h)).injective
    rw [← hG, LinearEquiv.apply_symm_apply, coordRat_toLE_apply_inv]
  refine LinearMap.ext fun w => funext fun l => ?_
  have key : (fun l => t.seam.iE (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z) w l)) =
      (fun l => t.seam.iE (g'.1 (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi))
        (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
          (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)) (g.1.symm w)) l)) := by
    rw [hG, hS, hS, hw, hg, hg', coordRat_inFr, coordRat_toLE_apply_inv, coordRat_toLE_apply_inv]
  exact t.seam.iE.injective (congrFun key l)

end GlobalTheory.TwV

end
