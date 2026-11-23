import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

open Matrix

section Gen

variable {E : Type} [Field E] {N : ℕ}

theorem unit_hform_mulVec (σ : E →+* E) (J B : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    hform σ J (B *ᵥ x) (B *ᵥ y) = hform σ (cT σ B * J * B) x y := by
  have key : ∀ (K : Matrix (Fin N) (Fin N) E) (v w : Fin N → E), hform σ K v w = (σ ∘ v) ⬝ᵥ (K *ᵥ w) := by
    intro K v w
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h1 : σ ∘ (B *ᵥ x) = (B.map σ) *ᵥ (σ ∘ x) := funext fun l => RingHom.map_mulVec σ B x l
  rw [key, key, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (σ ∘ x), cT,
    Matrix.vecMul_transpose]

theorem unit_hform_one (σ : E →+* E) (x y : Fin N → E) : hform σ 1 x y = ∑ a, σ (x a) * y a := by
  simp [hform, Matrix.one_apply]

theorem cT_mul_self_of_hform (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E)
    (h : ∀ x y, hform σ 1 (M *ᵥ x) (M *ᵥ y) = hform σ 1 x y) : cT σ M * M = 1 := by
  ext p q
  have h1 := h (Pi.single p 1) (Pi.single q 1)
  rw [unit_hform_mulVec, Matrix.mul_one] at h1
  simpa [hform, Pi.single_apply, apply_ite σ] using h1

end Gen

section Gen2

variable {E : Type} [Field E] {N : ℕ}

theorem cT_mul_self_toStdCo_stdG (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E)
    (hco : cT σ co.1 * co.1 = J) (hγ : γ ∈ UJ σ J) :
    cT σ (LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap) *
      LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap = 1 := by
  have hc : IsOrthCo σ J (toLE co) := by
    intro x y
    have h := unit_hform_mulVec σ 1 co.1 x y
    rw [Matrix.mul_one, hco, unit_hform_one] at h
    exact h
  have hs : IsOrthCo σ J (stdCo σ J) := Classical.epsilon_spec (p := IsOrthCo σ J) ⟨_, hc⟩
  have hγ' : cT σ γ.1 * J * γ.1 = J := hγ
  apply cT_mul_self_of_hform
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, unit_hform_one, unit_hform_one]
  obtain ⟨x, rfl⟩ := (toLE co).surjective x
  obtain ⟨y, rfl⟩ := (toLE co).surjective y
  rw [hc]
  simp only [toStdCo, stdG, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [hs]
  have h := unit_hform_mulVec σ J γ.1 x y
  rw [hγ'] at h
  exact h

end Gen2

theorem ratIsometry_unitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ i hi γ hγ
  have h := cT_mul_self_toStdCo_stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi) γ (hP.crd_orth i hi) hγ
  rw [mul_eq_one_comm] at h
  exact h

end GlobalTheory.TwV

end
