import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormSqLine

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} (ε : Fin n → Bool)

structure Frm (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (T : ℝ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ep : ∀ a b, hJ ε (e a) (p b) = if a = b then 1 else 0
  pp : ∀ a b, hJ ε (p a) (p b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  pz : ∀ a, hJ ε (p a) z = 0
  zz : hJ ε z z = -(T : ℂ)
  ew : ∀ a j, hJ ε (e a) (w j) = 0
  pw : ∀ a j, hJ ε (p a) (w j) = 0
  zw : ∀ j, hJ ε z (w j) = 0
  ww : ∀ i j, hJ ε (w i) (w j) = if i = j then 1 else 0
  T_ne : T ≠ 0

variable {ε}

theorem hJ_swap0 {x y : Fin n → ℂ} (h : hJ ε x y = 0) : hJ ε y x = 0 := by
  rw [UnitaryIsometries.hJ_conj, h, map_zero]

theorem hJ_swapδ {ι : Type*} [DecidableEq ι] {x y : ι → Fin n → ℂ} (h : ∀ a b, hJ ε (x a) (y b) = if a = b then 1 else 0)
    (a b : ι) : hJ ε (y b) (x a) = if a = b then 1 else 0 := by
  rw [UnitaryIsometries.hJ_conj, h]
  split_ifs <;> simp

def syn (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) (T : ℝ)
    (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) : Fin n → ℂ :=
  ∑ a, α a • e a + ∑ a, β a • p a + (-γ / (T : ℂ)) • z + ∑ j, δ j • w j

section Coord

variable {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {w : Fin k → Fin n → ℂ} {T : ℝ}

theorem hJ_syn (x : Fin n → ℂ) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ) :
    hJ ε x (syn e p z w T α β γ δ) = ∑ a, α a * hJ ε x (e a) + ∑ a, β a * hJ ε x (p a) +
      (-γ / (T : ℂ)) * hJ ε x z + ∑ j, δ j * hJ ε x (w j) := by
  simp only [syn, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, UnitaryIsometries.hJ_sum_right]

theorem syn_p (F : Frm ε e p z w T) (c : Fin r) α β γ δ : hJ ε (p c) (syn e p z w T α β γ δ) = α c := by
  rw [hJ_syn]
  simp [hJ_swapδ F.ep, F.pp, F.pz, F.pw]

theorem syn_e (F : Frm ε e p z w T) (c : Fin r) α β γ δ : hJ ε (e c) (syn e p z w T α β γ δ) = β c := by
  rw [hJ_syn]
  simp [F.ee, F.ep, F.ez, F.ew]

theorem synthesized_vector_z_pairing (F : Frm ε e p z w T) α β γ δ : hJ ε z (syn e p z w T α β γ δ) = γ := by
  rw [hJ_syn]
  have hT : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 F.T_ne
  simp only [fun a => hJ_swap0 (F.ez a), fun a => hJ_swap0 (F.pz a), F.zz, F.zw, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero]
  field_simp

theorem syn_w (F : Frm ε e p z w T) (c : Fin k) α β γ δ : hJ ε (w c) (syn e p z w T α β γ δ) = δ c := by
  rw [hJ_syn]
  simp [fun a => hJ_swap0 (F.ew a c), fun a => hJ_swap0 (F.pw a c), hJ_swap0 (F.zw c), F.ww]

def crd (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w : Fin k → Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ) :=
  (LinearMap.pi fun a => hJL ε (p a)).prod ((LinearMap.pi fun a => hJL ε (e a)).prod
    ((hJL ε z).prod (LinearMap.pi fun j => hJL ε (w j))))

theorem crd_syn (F : Frm ε e p z w T) α β γ δ :
    crd (ε := ε) e p z w (syn e p z w T α β γ δ) = (α, β, γ, δ) := by
  ext c
  · exact syn_p F c α β γ δ
  · exact syn_e F c α β γ δ
  · exact synthesized_vector_z_pairing F α β γ δ
  · exact syn_w F c α β γ δ

theorem recon (F : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) (v : Fin n → ℂ) :
    v = syn e p z w T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  have hsurj : Function.Surjective (crd (ε := ε) e p z w) := fun c =>
    ⟨syn e p z w T c.1 c.2.1 c.2.2.1 c.2.2.2, crd_syn F _ _ _ _⟩
  have hfin : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ ((Fin r → ℂ) × (Fin r → ℂ) × ℂ × (Fin k → ℂ)) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj
  apply hinj
  rw [crd_syn F]
  rfl

end Coord

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
