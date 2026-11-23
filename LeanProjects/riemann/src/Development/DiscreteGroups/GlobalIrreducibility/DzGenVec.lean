import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzGenDefs
import Development.DiscreteGroups.GlobalIrreducibility.DzGenMat
import Development.DiscreteGroups.GlobalIrreducibility.ValuationUnitriLt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

@[simp] theorem blk_eOne (i : Fin m) : blk (eOne m) i = i := rfl

@[simp] theorem eOne_mk (a : Fin m) (i : Fin 1) : eOne m ⟨a, i⟩ = a := rfl

def dl (p : parab k (eOne m)) : ℂˣ := deltaHalf k (fun _ : Fin m => Fin 1) (leviProj k (eOne m) p)

theorem dl_mul (p q : parab k (eOne m)) : dl (p * q) = dl p * dl q := by
  simp [dl, map_mul]

theorem dl_one : dl (1 : parab k (eOne m)) = 1 := by simp [dl]

theorem dl_eq_one {q : parab k (eOne m)} (hq : ∀ a, valuation k (((q : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1) :
    dl q = 1 := by
  rw [dl, deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => Units.ext ?_
  rw [val_absPow, Units.val_one]
  have hd : ((GeneralLinearGroup.det (leviProj k (eOne m) q a) : kˣ) : k) =
      ((q : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a := by
    simp only [GeneralLinearGroup.val_det_apply, det_unique]
    rfl
  rw [nabs_eq_one k (by rw [hd]; exact hq a)]
  simp

variable (S : Subgroup (GL (Fin m) k))

def InCell (g : GL (Fin m) k) : Prop := ∃ p : parab k (eOne m), ∃ y ∈ S, g = (p : GL (Fin m) k) * wRev k m * y

open Classical in

def cellFun (g : GL (Fin m) k) : ℂ := if h : InCell S g then (dl h.choose : ℂ) else 0

variable {S}

theorem cellFun_eq (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)
    (p : parab k (eOne m)) {y : GL (Fin m) k} (hy : y ∈ S) :
    cellFun S ((p : GL (Fin m) k) * wRev k m * y) = dl p := by
  have h : InCell S ((p : GL (Fin m) k) * wRev k m * y) := ⟨p, y, hy, rfl⟩
  rw [cellFun, dif_pos h]
  obtain ⟨y', hy', e⟩ := h.choose_spec
  set p' := h.choose
  let q : parab k (eOne m) := p'⁻¹ * p
  have hq : ((q : GL (Fin m) k)) = wRev k m * (y' * y⁻¹) * (wRev k m)⁻¹ := by
    have e2 : (p : GL (Fin m) k) = p' * (wRev k m * (y' * y⁻¹) * (wRev k m)⁻¹) :=
      calc (p : GL (Fin m) k) = p * wRev k m * y * y⁻¹ * (wRev k m)⁻¹ := by group
        _ = p' * wRev k m * y' * y⁻¹ * (wRev k m)⁻¹ := by rw [e]
        _ = p' * (wRev k m * (y' * y⁻¹) * (wRev k m)⁻¹) := by group
    simp only [q, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2]
    group
  have hs : y' * y⁻¹ ∈ S := S.mul_mem hy' (S.inv_mem hy)
  have h1 : dl q = 1 := dl_eq_one fun a => by
    rw [hq, wRev_inv, wRev_conj_apply]
    exact hS4 _ hs _
  have : p = p' * q := by simp [q]
  rw [this, dl_mul, h1, mul_one]

end DiscreteGroups.sglob.DzType
