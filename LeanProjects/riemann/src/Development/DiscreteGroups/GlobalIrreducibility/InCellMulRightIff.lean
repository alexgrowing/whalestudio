import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzGenVec

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {S : Subgroup (GL (Fin m) k)}

theorem inCell_mul_left_iff (p₀ : parab k (eOne m)) (g : GL (Fin m) k) :
    InCell S ((p₀ : GL (Fin m) k) * g) ↔ InCell S g := by
  constructor
  · rintro ⟨p, y, hy, e⟩
    refine ⟨p₀⁻¹ * p, y, hy, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc g = (p₀ : GL (Fin m) k)⁻¹ * ((p₀ : GL (Fin m) k) * g) := by group
      _ = _ := by rw [e]; group
  · rintro ⟨p, y, hy, e⟩
    exact ⟨p₀ * p, y, hy, by rw [e]; simp only [Subgroup.coe_mul]; group⟩

theorem inCell_mul_right_iff {s : GL (Fin m) k} (hs : s ∈ S) (g : GL (Fin m) k) :
    InCell S (g * s) ↔ InCell S g := by
  constructor
  · rintro ⟨p, y, hy, e⟩
    refine ⟨p, y * s⁻¹, S.mul_mem hy (S.inv_mem hs), ?_⟩
    calc g = g * s * s⁻¹ := by group
      _ = _ := by rw [e]; group
  · rintro ⟨p, y, hy, e⟩
    exact ⟨p, y * s, S.mul_mem hy hs, by rw [e]; group⟩

variable (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)
include hS4

theorem cellFun_mul_left (p₀ : parab k (eOne m)) (g : GL (Fin m) k) :
    cellFun S ((p₀ : GL (Fin m) k) * g) = dl p₀ * cellFun S g := by
  by_cases h : InCell S g
  · obtain ⟨p, y, hy, rfl⟩ := h
    have e : (p₀ : GL (Fin m) k) * (p * wRev k m * y) = ((p₀ * p : parab k (eOne m)) : GL (Fin m) k) * wRev k m * y := by
      simp only [Subgroup.coe_mul]; group
    rw [e, cellFun_eq hS4 _ hy, cellFun_eq hS4 _ hy, dl_mul, Units.val_mul]
  · have h' : ¬ InCell S ((p₀ : GL (Fin m) k) * g) := fun h' => h ((inCell_mul_left_iff p₀ g).1 h')
    rw [cellFun, dif_neg h', cellFun, dif_neg h, mul_zero]

theorem cellFun_mul_right {s : GL (Fin m) k} (hs : s ∈ S) (g : GL (Fin m) k) :
    cellFun S (g * s) = cellFun S g := by
  by_cases h : InCell S g
  · obtain ⟨p, y, hy, rfl⟩ := h
    have e : (p : GL (Fin m) k) * wRev k m * y * s = p * wRev k m * (y * s) := by group
    rw [e, cellFun_eq hS4 _ (S.mul_mem hy hs), cellFun_eq hS4 _ hy]
  · rw [cellFun, dif_neg (fun h' => h ((inCell_mul_right_iff hs g).1 h')), cellFun, dif_neg h]

end DiscreteGroups.sglob.DzType
