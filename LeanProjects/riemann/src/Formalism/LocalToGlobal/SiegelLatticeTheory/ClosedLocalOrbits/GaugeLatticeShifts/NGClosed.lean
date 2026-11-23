import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SynthesizedVectorZPairing
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightInvOfModular

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem uMat_inv_mul (g : UJ ε) : Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  show (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
  rw [Subgroup.coe_inv, Units.inv_mul]

theorem uMat_mul_inv (g : UJ ε) : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  show _ * (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [Subgroup.coe_inv, Units.mul_inv]

theorem uMat_mul (g h : UJ ε) : Formalism.MainNotions.S.uMat (g * h) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat h := rfl

theorem inv_fix {g : UJ ε} {v : Fin n → ℂ} (h : Formalism.MainNotions.S.uMat g *ᵥ v = v) : Formalism.MainNotions.S.uMat g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [mulVec_mulVec, uMat_inv_mul, one_mulVec]

theorem fix_span {g : Matrix (Fin n) (Fin n) ℂ} (hg : ∀ a, g *ᵥ e a = e a) (a : ℕ) :
    ∀ x ∈ spanLt e a, g *ᵥ x = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, _, rfl⟩ := hy
    exact hg b
  | zero => exact mulVec_zero _
  | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
  | smul c x _ hx => rw [mulVec_smul, hx]

theorem InN_one : InN ε e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨UnitaryIsometries.RI.inS_one e z, fun y _ => by rw [sub_self, zero_mulVec]; exact Submodule.zero_mem _⟩

theorem InN_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InN ε e z g) (hh : InN ε e z h) : InN ε e z (g * h) := by
  refine ⟨UnitaryIsometries.RI.inS_mul e z hg.1 hh.1, fun y hy => ?_⟩
  have key : (g * h - 1) *ᵥ y = g *ᵥ ((h - 1) *ᵥ y) + (g - 1) *ᵥ y := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  rw [key]
  exact Submodule.add_mem _ (UnitaryIsometries.RI.inS_pres e z hg.1 r _ (hh.2 y hy)) (hg.2 y hy)

def NG : Subgroup (UJ ε) where
  carrier := NLoc ε e z
  one_mem' := InN_one ε e z
  mul_mem' {g h} hg hh := InN_mul ε e z hg hh
  inv_mem' {g} hg := by
    have hS : g⁻¹ ∈ UnitaryIsometries.RI.SG ε e z := (UnitaryIsometries.RI.SG ε e z).inv_mem hg.1
    refine ⟨hS, fun y hy => ?_⟩
    have key : (Formalism.MainNotions.S.uMat g⁻¹ - 1) *ᵥ y = -(Formalism.MainNotions.S.uMat g⁻¹ *ᵥ ((Formalism.MainNotions.S.uMat g - 1) *ᵥ y)) := by
      rw [mulVec_mulVec, Matrix.mul_sub, uMat_inv_mul, Matrix.mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec]
      abel
    rw [key]
    exact Submodule.neg_mem _ (UnitaryIsometries.RI.inS_pres e z hS r _ (hg.2 y hy))

def HG : Subgroup (UJ ε) where
  carrier := HLoc ε e p z
  one_mem' := ⟨fun a => one_mulVec _, fun a => one_mulVec _, one_mulVec _⟩
  mul_mem' {g h} hg hh := ⟨fun a => by rw [uMat_mul, ← mulVec_mulVec, hh.1 a, hg.1 a],
    fun a => by rw [uMat_mul, ← mulVec_mulVec, hh.2.1 a, hg.2.1 a],
    by rw [uMat_mul, ← mulVec_mulVec, hh.2.2, hg.2.2]⟩
  inv_mem' {g} hg := ⟨fun a => inv_fix ε (hg.1 a), fun a => inv_fix ε (hg.2.1 a), inv_fix ε hg.2.2⟩

theorem coe_NG : (NG ε e z : Set (UJ ε)) = NLoc ε e z := rfl

theorem coe_HG : (HG ε e p z : Set (UJ ε)) = HLoc ε e p z := rfl

theorem NG_closed : IsClosed (NG ε e z : Set (UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ v) := fun v =>
    ((UnitaryIsometries.RI.continuous_uMat ε).sub continuous_const).matrix_mulVec continuous_const
  have e1 : (NG ε e z : Set (UJ ε)) = (UnitaryIsometries.RI.SG ε e z : Set (UJ ε)) ∩
      ⋂ y ∈ {y : Fin n → ℂ | ∀ a, hJ ε (e a) y = 0},
        (fun g : UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ y) ⁻¹' (spanLt e r : Set (Fin n → ℂ)) := by
    ext g
    simp only [coe_NG, NLoc, InN, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
    rfl
  rw [e1]
  exact (UnitaryIsometries.RI.SG_closed ε e z).inter (isClosed_biInter fun y _ =>
    (Submodule.closed_of_finiteDimensional _).preimage (hc y))

theorem HG_closed : IsClosed (HG ε e p z : Set (UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : UJ ε => Formalism.MainNotions.S.uMat g *ᵥ v) := fun v =>
    (UnitaryIsometries.RI.continuous_uMat ε).matrix_mulVec continuous_const
  have e1 : (HG ε e p z : Set (UJ ε)) = (⋂ a, {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ e a = e a}) ∩
      ((⋂ a, {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ p a = p a}) ∩ {g : UJ ε | Formalism.MainNotions.S.uMat g *ᵥ z = z}) := by
    ext g
    simp only [coe_HG, HLoc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e1]
  exact (isClosed_iInter fun a => isClosed_eq (hc _) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_eq (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const))

theorem NG_le_SG : NG ε e z ≤ UnitaryIsometries.RI.SG ε e z := fun _ hg => hg.1

theorem HG_le_SG : HG ε e p z ≤ UnitaryIsometries.RI.SG ε e z := by
  intro g hg
  refine ⟨fun a => ?_, ?_⟩
  · rw [Matrix.sub_mulVec, one_mulVec, hg.1 a, sub_self]
    exact Submodule.zero_mem _
  · rw [Matrix.sub_mulVec, one_mulVec, hg.2.2, sub_self]
    exact Submodule.zero_mem _

theorem conj_mem {h g : UJ ε} (hh : h ∈ HG ε e p z) (hg : g ∈ NG ε e z) : h * g * h⁻¹ ∈ NG ε e z := by
  have hfix : ∀ a, Formalism.MainNotions.S.uMat h *ᵥ e a = e a := hh.1
  have hfix' : ∀ a, Formalism.MainNotions.S.uMat h⁻¹ *ᵥ e a = e a := fun a => inv_fix ε (hh.1 a)
  have key : ∀ v, (Formalism.MainNotions.S.uMat (h * g * h⁻¹) - 1) *ᵥ v =
      Formalism.MainNotions.S.uMat h *ᵥ ((Formalism.MainNotions.S.uMat g - 1) *ᵥ (Formalism.MainNotions.S.uMat h⁻¹ *ᵥ v)) := by
    intro v
    rw [uMat_mul, uMat_mul, mulVec_mulVec, mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      uMat_mul_inv, Matrix.sub_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, hfix', fix_span e hfix a.1 _ (hg.1.1 a)]
    exact hg.1.1 a
  · rw [key, inv_fix ε hh.2.2, fix_span e hfix r _ hg.1.2]
    exact hg.1.2
  · have hy' : ∀ a, hJ ε (e a) (Formalism.MainNotions.S.uMat h⁻¹ *ᵥ y) = 0 := by
      intro a
      rw [← hfix' a, UnitaryIsometries.isIsom_uMat ε h⁻¹, hy a]
    rw [key, fix_span e hfix r _ (hg.2 _ hy')]
    exact hg.2 _ hy'

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
