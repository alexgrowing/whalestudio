import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellS
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealHermitianForms

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut

section Fwd

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem Qi_spanLt (hT : TrHyp F Qm Qim c) {a : ℕ} {v : Fin n → ℂ} (hv : v ∈ spanLt F.e a) :
    ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qim *ᵥ v) i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro i hi
    rw [Qi_e hT b]
    have hne : i ≠ Formalism.QuantumDeterminants.eI k r b := fun h => by
      have := congrArg Fin.val h; simp only [Formalism.QuantumDeterminants.eI] at this; simp only [Set.mem_setOf_eq] at hb; omega
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply, hne]
  | zero => intro i _; simp
  | add x y _ _ hx hy => intro i hi; rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
  | smul d x _ hx => intro i hi; rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero]

theorem e_perp_mid (hT : TrHyp F Qm Qim c) (a : Fin r) (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val)
    (hj2 : j.val ≤ r + k) : hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := by
  have he : F.e a = (c a)⁻¹ • (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) := by
    rw [hT.he, smul_smul, inv_mul_cancel₀ (c_ne hT a), one_smul]
  rw [he, PtRepPf.hJ_smul_left, ← herm_Q hT, Formalism.L2.SG.Pf.CarrierBase.herm_bvec]
  have h0 : (Formalism.QuantumDeterminants.Hpk k r *ᵥ Formalism.QuantumDeterminants.bvec j) (Formalism.QuantumDeterminants.eI k r a) = 0 := by
    simp only [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one, Matrix.col_apply]
    unfold Formalism.QuantumDeterminants.Hpk
    have ha := a.2
    have hv : (Formalism.QuantumDeterminants.eI k r a).val = a.val := rfl
    rw [if_neg (fun h => by have h' := h.2; rw [hv] at h'; omega),
      if_neg (fun h => by have h' := h.1; omega),
      if_neg (fun h => by have h' := h.1; rw [hv] at h'; omega)]
  rw [h0, mul_zero]

theorem fwd_N (hT : TrHyp F Qm Qim c) {g : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ}
    (hgU : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) (hg : InN ε F.e z g) :
    Qim * g * Qm ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hQQ : Qimᴴ * Qmᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hT.h2, Matrix.conjTranspose_one]
  have hcol : ∀ (j i : Fin (2 * r + k + 1)), (Qim * g * Qm) i j = (Qim *ᵥ (g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j))) i := by
    intro j i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]
  refine ⟨?_, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩
  · show (Qim * g * Qm)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qim * g * Qm) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hT.hH]
    calc (Qim * g * Qm)ᴴ * (Qmᴴ * Formalism.REAL.Jm ε * Qm) * (Qim * g * Qm)
        = Qmᴴ * gᴴ * (Qimᴴ * Qmᴴ) * Formalism.REAL.Jm ε * (Qm * Qim) * g * Qm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qmᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * Qm := by
          rw [hQQ, hT.h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hgU]
  · rw [hcol, hT.he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply]
    have hsplit : g *ᵥ F.e a = F.e a + (g - 1) *ᵥ F.e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.1.1 a) i hi, add_zero, Qi_e hT a,
      Pi.smul_apply, smul_smul, mul_inv_cancel₀ (c_ne hT a), one_smul]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]
  · rw [hcol]
    have hw : ∀ a, hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := fun a => e_perp_mid hT a j hj1 hj2
    have hsplit : g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = Qm *ᵥ Formalism.QuantumDeterminants.bvec j + (g - 1) *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.2 _ hw) i hi, add_zero, Matrix.mulVec_mulVec,
      hT.h1, Matrix.one_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]

end Fwd

end Formalism.L2.SG.Pf.Bridge
