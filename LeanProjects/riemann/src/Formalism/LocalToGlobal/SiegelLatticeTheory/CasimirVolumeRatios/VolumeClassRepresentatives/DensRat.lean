import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.DensDefs
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

namespace Formalism.L2.S.S7.DensRat

open NumberField
open scoped Matrix
open Formalism.MainNotions.S Formalism.L2.S.S7.DensDefs

def ratReal (I : AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨⟨(I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    by
      have e1 : (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
          ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
        rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      calc (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v *
            ((I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
          = (I.P v)⁻¹ * ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * (I.P v * (I.P v)⁻¹) *
            ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one, e1, Matrix.mul_one,
              Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul],
    by
      have e1 : ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
        rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      calc (I.P v)⁻¹ * ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v *
            ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
          = (I.P v)⁻¹ * (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) *
            (I.P v * (I.P v)⁻¹) * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one, e1, Matrix.mul_one,
              Formalism.MainNotions.LeviCoordinates.rrg_P_inv_mul]⟩,
  by
    have hγ' : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
    have hc : (Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map (I.φ v) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        starRingEnd_apply]
      exact I.cm.cmUnram.2.1 (I.φ v) _
    have hu : ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
      rw [← hc, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
    have hPP : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.conjTranspose_one]
    show ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ *
        Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) =
        Formalism.REAL.Jm (I.ε v)
    rw [← I.P_spec v]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((I.P v)⁻¹)ᴴ (I.P v)ᴴ, hPP, Matrix.one_mul,
      ← Matrix.mul_assoc (I.P v) (I.P v)⁻¹, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mul]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [hu]⟩

theorem ratPoint_holds (I : AutInst) : RatPoint I := by
  intro g hg
  have hf : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) g ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    Formalism.UG.Final.RatPtsLe I.F I.E (Fin I.n) I.cm.sig I.J (Af I.F) (Subgroup.mem_map_of_mem _ hg)
  let x : I.GA := (fun v => ratReal I g hg v, ⟨_, hf⟩)
  have hx : x ∈ I.GFset := ⟨g, hg, fun v => rfl, rfl⟩
  exact ⟨x, hx, ratM_eq I hx g rfl⟩

end Formalism.L2.S.S7.DensRat

end
