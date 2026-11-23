import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AntiLevWittJ

noncomputable section

namespace PI.IwaMeasEx.PD

open Matrix NumberField Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
open scoped TensorProduct

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {ι : Type} [Fintype ι] [DecidableEq ι]
  (lev : ι → ℕ) {T : Matrix ι ι R}

end Maps

section Pt

variable {I : AutInst}

theorem sigR_inclE (x : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) x) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star x) := by
  show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) (x ⊗ₜ[I.F] (1 : Af I.F)) = star x ⊗ₜ[I.F] (1 : Af I.F)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem cT_map (M : Matrix (Fin I.n) (Fin I.n) I.E) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (M.map (Formalism.UG.inclE (F := I.F) (Af I.F))) =
      Mᴴ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  ext i j
  simp only [Formalism.UG.cT, transpose_apply, map_apply, conjTranspose_apply]
  exact sigR_inclE (M j i)

def ptF (h : GL (Fin I.n) I.E) (hh : (h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * h = I.J) : I.Gf :=
  ⟨Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom h, by
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) ((h : Matrix (Fin I.n) (Fin I.n) I.E).map
        (Formalism.UG.inclE (F := I.F) (Af I.F))) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        (h : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) =
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [cT_map, ← Matrix.map_mul, ← Matrix.map_mul, hh]⟩

theorem semiconj_phi (v : InfinitePlace I.F) : Function.Semiconj (I.φ v) star star := fun a => by
  rw [I.cm.cmUnram.2.1 (I.φ v) a]
  rfl

def ptV (h : GL (Fin I.n) I.E) (hh : (h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * h = I.J)
    (v : InfinitePlace I.F) : Formalism.REAL.UJ (I.ε v) :=
  ⟨⟨(I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v,
    (I.P v)⁻¹ * ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v, by
      calc (I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v *
            ((I.P v)⁻¹ * ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
          = (I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * (I.P v * (I.P v)⁻¹) *
            ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [rrg_P_mul_inv, Matrix.mul_one, Matrix.mul_assoc (I.P v)⁻¹, ← Matrix.map_mul, ← Units.val_mul,
              mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, rrg_P_inv_mul], by
      calc (I.P v)⁻¹ * ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v *
            ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
          = (I.P v)⁻¹ * ((h⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * (I.P v * (I.P v)⁻¹) *
            (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [rrg_P_mul_inv, Matrix.mul_one, Matrix.mul_assoc (I.P v)⁻¹, ← Matrix.map_mul, ← Units.val_mul,
              inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, rrg_P_inv_mul]⟩, by
    show ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ * Formalism.REAL.Jm (I.ε v) *
      ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) = Formalism.REAL.Jm (I.ε v)
    have hJm : Formalism.REAL.Jm (I.ε v) = (I.P v)ᴴ * I.J.map (I.φ v) * I.P v := (I.P_spec v).symm
    have hc : ((h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ =
        ((h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ).map (I.φ v) := (conjTranspose_map _ (semiconj_phi v)).symm
    have e1 : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
      rw [← conjTranspose_mul, rrg_P_mul_inv, conjTranspose_one]
    calc ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ * Formalism.REAL.Jm (I.ε v) *
          ((I.P v)⁻¹ * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
        = (I.P v)ᴴ * ((h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * (((I.P v)⁻¹)ᴴ * (I.P v)ᴴ) *
            I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) * (h : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
          rw [hJm]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (I.P v)ᴴ * (((h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * h).map (I.φ v)) * I.P v := by
          rw [e1, rrg_P_mul_inv, hc]; simp only [Matrix.map_mul, Matrix.mul_one, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (I.ε v) := by rw [hh, hJm]⟩

def ptOf (h : GL (Fin I.n) I.E) (hh : (h : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * h = I.J) : I.GA :=
  (fun v => ptV h hh v, ptF h hh)

end Pt

section Dec

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)

def glOf (A Ai : Matrix (WIdx J (nz I J)) (WIdx J (nz I J)) I.E) (h1 : A * Ai = 1) (h2 : Ai * A = 1) :
    GL (Fin I.n) I.E :=
  ⟨unwc Fr A, unwc Fr Ai, by rw [unwc_mul, h1, unwc_one], by rw [unwc_mul, h2, unwc_one]⟩

end Dec

end PI.IwaMeasEx.PD

namespace PI.IwaMeasEx.Sk

open Formalism.L2.S.S7.DensDefs PI.IwaMeasEx.PD

end PI.IwaMeasEx.Sk

end
