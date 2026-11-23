import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HModelAllOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImABwdEps

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

theorem psiV_sigA (X : HidaSetting D) (p : TypX X) (t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    PI.FinKW.psiV X.B.I p.1 (sigA X.B.I t) =
      sigR (Fv X.B.I.F p.1) X.B.I.cm.sig (PI.FinKW.psiV X.B.I p.1 t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp only [PI.FinKW.psiV, sigA, Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
      AlgEquiv.coe_algHom, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul, AlgHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem theta_eps_cases (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (hθ : IsSplitEquiv X p θ) : θ (epsP X p) = (1, 0) ∨ θ (epsP X p) = (0, 1) := by
  have hs := hθ (epsP X p)
  have h1 : sigR (FpX X p) X.B.I.cm.sig (epsP X p) = 1 - epsP X p := by
    rw [imA_eps'_eq]
    exact (psiV_sigA X p X.ew).symm
  rw [h1, map_sub, map_one] at hs
  have hi : θ (epsP X p) * θ (epsP X p) = θ (epsP X p) := by rw [← map_mul, imA_eps_idem]
  generalize θ (epsP X p) = q at hs hi ⊢
  obtain ⟨a, b⟩ := q
  have ha : 1 - a = b := congrArg Prod.fst hs
  have hb : a * a = a := congrArg Prod.fst hi
  have h0 : a * (a - 1) = 0 := by linear_combination hb
  rcases mul_eq_zero.mp h0 with h | h
  · right
    subst h
    rw [← ha]
    simp
  · left
    have : a = 1 := by linear_combination h
    subst this
    rw [← ha]
    simp

end PIW.MassDataColumns
