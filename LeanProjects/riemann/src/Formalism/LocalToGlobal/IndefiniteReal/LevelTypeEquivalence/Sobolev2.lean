import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobDer

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ} {ψ : AddChar (AF D.host.F) ℂ}

theorem psi_neg_mul (a : AF D.host.F) : ψ (-a) * ψ a = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem Gf_rat {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (L : (Fin k → ℝ) →+ WO S T)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (x : WO S T) :
    Gf ψ L f (ratW T S γ + x) = fun t => ψ (-(symplOH S T (ratW T S γ) x)) * Gf ψ L f x t := by
  funext t
  simp only [Gf, heisO]
  rw [add_assoc, hf.quasi γ (x + L t), symplOH_add_left, symplOH_add_right]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  abel

theorem Gf_fin {f : WO S T → ℂ} {L : (Fin k → ℝ) →+ WO S T} (hL : IsRealFrame L) (u : WO S T)
    (hu : eFin D • u = u) (hfu : heisO ψ S T u f = f) (x : WO S T) :
    Gf ψ L f (x + u) = fun t => ψ (-(symplOH S T x u)) * Gf ψ L f x t := by
  funext t
  have hr : eInf D • L t = L t := (wo_real_iff (L t)).mp (hL.2.1 t)
  have hfy : ∀ y, f (y + u) = ψ (-(symplOH S T y u)) * f y := by
    intro y
    have := congrFun hfu y
    simp only [heisO] at this
    rw [← this, ← mul_assoc, psi_neg_mul, one_mul]
  simp only [Gf, heisO]
  rw [show x + u + L t = (x + L t) + u by abel, hfy, symplOH_add_left, symplOH_add_left,
    symplOH_fin_real u (L t) hu hr, symplOH_real_fin (L t) u hr hu, add_zero, add_zero]
  ring

theorem dH_smul_const {f : WO S T → ℂ} {L : (Fin k → ℝ) →+ WO S T} {n : ℕ} (l : Fin n → Fin k) {x y : WO S T}
    (c : ℂ) (h : Gf ψ L f y = fun t => c * Gf ψ L f x t) (hs : ContDiff ℝ ∞ (Gf ψ L f x)) :
    dH ψ L l f y = c * dH ψ L l f x := by
  have e : dH ψ L l f y = iteratedFDeriv ℝ n (Gf ψ L f y) 0 (fun i => Pi.single (l i) 1) := rfl
  have e' : dH ψ L l f x = iteratedFDeriv ℝ n (Gf ψ L f x) 0 (fun i => Pi.single (l i) 1) := rfl
  rw [e, e', h]
  have h2 : (fun t => c * Gf ψ L f x t) = c • Gf ψ L f x := rfl
  have hs' : ContDiff ℝ n (Gf ψ L f x) := hs.of_le (natCast_lt_inf n).le
  rw [h2]
  first
    | (rw [iteratedFDeriv_const_smul_apply hs']; rfl)
    | (rw [iteratedFDeriv_const_smul_apply hs'.contDiffAt]; rfl)
    | (rw [iteratedFDeriv_const_smul_apply (hs.contDiffAt)]; rfl)

end Formalism.IndefR.Eqv

end
