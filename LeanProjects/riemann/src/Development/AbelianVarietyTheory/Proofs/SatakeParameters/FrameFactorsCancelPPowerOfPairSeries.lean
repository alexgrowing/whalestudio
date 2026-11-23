import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem eFac_mul_pPow : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv) (g : GL3Theta.G1 p) (hLT : LTIso g) (T : Type) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), E.iK ((pendT X E hfin hst hLT pos F).eS j La * ((pendT X E hfin hst hLT pos F).eT j La')⁻¹) * pPow X j La La' = 1 := by
  intro p _ X _ E hfin hst g hLT T pos F j La La'
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  show E.iK (Pend.eS _ j La * (Pend.eT _ j La')⁻¹) * pPow X j La La' = 1
  simp only [Pend.eS, Pend.eT]
  rw [pPow_eq_prod]
  rw [map_mul, map_inv₀, map_prod, map_prod]
  simp only [map_zpow₀, map_natCast]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun v _ => ?_)
  rw [← zpow_neg, ← zpow_add₀ hp, ← zpow_add₀ hp]
  show (p : ℂ_[p]) ^ _ = 1
  ring_nf
  simp

end GlobalTheory.TwV.DelB
