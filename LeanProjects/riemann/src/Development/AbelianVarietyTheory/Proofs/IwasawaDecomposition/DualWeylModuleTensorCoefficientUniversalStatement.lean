import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylModule_tensor_coefficient_universal : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : Type) [AddCommGroup V] [Module ℂ V] (F : MultilinearMap ℂ (fun v => nablaSq ℂ n (lam v)) V), ∃! f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] V, ∀ u, f (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = F u := by
  first | exact @GlobalTheory.CoefIrred.vv_universal | exact GlobalTheory.CoefIrred.vv_universal | (intros; apply GlobalTheory.CoefIrred.vv_universal <;> assumption)
