import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealisationDefiniteRealPointFockVectorAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_definite_realPoint_fockVector_action : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (j : Fin D.R.m) (t : T0) (B : Base (Vc D j) (Wc D j)), R.IsThP → B.Good → B.F.ψ = R.ψ → B.F.θ = R.θ → B.F.sT = cart (R.MW j (sg0 D A)) → (∀ τ, (B.F.BS τ).val = R.BV j τ) → B.F.BT = onb (R.MW j (sg0 D A)) → B.eta = R.eta → (∀ τ, HasInfExp D (R.toLevCh.mu t ((j : ℕ) + 1)) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2)) → ∀ u ∈ GinfC (Vc D j), ∀ P, R.ωP j t (u, 1) (R.ptP j t P) = R.ptP j t (B.act u P) := by
  first | exact @GlobalTheory.RealFockActionP.om_fock_vP | exact GlobalTheory.RealFockActionP.om_fock_vP | (intros; apply GlobalTheory.RealFockActionP.om_fock_vP <;> assumption)
