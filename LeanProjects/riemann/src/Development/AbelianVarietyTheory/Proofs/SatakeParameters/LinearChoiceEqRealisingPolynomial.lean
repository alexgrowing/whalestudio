import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjectiveStatement
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem phiC_eq_of_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Realises X D pos i h a Q R → phiC X D pos i h a Q = R := by
  intro p _ X D pos i n h a Q R hR
  have hmem : Q ∈ (relPhi X D pos i h a).map (LinearMap.fst ℂ _ _) :=
    Submodule.mem_map.2 ⟨(Q, R), hR, rfl⟩
  have hsel : Realises X D pos i h a Q (phiC X D pos i h a Q) := selOf_mem (relPhi X D pos i h a) Q hmem
  have hz : phiC X D pos i h a Q - R = 0 := by
    apply GlobalTheory.T.evalModelPolynomialOnStdFrames_injective X D pos i h
    intro f
    rw [map_sub, Pi.sub_apply, hsel f, hR f, sub_self]
  exact sub_eq_zero.1 hz

end GlobalTheory.TwV.DelA
