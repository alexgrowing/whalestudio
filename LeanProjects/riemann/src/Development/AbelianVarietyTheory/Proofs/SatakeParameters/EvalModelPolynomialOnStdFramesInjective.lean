import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IsUnitDetBlockPreimage
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem eq_zero_of_ev1_eq_zero_on_frames : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ), (∀ f : Fr1 D n, ev1 X D pos i h R f = 0) → R = 0 := by
  intro p _ X D pos i n h R hR
  refine Formalism.L2.G.evC_inj (X.Pj i) h (posJ X D pos i) (fun _ => 1) (fun _ => 1) (fun _ => by simp) R ?_
  funext f
  exact hR f

end GlobalTheory.TwV.DelA
