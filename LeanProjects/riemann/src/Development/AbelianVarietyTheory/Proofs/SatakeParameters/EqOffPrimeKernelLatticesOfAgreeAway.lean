import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeEqAwayFromPrimeOfAgreeOffPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsAgreeAwayOfLatticeTuplesAgreeAwayStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

namespace GlobalTheory.TwV.Xc

theorem eqOffPrime_of_heq_lattices_rank_eq {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {n m : ℕ} (h : n = m)
    {A B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {A' B' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    (ha : HEq A A') (hb : HEq B B') (h' : GL3Theta.EqOff D P A' B') : GL3Theta.EqOff D P A B := by
  subst h
  cases ha
  cases hb
  exact h'

theorem eqOff_kerN_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf (D.what₂.places.resChar w) ((sysS H X std).G.P.W v) (J.rho std v) P → ∀ j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → GL3Theta.EqOff D P ((J.fd std).kerN j La) ((J.fd std).kerN j Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSpl v P hP j hj La Lb hSA
  have hLa := hSA.1
  have hLb := hSA.2.1
  have h1 := hSA.2.2.1
  have hch : J.chart std j hj La = J.chart std j hj Lb := by
    obtain ⟨c, A⟩ := La
    obtain ⟨c', B⟩ := Lb
    simp only at h1
    subst h1
    exact GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hSpl j hj c A B hLa hLb
  have hoff := (GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v j hj La Lb hSA).1
  obtain ⟨⟨hr, -⟩, -, hKa, -⟩ := hD j hj La hLa
  obtain ⟨-, -, hKb, -⟩ := hD j hj Lb hLb
  rw [← hch] at hKb
  have key := GlobalTheory.T.kernelLattice_eq_away_from_prime_of_agree_off_place D (D.R.N 0) (D.what₂.places.resChar w) (D.gat u w hg) (A0 J) J.one.int hSpl.1 v P hP (D.R.N j)
    (gramN D j hj) J.a ((J.St j hj).K (J.chart std j hj La)).lev.Lb ((J.St j hj).K (J.chart std j hj La)).lev.Lb_fin
    ((J.St j hj).K (J.chart std j hj La)).lev.Lb_span (J.pt std j hj La).1 (J.pt std j hj Lb).1 hoff
  exact eqOffPrime_of_heq_lattices_rank_eq hr hKa hKb key

end GlobalTheory.TwV.Xc
