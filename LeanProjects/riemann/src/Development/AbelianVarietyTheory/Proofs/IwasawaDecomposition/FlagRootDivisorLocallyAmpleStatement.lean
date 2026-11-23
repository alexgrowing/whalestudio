import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorLocallyAmple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_root_divisor_locally_ample : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (μ : Fin N → ℤ), StrictAnti μ → ∀ z : gen s.T.Z, ∃ V : (gen s.T.Z).Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB (((Φ.C k).Y.lb (-∑ x : DV.Rt D.what₂.Tau N, μ x.2 • divOf (Φ.C k) (rootEx S.Dw (DV.tauEmb D x.1) x.2))).pull ((Φ.C k).π ⁻¹ᵁ V).ι) := by
  first | exact @GlobalTheory.FlagAmple.isAmpleLB_rootEx | exact GlobalTheory.FlagAmple.isAmpleLB_rootEx | (intros; apply GlobalTheory.FlagAmple.isAmpleLB_rootEx <;> assumption)
