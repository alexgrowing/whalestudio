import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeneralLinearTransitiveOnLatticesOverDVR
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by
  first | exact @GlobalTheory.LatHecke.gl_transitive_lattices | exact GlobalTheory.LatHecke.gl_transitive_lattices | (intros; apply GlobalTheory.LatHecke.gl_transitive_lattices <;> assumption)
