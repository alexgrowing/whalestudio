import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E), L.FG → (∀ τ, GL3Columns.BasR D lam τ L ((P τ).map (tauEmb D lam τ))) → (∀ τ τ', Formalism.L2.Ker.ConjPr lam τ τ' → P τ' = Formalism.L2.Ker.dualM (P τ)) → StdBases D lam L P := by
  first | exact @GlobalTheory.KerStd.stdBases_of_basR | exact GlobalTheory.KerStd.stdBases_of_basR | (intros; apply GlobalTheory.KerStd.stdBases_of_basR <;> assumption)
