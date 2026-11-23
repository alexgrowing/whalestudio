import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LabelDegreeCommensurableBound
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.labelled_degree_commensurable_bound : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ) (F : Submodule (𝓞 L) V) (𝔞 : Ideal (𝓞 L)), A.IsAdapted s v q → 𝔞 ≠ ⊥ → 𝔞 • F ≤ A.eig s → 𝔞 • A.eig s ≤ F → |A.labDeg s F v q - A.labDeg s (A.eig s) v q| ≤ (r + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L := by
  first | exact @LevelTowerAlt.label_degree_commensurable_bound | exact LevelTowerAlt.label_degree_commensurable_bound
