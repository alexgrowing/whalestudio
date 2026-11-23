import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassProdEqMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitStabilizerMass_prod_eq_mul : ∀ (Γ G G' α β : Type) [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β] [MulAction Γ (α × β)] (φ : Γ ≃* G × G') (X : Set α) (Y : Set β), (∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2)) → Stable G X → Stable G' Y → (∀ x ∈ X, Finite (MulAction.stabilizer G x)) → (∀ y ∈ Y, Finite (MulAction.stabilizer G' y)) → orbMass Γ (X ×ˢ Y) = orbMass G X * orbMass G' Y := by
  first | exact @GlobalTheory.Mass.ProdMass.orbMass_prod | exact GlobalTheory.Mass.ProdMass.orbMass_prod | (intros; apply GlobalTheory.Mass.ProdMass.orbMass_prod <;> assumption)
