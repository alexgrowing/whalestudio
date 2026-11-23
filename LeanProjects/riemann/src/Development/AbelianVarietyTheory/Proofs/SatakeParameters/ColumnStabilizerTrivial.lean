import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ConjugacyRepresentativeSystems

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.ConjugacyRepresentativeSystems

noncomputable section

namespace GlobalTheory.Proof.ColumnStabilizerTrivial

section Concrete

variable {E : Type} [Field E] [NumberField E]

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

end GlobalTheory.Proof.ColumnStabilizerTrivial
