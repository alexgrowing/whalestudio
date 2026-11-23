import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFacts
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → (per A N N').FG ∧ (∀ x : HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ per A N N') ∧ (∀ r : 𝓞 X.E, r ≠ 0 → (smulLat (r : X.E) (per A N N')).toAddSubgroup.relIndex (per A N N').toAddSubgroup ≠ 0) ∧ ∀ P : HeightOneSpectrum (𝓞 X.E), localization₂ P.asIdeal A.AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : HomE X.E a b, y ∈ localization₂ P.asIdeal (per A N N') ↔ ∀ v ∈ localization₂ P.asIdeal N, y v ∈ localization₂ P.asIdeal N' := by
  first | exact @GlobalTheory.MomT.LatFin.per_lattice_facts | exact GlobalTheory.MomT.LatFin.per_lattice_facts | (intros; apply GlobalTheory.MomT.LatFin.per_lattice_facts <;> assumption)
