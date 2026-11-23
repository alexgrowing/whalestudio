import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicModularFormsIrreducibleDecomposition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicModularForms_irreducible_decomposition : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j), ∃ (ι : Type) (_ : Finite ι) (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), (∀ P, NG.IsIrrRep Mr.wt.ρ (F P)) ∧ (∀ P P', NG.IsoRep (F P) (F P') → P = P') ∧ (∀ S', NG.IsIrrRep Mr.wt.ρ S' → (NG.isoTyp Mr.wt.ρ S').comap Mr.real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') ∧ (∀ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real ≠ ⊥) ∧ iSupIndep (fun P => (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real) ∧ ⨆ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real = ⊤ := by
  first | exact @GlobalTheory.AutReps.mtReal_decomp | exact GlobalTheory.AutReps.mtReal_decomp | (intros; apply GlobalTheory.AutReps.mtReal_decomp <;> assumption)
