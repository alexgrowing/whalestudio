import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalSetMeasureRealSUStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamental_set_measure_realSU_stabilizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Γ : Subgroup (GL (Fin r) E)) (ν : Measure (realSU Ψ G)) [ν.IsMulLeftInvariant], (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → (∀ γ ∈ Γ, IsUStab G Λ γ) → ∃ S : Set (realSU Ψ G), MeasurableSet S ∧ ν S = covolume (inReal Ψ G Γ) (realSU Ψ G) ν ∧ ∀ s : realSU Ψ G, ∃ δ ∈ Γ, ∃ hδ : embGL Ψ r δ ∈ realSU Ψ G, (⟨embGL Ψ r δ, hδ⟩ : realSU Ψ G) * s ∈ S := by
  first | exact @GlobalTheory.CovTop.VolUp.exists_measurableSet_reps_covolume | exact GlobalTheory.CovTop.VolUp.exists_measurableSet_reps_covolume | (intros; apply GlobalTheory.CovTop.VolUp.exists_measurableSet_reps_covolume <;> assumption)
