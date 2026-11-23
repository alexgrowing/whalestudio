import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePartIntegralUnitOfUnitResidue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_integral_unit_of_unit_residue : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ k : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) k) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → ∀ (P : Pl D.host.E) (e : AE D), (∀ P' : Pl D.host.E, P' ≠ P → ι (finPart D e) P' = 0) → ∀ (x : (AE D)ˣ), (1 - e) * (x : AE D) = 1 - e → ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (v : (kP P)ˣ), resS D.host.F P ⟨_, hx⟩ = v → finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  first | exact @GlobalTheory.ExportSeries.finPart_mem_intAE_of_unit_residue | exact GlobalTheory.ExportSeries.finPart_mem_intAE_of_unit_residue | (intros; apply GlobalTheory.ExportSeries.finPart_mem_intAE_of_unit_residue <;> assumption)
