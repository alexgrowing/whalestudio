import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselCharacter_generic_character_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ d : BesDat A B ι, (∀ n n' : NFlag B d.e, besChar ψ d ((n * n' : NFlag B d.e) : GA D B) = besChar ψ d (n : GA D B) * besChar ψ d (n' : GA D B)) ∧ (∀ γ ∈ NFlagQ B d.e, besChar ψ d (γ : GA D B) = 1) ∧ (Continuous fun n : NFlag B d.e => besChar ψ d (n : GA D B)) ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ NFlag B d.e, g * n * g⁻¹ ∈ NFlag B d.e ∧ besChar ψ d (g * n * g⁻¹) = besChar ψ d n := by
  first | exact @GlobalTheory.BesselChar.besChar_laws | exact GlobalTheory.BesselChar.besChar_laws | (intros; apply GlobalTheory.BesselChar.besChar_laws <;> assumption)
