import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryConjugateDual
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_unitary_conjugate_dual : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsAdmissible ρ → GlobalTheory.LGrp.IsUnitarisable ρ → ∃ φ : V →ₛₗ[starRingEnd ℂ] smoothPart ρ.dual, Function.Bijective φ ∧ ∀ g x, φ (ρ g x) = GlobalTheory.LGrp.smoothDual ρ g (φ x) := by
  first | exact @GlobalTheory.SmoothRiesz.exists_conj_smoothDual | exact GlobalTheory.SmoothRiesz.exists_conj_smoothDual | (intros; apply GlobalTheory.SmoothRiesz.exists_conj_smoothDual <;> assumption)
