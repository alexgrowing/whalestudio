import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemilinearEquivPreservesProperties
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_equiv_preserves_properties : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W) (φ : V →ₛₗ[starRingEnd ℂ] W), Function.Bijective φ → (∀ g x, φ (ρ g x) = ρ' g (φ x)) → (ρ.IsIrreducible → ρ'.IsIrreducible) ∧ (IsAdmissible ρ → IsAdmissible ρ') ∧ (GlobalTheory.LGrp.IsUnitarisable ρ → GlobalTheory.LGrp.IsUnitarisable ρ') ∧ (GlobalTheory.LGrp.IsSpherical ρ K → GlobalTheory.LGrp.IsSpherical ρ' K) := by
  first | exact @GlobalTheory.ConjRep.conj_transfer | exact GlobalTheory.ConjRep.conj_transfer | (intros; apply GlobalTheory.ConjRep.conj_transfer <;> assumption)
