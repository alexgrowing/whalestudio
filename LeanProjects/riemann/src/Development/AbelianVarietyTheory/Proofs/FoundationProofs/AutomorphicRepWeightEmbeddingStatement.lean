import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepWeightEmbedding
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_rep_weight_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n), Function.Injective (fun τ => InfinitePlace.mk (σ τ)) → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ)), f ≠ 0 → (∀ v, f v ∈ π) → (∀ (x : infU E n) v, f (((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype)) x v) = RU E n x (f v)) → ∀ τ, HasWeightAt π (σ τ) (lam τ) ∧ HasWeightAt π (ComplexEmbedding.conjugate (σ τ)) (lam τ).dual := by
  first | exact @GlobalTheory.DefU.EquivWt.hasWeightAt_of_equivariant | exact GlobalTheory.DefU.EquivWt.hasWeightAt_of_equivariant | (intros; apply GlobalTheory.DefU.EquivWt.hasWeightAt_of_equivariant <;> assumption)
