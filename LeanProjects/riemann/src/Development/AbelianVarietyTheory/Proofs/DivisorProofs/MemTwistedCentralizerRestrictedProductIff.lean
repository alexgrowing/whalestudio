import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerAbs

theorem mem_twCent_iff_forall_comp : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → ∀ (δ x : X), x ∈ twCent θ δ ↔ ∀ v, pf v x ∈ twCent (θv v) (pf v δ) := by
  intro X V Y _ _ _ _ pf K hX θ θv hθ δ x
  simp only [twCent, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h v
    have := congrArg (pf v) h
    simpa [map_mul, hθ] using this
  · intro h
    apply hX.ext
    · intro w; exact isEmptyElim w
    · intro v
      simpa [map_mul, hθ] using h v

end GlobalTheory.EulerAbs
