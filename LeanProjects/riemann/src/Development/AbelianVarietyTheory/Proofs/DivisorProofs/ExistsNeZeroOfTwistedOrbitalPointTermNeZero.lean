import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

theorem exists_ne_zero_of_twTerm_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (δ : G) (f : G → ℂ) (y : G) (h : GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0) :
    ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  have hu : (fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))) = fun _ => 0 := by
    funext k
    exact hc k k.2
  unfold GlobalTheory.EulerAbs.twTerm
  rw [hu]
  simp [GlobalTheory.BCT.avg]

end GlobalTheory.EulerAbs
