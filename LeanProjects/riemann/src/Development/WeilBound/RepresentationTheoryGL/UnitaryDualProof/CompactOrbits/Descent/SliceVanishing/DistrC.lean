import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ExistsQuotientHomeo
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.NilpotentPowers.IsNilpotentPowSub
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FiberLocalization.EqZeroOfFiberEquivariant
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FiberLocalization.EqZeroOfFiberEquivariantSB

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.PfBern.Loc

variable {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S] [TotallyDisconnectedSpace S]

theorem exists_distr_on (ξ : (S → ℂ) →ₗ[ℂ] ℂ) {C : Set S} (hC : IsClosed C)
    (hξ : ∀ f ∈ supportedIn (Set.univ : Set S), (∀ p ∈ C, f p = 0) → ξ f = 0) :
    ∃ D : Distr C, ∀ f : SC S, ξ f = D (restr hC f) := by
  let ξ' : SC S →ₗ[ℂ] ℂ := ξ ∘ₗ (SC S).subtype
  have hker : LinearMap.ker (restr hC) ≤ LinearMap.ker ξ' := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply hξ
    · exact ⟨f.2, Set.subset_univ _⟩
    · intro p hp
      have h0 := congrArg (fun g : SC C => (g : C → ℂ) ⟨p, hp⟩) hf
      simpa [restr] using h0
  let D0 : LinearMap.range (restr hC) →ₗ[ℂ] ℂ :=
    (LinearMap.ker (restr hC)).liftQ ξ' hker ∘ₗ (restr hC).quotKerEquivRange.symm.toLinearMap
  obtain ⟨r, hr⟩ := (LinearMap.range (restr hC)).subtype.exists_leftInverse_of_injective
    (LinearMap.range (restr hC)).ker_subtype
  refine ⟨D0 ∘ₗ r, fun f => ?_⟩
  have h1 : r (restr hC f) = ⟨restr hC f, LinearMap.mem_range_self _ f⟩ :=
    LinearMap.congr_fun hr ⟨_, _⟩
  rw [LinearMap.comp_apply, h1]
  simp only [D0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.liftQ_apply]
  rfl

theorem exists_functional {C : Set S} (hC : IsClosed C) (E : Distr C) :
    ∃ η : (S → ℂ) →ₗ[ℂ] ℂ, ∀ f : SC S, η f = E (restr hC f) := by
  obtain ⟨r, hr⟩ := (SC S).subtype.exists_leftInverse_of_injective (SC S).ker_subtype
  refine ⟨E ∘ₗ restr hC ∘ₗ r, fun f => ?_⟩
  have h1 : r (f : S → ℂ) = f := LinearMap.congr_fun hr f
  simp only [LinearMap.comp_apply, h1]

end PositivityTheory.RgUd.T.Desc.SLF
