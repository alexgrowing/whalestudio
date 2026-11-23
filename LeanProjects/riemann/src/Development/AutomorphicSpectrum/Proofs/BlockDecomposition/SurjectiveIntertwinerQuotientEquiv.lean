import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.KerQuot

theorem exists_subQuot_top_ker_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (R : ρ.IntertwiningMap τ) (hR : Function.Surjective R) :
    ∃ S : Subrepresentation ρ, S.toSubmodule = LinearMap.ker R.toLinearMap ∧
      Nonempty ((subQuot ⊤ S).Equiv τ) := by
  refine ⟨Representation.IntertwiningMap.ker ρ τ R, rfl, ?_⟩
  let T : Subrepresentation ρ := ⊤
  let f : T.toSubmodule →ₗ[ℂ] W := R.toLinearMap ∘ₗ T.toSubmodule.subtype
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v, rfl⟩ := hR w
    exact ⟨⟨v, by first | exact Submodule.mem_top | trivial | simp [T]⟩, rfl⟩
  have hker : Submodule.comap T.toSubmodule.subtype
      (Representation.IntertwiningMap.ker ρ τ R).toSubmodule = LinearMap.ker f :=
    (LinearMap.ker_comp T.toSubmodule.subtype R.toLinearMap).symm
  let e := (Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hf)
  refine ⟨⟨⟨e.toLinearMap, fun g => ?_⟩, e.symm, e.left_inv, e.right_inv⟩⟩
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  first
    | exact Representation.IntertwiningMap.isIntertwining ρ τ R g x.1
    | exact R.isIntertwining g x.1
    | simp [e, f, T, GlobalTheory.SmGL.subQuot, Representation.quotient_apply,
        Subrepresentation.toRepresentation, Representation.IntertwiningMap.isIntertwining]

end GlobalTheory.CompanionTheory.BZRes.KerQuot
