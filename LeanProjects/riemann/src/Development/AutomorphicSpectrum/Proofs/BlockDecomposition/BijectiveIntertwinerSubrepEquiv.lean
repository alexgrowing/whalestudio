import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem subQuot_bot_equiv_of_bijective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (S : Subrepresentation ρ) (O : S.toSubmodule →ₗ[ℂ] W)
    (hO : Function.Bijective O)
    (hi : ∀ (g : G) (v : S.toSubmodule), O ⟨ρ g v, S.apply_mem_toSubmodule g v.2⟩ = τ g (O v)) :
    Nonempty ((subQuot S ⊥).Equiv τ) := by
  have hbot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := by
    first
      | rfl
      | simp
      | (ext v; simp)
  have hp : Submodule.comap S.toSubmodule.subtype (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := by
    rw [hbot, Submodule.comap_bot, Submodule.ker_subtype]
  let e := (Submodule.quotEquivOfEqBot _ hp).trans (LinearEquiv.ofBijective O hO)
  refine ⟨Representation.Equiv.mk' ⟨e.toLinearMap, fun g => ?_⟩ e.symm e.left_inv e.right_inv⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact hi g v

end GlobalTheory.CompanionTheory.BZRes
