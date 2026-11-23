import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeKernelRankBoundNorm
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_kernel_rank_bound_norm : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly | exact GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly <;> assumption)
