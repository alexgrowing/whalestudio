import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow

namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem condC_sh_and_nab_mem : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ a : ℤ, CondC g (sh a N) ∧ ∀ x ∈ sh a N, nab g x ∈ sh a N := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hC a
  have h : ∀ x ∈ sh a N, nab g x ∈ sh a N := fun x hx => Window.nab_mem_sh R hg hC a hx
  exact ⟨(condC_iff_nab_mem g _).2 h, h⟩

end GlobalTheory.PhiGam
