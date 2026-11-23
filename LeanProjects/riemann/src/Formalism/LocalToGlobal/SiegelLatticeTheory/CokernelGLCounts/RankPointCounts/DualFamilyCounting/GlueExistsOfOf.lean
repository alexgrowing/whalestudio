import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFSubspace
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ApplyMemSmulOfMemAutSub

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def GlueLocal : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → cJ h U M 𝔭 < finrank K (orthK h U) →
      ∃ T : Submodule (𝓞 K) V, (∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧ locF 𝔭 A = T) ∧
        dualF h 𝔭 T = T ∧ T ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

def BadFinite : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ →
    ∀ U : Submodule K V, ∀ M : Submodule (𝓞 K) V, IsLatIn U M →
      ∃ s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∀ 𝔭 ∉ s,
        locF 𝔭.1 (Λ₀ ⊓ U.restrictScalars (𝓞 K)) = locF 𝔭.1 M

theorem glueExists_of_of (hloc : GlueLocal) (hfin : BadFinite) : GlueExists := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀' M hM hMi hc
  obtain ⟨Λ₀, hΛ₀, hΛ₀u⟩ := hΛ₀'
  obtain ⟨s, hsM⟩ := hfin K F V hK hF Λ₀ hΛ₀ U M hM
  choose T hT using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    hloc K F V hK hF h hs hnd U hUc hpos ⟨Λ₀, hΛ₀, hΛ₀u⟩ M hM hMi 𝔭.1 𝔭.2 (hc 𝔭.1 𝔭.2)
  obtain ⟨Λ, ⟨hΛ, hΛs, hΛn⟩, -⟩ := exists_unique_patch hK hF hΛ₀ s T (fun 𝔭 _ => by
    obtain ⟨A, hA, e⟩ := (hT 𝔭).1
    exact ⟨by rw [← e, LocF.locF_idem], A, hA, e⟩)
  have key : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      locF 𝔭.1 Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭.1 M ∧
        dualF h 𝔭.1 (locF 𝔭.1 Λ) = locF 𝔭.1 Λ := by
    intro 𝔭
    by_cases hp : 𝔭 ∈ s
    · rw [hΛs 𝔭 hp]
      exact ⟨(hT 𝔭).2.2, (hT 𝔭).2.1⟩
    · rw [hΛn 𝔭 hp]
      refine ⟨?_, ?_⟩
      · rw [← hsM 𝔭 hp, LIOrb.locF_inf_locF 𝔭.2, locF_subspace U 𝔭.2.isPrime]
      · rw [← locF_dual hF h hΛ₀.fg 𝔭.2.isPrime]
        exact congrArg (locF 𝔭.1) hΛ₀u
  refine ⟨Λ, hΛ, ?_, ?_⟩
  · show Formalism.HermitianLatticesTheory.dual h Λ = Λ
    apply eq_of_locF (F := F)
    intro 𝔭 h𝔭
    rw [locF_dual hF h hΛ.fg h𝔭.isPrime]
    exact (key ⟨𝔭, h𝔭⟩).2
  · apply eq_of_locF (F := F)
    intro 𝔭 h𝔭
    rw [LIOrb.locF_inf_locF h𝔭, locF_subspace U h𝔭.isPrime]
    exact (key ⟨𝔭, h𝔭⟩).1

end Formalism.L2.SG.Pf.G7
