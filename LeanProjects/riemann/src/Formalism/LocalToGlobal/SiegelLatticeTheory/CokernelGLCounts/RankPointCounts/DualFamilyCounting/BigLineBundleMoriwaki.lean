import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GmapEqSelfOfFix
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscIsoOfProj

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def ProjInto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ x ∈ Λ, X.projection Y hc x ∈ locF 𝔭 (dualIn h X L)

def ProjOnto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ v ∈ locF 𝔭 (dualIn h X L), ∃ x ∈ Λ, X.projection Y hc x = v

def FibCount : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M T : Submodule (𝓞 K) V, IsLatIn U M → IsLatIn (orthK h U) T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      fibP h U 𝔭 M T ≠ 0 → fibP h U 𝔭 M T = discAut h (orthK h U) T 𝔭

end Formalism.L2.SG.Pf.G6

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6

theorem glueLoc_of (hi : ProjInto) (ho : ProjOnto) (hn : FibCount) : GlueLoc := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭
  refine ⟨fun hne => ⟨?_, hn K F V hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭 hne⟩,
    fun g hg => fibP_gmap hM 𝔭 T hg⟩
  obtain ⟨⟨Λ, hΛ0, hΛd, hΛU, hΛW⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have oU : ∀ x ∈ U, ∀ y ∈ orthK h U, h x y = 0 := fun x hx y hy => mem_orthK.mp hy x hx
  have oW : ∀ x ∈ orthK h U, ∀ y ∈ U, h x y = 0 := by
    intro x hx y hy
    have e := hs.eq x y
    rw [oU y hy x hx] at e
    simpa using e
  exact discIso_of_proj h hcU hΛU hΛW
    (hi K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (ho K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (hi K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)
    (ho K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)

end Formalism.L2.SG.Pf.Cnt
