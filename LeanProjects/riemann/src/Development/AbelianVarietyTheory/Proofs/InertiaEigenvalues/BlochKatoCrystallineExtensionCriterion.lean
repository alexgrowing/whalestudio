import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryIffIsCrys
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ExtCrysCrit

theorem cocycle_of_ext {G LL V₀ V₁ : Type} [Group G] [TopologicalSpace G] [Field LL] [TopologicalSpace LL]
    [AddCommGroup V₀] [Module LL V₀] [TopologicalSpace V₀] [ContinuousAdd V₀] [ContinuousSMul LL V₀]
    [AddCommGroup V₁] [Module LL V₁] [TopologicalSpace V₁] [IsModuleTopology LL V₁]
    (ρ₀ : Representation LL G V₀) (ρ₁ : Representation LL G V₁) (ι : V₀ →ₗ[LL] V₁)
    (hι : Function.Injective ι) (hιρ : ∀ g y, ι (ρ₀ g y) = ρ₁ g (ι y)) (x : V₁)
    (hx : Continuous fun g => ρ₁ g x) (c : G → V₀) (hc : ∀ g, ι (c g) = ρ₁ g x - x) :
    Continuous c ∧ ∀ g h, c (g * h) = c g + ρ₀ g (c h) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.2 hι)
  have hrc : ∀ g, c g = r (ρ₁ g x) + (- r x) := by
    intro g
    rw [← sub_eq_add_neg, ← map_sub, ← hc, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  refine ⟨?_, fun g h => hι ?_⟩
  · have : c = fun g => r (ρ₁ g x) + (- r x) := funext hrc
    rw [this]
    exact ((IsModuleTopology.continuous_of_linearMap r).comp hx).add continuous_const
  · rw [map_add, hιρ, hc, hc, hc, map_mul, Module.End.mul_apply, map_sub]
    abel

theorem finrank_ext {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [FiniteDimensional LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (h1 : Module.finrank LL V₂ = 1) :
    Module.finrank LL V₁ = Module.finrank LL V₀ + 1 := by
  have hk' : LinearMap.ker π = LinearMap.range ι := by
    ext z; rw [LinearMap.mem_ker, LinearMap.mem_range]; exact hk z
  have h := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.2 hπ, finrank_top, hk', LinearMap.finrank_range_of_inj hι, h1] at h
  omega

theorem not_mem_range {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (x : V₁) (hx : π x ≠ 0) :
    x ∉ LinearMap.range ι := by
  rintro ⟨y, rfl⟩
  exact hx ((hk _).2 ⟨y, rfl⟩)

theorem blochKato_ext_all : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm15 D := by
  intro D l _ K LL
  intro T Tp To ι π hses htriv hdim hcrys x hxT hπx c hc
  have key := GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Tp.V Tp.ρ ι.f ι.equiv hses.1
    (finrank_ext ι.f π.f hses.1 hses.2.1 hses.2.2.2.1 hdim) hcrys x
    (not_mem_range ι.f π.f hses.2.2.2.1 x hπx) c hc
  obtain ⟨hcont, hcoc⟩ := cocycle_of_ext T.ρ Tp.ρ ι.f hses.1 ι.equiv x (Tp.cont x) c hc
  exact ⟨fun h => key.1 h.2, fun h => ⟨⟨hcont, hcoc⟩, key.2 h⟩⟩

end GlobalTheory.ExtCrysCrit
