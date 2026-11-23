import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AkCountEqRedCountMul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNearRepresentation
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdLeOneOfBasis

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private theorem algebraMap_int_F_to_K_eq_algebraMap_F_K (n : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := by
  rw [← IsScalarTower.algebraMap_apply]
  first
  | exact IsScalarTower.algebraMap_apply (𝓞 F) F K n
  | (rw [IsScalarTower.algebraMap_apply (𝓞 F) F K]; rfl)
  | simp

theorem exists_exact_near (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0)
    (hrep : ∃ b : V, h b b = algebraMap F K (n : F)) :
    ∃ c₀ : ℕ, ∀ k : ℕ, c₀ ≤ k → ∀ x ∈ (locF 𝔭 A₀), CongrP 𝔭 k (h x x) (algebraMap F K (n : F)) →
      ∃ y ∈ (locF 𝔭 A₀), h y y = algebraMap F K (n : F) ∧
        y - x ∈ ((extP K 𝔭) ^ (k - c₀) • (locF 𝔭 A₀) : Submodule (𝓞 K) V) := by
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨v, hv⟩ := Cell.exists_near (𝔭 := 𝔭) h𝔭 hF hs hA₀ hA₀i hn
    (by obtain ⟨b, hb⟩ := hrep; exact ⟨b, by rw [algebraMap_int_F_to_K_eq_algebraMap_F_K]; exact hb⟩)
  refine ⟨v + 1, fun k hk x hx hc => ?_⟩
  rw [Cell.congrP_iff_inI] at hc
  obtain ⟨y, hy0, hyy, hyx⟩ := hv (k - v) (by omega) x ((WCA.inL_zero_iff hp).2 hx)
    (by rw [algebraMap_int_F_to_K_eq_algebraMap_F_K, show v + (k - v) = k by omega]; exact hc)
  refine ⟨y, (WCA.inL_zero_iff hp).1 hy0, by rw [hyy, algebraMap_int_F_to_K_eq_algebraMap_F_K], ?_⟩
  exact (WCA.InL.mono (by omega) hyx).mem hp

theorem exists_lattice_vd_le_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} {n : 𝓞 F} (hx : h x₀ x₀ = algebraMap F K (n : F)) (hn : n ∉ 𝔭) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
      x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
  exact Cell.exists_lattice (𝔭 := 𝔭) hK hF hs hd h𝔭 (by rw [algebraMap_int_F_to_K_eq_algebraMap_F_K]; exact hx) hn

end Formalism.HermitianLattices.Ext.L3
