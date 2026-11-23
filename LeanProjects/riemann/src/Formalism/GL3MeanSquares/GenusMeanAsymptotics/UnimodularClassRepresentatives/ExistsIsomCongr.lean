import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.WCC

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_isom_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {x y : V} (hxL : x ∈ (locF 𝔭 A₀))
    (hyL : y ∈ (locF 𝔭 A₀)) (hx : h x x = algebraMap F K (n : F)) (hy : h y y = algebraMap F K (n : F))
    {j : ℕ} (hj : 4 * vF 𝔭 n + eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ j)
    (hxy : y - x ∈ ((extP K 𝔭) ^ j • (locF 𝔭 A₀) : Submodule (𝓞 K) V)) :
    ∃ g ∈ autSub h (locF 𝔭 A₀),
      (∀ z ∈ (locF 𝔭 A₀), g z - z ∈ ((extP K 𝔭) ^ (j - 2 * vF 𝔭 n) • (locF 𝔭 A₀) : Submodule (𝓞 K) V)) ∧
      g x = y := by
  classical
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  have han : ∀ z, h z z = 0 → z = 0 := by
    intro z hz
    by_contra hz0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have hpos := hd z hz0 φ
    rw [hz, map_zero, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  set v := vF 𝔭 n with hvdef
  have hv : n ∉ 𝔭 ^ (v + 1) := localValuationFiltration.notMem_pow_vF h𝔭 hn
  have hx0 : WCA.InL 𝔭 A₀ 0 x := (WCA.inL_zero_iff hp).2 hxL
  have hJ : 1 ≤ j - 2 * v := by omega
  have hw : WCA.InL 𝔭 A₀ (v + (v + (j - 2 * v))) (y - x) := by
    have e : v + (v + (j - 2 * v)) = j := by omega
    rw [e]
    exact WCA.InL.of_mem h𝔭 hxy
  obtain ⟨g, hgI, hgJ, hgS, hgxy⟩ := WCC.core hK hF hs han hA₀i h𝔭 hn hv hx0 hx hy hJ hw
  have hL : ∀ z, z ∈ locF 𝔭 A₀ → g z ∈ locF 𝔭 A₀ := by
    intro z hz
    have hz0 : WCA.InL 𝔭 A₀ 0 z := (WCA.inL_zero_iff hp).2 hz
    have h1 : WCA.InL 𝔭 A₀ 0 (g z - z) := (hgJ z hz0).mono (Nat.zero_le _)
    have h2 := h1.add hp hz0
    rw [sub_add_cancel] at h2
    exact (WCA.inL_zero_iff hp).1 h2
  have hLs : ∀ z, z ∈ locF 𝔭 A₀ → g.symm z ∈ locF 𝔭 A₀ := fun z hz =>
    (WCA.inL_zero_iff hp).1 (hgS z ((WCA.inL_zero_iff hp).2 hz))
  refine ⟨g, ?_, fun z hz => (hgJ z ((WCA.inL_zero_iff hp).2 hz)).mem hp, hgxy⟩
  show g ∈ Formalism.ThetaLiftIndependence.autL h (locF 𝔭 A₀)
  refine ⟨hgI, le_antisymm ?_ ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hL z hz
  · intro z hz
    exact Submodule.mem_map.2 ⟨g.symm z, hLs z hz, by simp⟩

end Formalism.HermitianLattices.Ext.L3
