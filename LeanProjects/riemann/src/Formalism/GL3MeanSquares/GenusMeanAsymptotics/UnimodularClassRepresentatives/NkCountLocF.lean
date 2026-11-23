import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FirstFamilyOperatorEnd

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem nkCount_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) : nkCount h (locF 𝔭 L) 𝔭 k n = nkCount h L 𝔭 k n :=
  localizedQuotients.nkCount_locF hF h L 𝔭 h𝔭 k n

theorem akCount_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : akCount h (locF 𝔭 L) 𝔭 k = akCount h L 𝔭 k :=
  localizedQuotients.akCount_locF hF h L 𝔭 h𝔭 k

theorem vd_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : vd h (locF 𝔭 L) 𝔭 = vd h L 𝔭 :=
  localizedQuotients.vd_locF hF h L h𝔭

theorem nkCount_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {k : ℕ}
    (hk : 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k) :
    nkCount h L 𝔭 (k + 1) n = Ideal.absNorm 𝔭 ^ (2 * finrank K V - 1) * nkCount h L 𝔭 k n :=
  firstFamilyOperatorEnd.nkCount_succ_fine hK hF hs hd hL hLi h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hn) (by omega)

theorem alphaN_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n n' : 𝓞 F} (hn : n ≠ 0)
    {k : ℕ} (hk : vF 𝔭 n + 2 * vd h L 𝔭 + 2 ≤ k) (hc : n - n' ∈ 𝔭 ^ k) :
    alphaN h L 𝔭 n = alphaN h L 𝔭 n' := by
  have hn1 := localValuationFiltration.notMem_pow_vF h𝔭 hn
  have hn1' : n' ∉ 𝔭 ^ (vF 𝔭 n + 1) := by
    intro h'
    apply hn1
    have hk' : 𝔭 ^ k ≤ 𝔭 ^ (vF 𝔭 n + 1) := Ideal.pow_le_pow_right (by omega)
    have := Ideal.add_mem _ (hk' hc) h'
    simpa using this
  rw [firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 hn1 (k := k) (by omega),
    firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 hn1' (k := k) (by omega),
    firstFamilyOperatorEnd.nkCount_congr hF hs hd hL hLi h𝔭 hc]

theorem nkCount_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ C : ℝ, ∀ (k : ℕ) (n : 𝓞 F),
      (nkCount h L 𝔭 k n : ℝ) ≤ C * (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  refine ⟨2 * (Ideal.absNorm 𝔭 : ℝ) ^ (2 * vd h L 𝔭 + 1), fun k n => ?_⟩
  have := firstFamilyOperatorEnd.nkCount_le_nat hK hF hs hd hL hLi hm h𝔭 k n
  exact_mod_cast this

theorem alphaL_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < alphaL h L 𝔭 := by
  rw [firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := 2 * vd h L 𝔭 + 1) le_rfl]
  have hN : 0 < Ideal.absNorm 𝔭 := by
    haveI := h𝔭
    exact Nat.pos_of_ne_zero fun h0 =>
      Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭 (Ideal.absNorm_eq_zero_iff.mp h0)
  apply div_pos
  · exact_mod_cast firstFamilyOperatorEnd.akCount_pos hF hs hd hL hLi h𝔭 _
  · apply pow_pos
    exact_mod_cast hN

end Formalism.HermitianLattices.Ext.L3
