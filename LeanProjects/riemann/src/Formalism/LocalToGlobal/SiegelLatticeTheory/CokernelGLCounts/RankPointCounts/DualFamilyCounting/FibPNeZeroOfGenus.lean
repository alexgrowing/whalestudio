import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibSEqSingleton
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocReps
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem isLatIn_cut {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (X : Submodule K V) :
    IsLatIn X (Λ ⊓ X.restrictScalars (𝓞 K)) := by
  refine ⟨?_, le_antisymm (Submodule.span_le.mpr fun x hx => hx.2) fun x hx => ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    exact Submodule.FG.of_le_of_isNoetherian (inf_le_left : Λ ⊓ X.restrictScalars (𝓞 K) ≤ Λ)
  · obtain ⟨r, hr, hrx⟩ := StabilizerLattices.exists_smul_mem hΛ x
    have h1 : r • x ∈ Λ ⊓ X.restrictScalars (𝓞 K) := ⟨hrx, (X.restrictScalars (𝓞 K)).smul_mem r hx⟩
    have hr' : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
    have e : x = (algebraMap (𝓞 K) K r)⁻¹ • (r • x) := by
      rw [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem nondegenerate_of {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) :
    h.Nondegenerate := by
  constructor
  · exact hnd
  · intro y hy
    refine hnd y fun x => ?_
    rw [← hs.eq x y, hy x, map_zero]

theorem finite_fibS (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    (fibS h U 𝔭 M T).Finite := by
  have hp := h𝔭.isPrime
  have hN := isLattice_sup hUc hM hT
  have hD : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) :=
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs (nondegenerate_of hs hnd) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range _ hN).1
  have hND := LIOrb.isLattice_inf hN hD
  have key : ∀ Λ ∈ fibS h U 𝔭 M T, locF 𝔭 (M ⊔ T) ≤ Λ ∧ Λ ≤ locF 𝔭 (Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) ∧
      locF 𝔭 Λ = Λ := by
    rintro Λ ⟨⟨Λ', -, rfl⟩, h1, h2, h3⟩
    have hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ' := by
      have hs' : M ⊔ T ≤ locF 𝔭 Λ' := sup_le
        ((LocF.le_locF 𝔭 M).trans (h2 ▸ inf_le_left)) ((LocF.le_locF 𝔭 T).trans (h3 ▸ inf_le_left))
      exact (LocF.locF_mono 𝔭 hs').trans (LocF.locF_idem 𝔭 Λ').le
    refine ⟨hle, ?_, LocF.locF_idem 𝔭 Λ'⟩
    rw [G7.locF_dual hF h hN.fg hp]
    calc locF 𝔭 Λ' = dualF h 𝔭 (locF 𝔭 Λ') := h1.symm
      _ ≤ dualF h 𝔭 (locF 𝔭 (M ⊔ T)) := dualF_anti h 𝔭 hle
  refine Set.Finite.of_finite_image (f := fun Λ => Λ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T))
    ((BrB.finite_between hND hD inf_le_right).subset ?_) ?_
  · rintro _ ⟨Λ, hΛ, rfl⟩
    obtain ⟨k1, -, -⟩ := key Λ hΛ
    exact ⟨inf_le_inf_right _ ((LocF.le_locF 𝔭 _).trans k1), inf_le_right⟩
  · intro Λ₁ h1 Λ₂ h2 he
    obtain ⟨-, a1, b1⟩ := key Λ₁ h1
    obtain ⟨-, a2, b2⟩ := key Λ₂ h2
    have e1 : locF 𝔭 (Λ₁ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) = Λ₁ := by
      rw [LIOrb.locF_inf_locF h𝔭, b1]; exact inf_eq_left.2 a1
    have e2 : locF 𝔭 (Λ₂ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) = Λ₂ := by
      rw [LIOrb.locF_inf_locF h𝔭, b2]; exact inf_eq_left.2 a2
    rw [← e1, ← e2]
    exact congrArg (locF 𝔭) he

theorem fibP_ne_zero_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    fibP h U 𝔭 M T ≠ 0 ↔ (fibS h U 𝔭 M T).Nonempty := by
  have hfin := finite_fibS hF hs hnd hUc hM hT h𝔭
  rw [fibP_eq, Nat.card_ne_zero]
  constructor
  · rintro ⟨⟨x, hx⟩, -⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨⟨x, hx⟩⟩, hfin.to_subtype⟩

theorem fibP_congr (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M : Submodule (𝓞 K) V)
    {T T' : Submodule (𝓞 K) V} (e : locF 𝔭 T = locF 𝔭 T') : fibP h U 𝔭 M T = fibP h U 𝔭 M T' := by
  unfold fibP
  rw [e]

theorem fibP_ne_zero_of_genus (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M : Submodule (𝓞 K) V}
    (hM : IsLatIn U M) {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M) {T : Submodule (𝓞 K) V}
    (hg : SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : fibP h U 𝔭 M T ≠ 0 := by
  obtain ⟨g, hg, he⟩ := hg 𝔭 h𝔭
  have hT₀ := isLatIn_cut hΛ₀.1 (orthK h U)
  rw [← fibP_congr h U 𝔭 M (show locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K))) = locF 𝔭 T
      by rw [← LocalizedFibreSets.gmap_locF, he]), G6.fibP_gmap hM 𝔭 _ hg,
    fibP_ne_zero_iff hF hs hnd hUc hM hT₀ h𝔭]
  exact ⟨_, locF_mem_fibS hF hΛ₀.1 hΛ₀.2.1 hΛ₀.2.2 rfl h𝔭⟩

end Formalism.L2.SG.Pf.G8
