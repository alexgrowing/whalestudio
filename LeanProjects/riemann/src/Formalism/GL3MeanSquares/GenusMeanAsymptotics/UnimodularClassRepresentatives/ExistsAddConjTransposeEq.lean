import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DetMulLeftCompMulRight

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_add_conj_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (a : 𝓞 F) :
    ∃ z : 𝓞 K, z + conjO K z = algebraMap (𝓞 F) (𝓞 K) a := by
  have htop : LinearMap.range (idealPowerSpanBounds.trF hF) = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal (LinearMap.range (idealPowerSpanBounds.trF hF)) hne
    obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
    have hmem : ∀ z : 𝓞 K, z + conjO K z ∈ extP K 𝔭 := fun z => by
      rw [← idealPowerSpanBounds.trF_spec hF]
      exact Ideal.mem_map_of_mem _ (hle ⟨z, rfl⟩)
    have h2 : (2 : 𝓞 K) ∈ extP K 𝔭 := by
      have := hmem 1
      rwa [map_one, one_add_one_eq_two] at this
    have hsq : (θ - conjO K θ) * (θ - conjO K θ) ∈ extP K 𝔭 := by
      have : (θ - conjO K θ) * (θ - conjO K θ) =
          (θ + conjO K θ) * (θ + conjO K θ) - 2 * (2 * (θ * conjO K θ)) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ (hmem θ)) (Ideal.mul_mem_right _ _ h2)
    have h1 : (θ - conjO K θ) ∈ extP K 𝔭 ^ 1 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by rwa [pow_one])
    have h0 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by rwa [mul_one])
    have h3 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by rwa [map_one])
    rw [pow_one] at h3
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  obtain ⟨z, hz⟩ : a ∈ LinearMap.range (idealPowerSpanBounds.trF hF) := htop ▸ Submodule.mem_top
  exact ⟨z, by rw [← idealPowerSpanBounds.trF_spec hF, hz]⟩

end Formalism.HermitianLattices.Ext.L3
