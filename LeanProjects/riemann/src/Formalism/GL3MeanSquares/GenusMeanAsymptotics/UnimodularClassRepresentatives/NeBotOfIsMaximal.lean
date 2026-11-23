import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumPeriodic
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.BoxInterEqEmpty

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem vF_lt_of_notMem {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {e : ℕ} (h : n ∉ 𝔭 ^ e) : vF 𝔭 n < e := by
  unfold vF
  have hne : ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ).Nonempty := ⟨0, by simp⟩
  have hlt : ∀ k ∈ ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ), k < e := by
    intro k hk
    by_contra hke
    push_neg at hke
    exact h (Ideal.pow_le_pow_right hke hk)
  have hbdd : BddAbove ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ) := ⟨e, fun k hk => (hlt k hk).le⟩
  exact hlt _ (Nat.sSup_mem hne hbdd)

theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ := by
  haveI := h𝔭
  exact Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭

theorem one_lt_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact h𝔭.ne_top
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact ne_bot_of_isMaximal h𝔭
  have h2 : 1 < Ideal.absNorm 𝔭 := by omega
  exact_mod_cast h2

end Formalism.HermitianLattices.Ext.L3.BoxSum
