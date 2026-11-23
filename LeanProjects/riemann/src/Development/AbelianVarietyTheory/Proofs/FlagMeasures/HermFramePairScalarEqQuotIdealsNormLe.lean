import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairInnerLatticeIndicesAndGeneratorsStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt

theorem mem_ipow_one_iff_exists {K : Type} [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (t : K) :
    t ∈ ipow 𝔞 1 ↔ ∃ a ∈ 𝔞, algebraMap (𝓞 K) K a = t := by
  unfold ipow
  rw [zpow_one]
  exact FractionalIdeal.mem_coeIdeal _

theorem exists_ideal_coeff {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L M : Submodule (𝓞 K) V) (z : V) (hML : M ≤ L)
    (hidx : idx L M ≠ 0) (hz : ∀ t : K, t • z ∈ L ↔ t ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ idx L M ∧ ∀ t : K, t ∈ ipow 𝔞 1 ↔ t • z ∈ M := by
  let f : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V z
  have hf : ∀ a : 𝓞 K, f a = (algebraMap (𝓞 K) K a) • z := fun a => by
    simp only [f, LinearMap.toSpanSingleton_apply, algebraMap_smul]
  let 𝔞 : Ideal (𝓞 K) := M.comap f
  have hr : f.toAddMonoidHom.range ≤ L.toAddSubgroup := by
    rintro _ ⟨a, rfl⟩
    show f a ∈ L
    rw [hf, hz]
    exact Submodule.mem_one.2 ⟨a, rfl⟩
  have hN : Ideal.absNorm 𝔞 = M.toAddSubgroup.relIndex f.toAddMonoidHom.range := by
    rw [← AddSubgroup.index_comap, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hle : Ideal.absNorm 𝔞 ≤ idx L M := by
    rw [hN]; exact AddSubgroup.relIndex_le_of_le_right hr hidx
  have hne : Ideal.absNorm 𝔞 ≠ 0 := by
    rw [hN]
    exact fun h => hidx (AddSubgroup.relIndex_eq_zero_of_le_right hr h)
  refine ⟨𝔞, fun h => hne (by rw [h, Ideal.absNorm_bot]), hle, fun t => ?_⟩
  rw [mem_ipow_one_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← hf]; exact ha
  · intro ht
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ((hz t).1 (hML ht))
    refine ⟨a, ?_, rfl⟩
    show f a ∈ M
    rw [hf]; exact ht

theorem c_eq_quot_ideals : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, -, hz, hz', -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  obtain ⟨hb, -, hD, h1⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hΛ
  obtain ⟨hi, hi', hle, -⟩ := GlobalTheory.T.flagPairInnerLattice_indices_and_generators K V H hK r N g Λ hg hΛ
  set i := idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) with hidef
  have hi0 : i ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hB : cardB N.F N.F' Λ ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hiD : (i : ℝ) ≤ N.Del := by
    have hB1 : (1 : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hB
    have hb1 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
    have hb2 : (1 : ℝ) ≤ (N.bI Λ : ℝ) ^ 2 := one_le_pow₀ hb1
    have hi1 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    calc (i : ℝ) ≤ i * cardB N.F N.F' Λ := le_mul_of_one_le_right hi1 hB1
      _ = delBar N.F N.F' Λ := hi
      _ ≤ delBar N.F N.F' Λ * (N.bI Λ : ℝ) ^ 2 := le_mul_of_one_le_right (by linarith) hb2
      _ = N.Del := hD
  obtain ⟨𝔞, h0, hn, hm⟩ := exists_ideal_coeff _ _ N.F.z (hle.trans inf_le_left) hi0 hz
  obtain ⟨𝔞', h0', hn', hm'⟩ := exists_ideal_coeff _ _ N.F'.z (hle.trans inf_le_right) (hi' ▸ hi0) hz'
  refine ⟨𝔞, 𝔞', h0, h0', le_trans (by exact_mod_cast hn) hiD,
    le_trans (by exact_mod_cast hi' ▸ hn') hiD, fun t => ?_⟩
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) (by simpa using N.j_le)
  rw [hm, hm', hzz, mul_smul]

end GlobalTheory.DegCnt
