import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsSubDivMemSP
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G2

open Formalism.HermitianLattices.Ext.L3

theorem smul_top_pi {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {N : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (J : Ideal R) :
    (J • ⊤ : Submodule R (∀ i, N i)) =
      Submodule.pi Set.univ (fun i => J • (⊤ : Submodule R (N i))) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_pi]
    intro i _
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro v hv
    rw [Submodule.mem_pi] at hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have h1 : Pi.single i (v i) ∈ (J • (⊤ : Submodule R (N i))).map (LinearMap.single R N i) :=
      Submodule.mem_map_of_mem (hv i (Set.mem_univ i))
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1

theorem card_quot_smul_top_congr {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M ≃ₗ[R] N) (J : Ideal R) :
    Nat.card (M ⧸ (J • ⊤ : Submodule R M)) = Nat.card (N ⧸ (J • ⊤ : Submodule R N)) := by
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ f ?_).toEquiv
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

theorem card_quot_quot {A : Type*} [CommRing A] (E J : Ideal A) :
    Nat.card ((A ⧸ E) ⧸ (J • ⊤ : Submodule A (A ⧸ E))) = Nat.card (A ⧸ (E ⊔ J)) := by
  have h1 : (J • ⊤ : Submodule A (A ⧸ E)) = Submodule.map E.mkQ J := by
    conv_lhs => rw [← Submodule.range_mkQ E, LinearMap.range_eq_map, ← Submodule.map_smul'',
      Ideal.smul_eq_mul, Ideal.mul_top]
  rw [h1]
  exact Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup E J).toEquiv

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm (extP K 𝔭) := by
  have hc := Formalism.HermitianLattices.Ext.L3.MeanB.comap_extP_pow (K := K) 𝔭 1
  rw [pow_one, pow_one] at hc
  have h1 : extP K 𝔭 ≠ ⊤ := fun h => h𝔭.ne_top (by rw [← hc, h, Ideal.comap_top])
  have h0 : extP K 𝔭 ≠ ⊥ := by
    intro h
    have hne : 𝔭 ≠ ⊥ := fun h' =>
      NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h' ▸ h𝔭))
    apply hne
    rw [← hc, h]
    ext t
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro ht
      have h2 : algebraMap F K (t : F) = 0 := by
        have h3 := congrArg (algebraMap (𝓞 K) K) ht
        rw [map_zero] at h3
        exact h3
      have h4 : (t : F) = 0 := (algebraMap F K).injective (by rw [h2, map_zero])
      exact_mod_cast h4
    · intro ht
      rw [ht, map_zero]
  have ha0 : Ideal.absNorm (extP K 𝔭) ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)
  have ha1 : Ideal.absNorm (extP K 𝔭) ≠ 1 := fun h => h1 (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem card_pi_quot (𝔭 : Ideal (𝓞 F)) {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ → ℕ) (j : ℕ) :
    Nat.card ((∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i) ⧸
        (extP K 𝔭 ^ j • ⊤ : Submodule (𝓞 K) (∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i))) =
      Ideal.absNorm (extP K 𝔭) ^ ∑ i, min (e i) j := by
  rw [smul_top_pi, Nat.card_congr (Submodule.quotientPi
    (fun i => (extP K 𝔭 ^ j • ⊤ : Submodule (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ e i)))).toEquiv,
    Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hsup : extP K 𝔭 ^ e i ⊔ extP K 𝔭 ^ j = extP K 𝔭 ^ min (e i) j := by
    rcases le_total (e i) j with h | h
    · rw [min_eq_left h, sup_eq_left.mpr (Ideal.pow_le_pow_right h)]
    · rw [min_eq_right h, sup_eq_right.mpr (Ideal.pow_le_pow_right h)]
  rw [card_quot_quot, hsup, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow]

end Formalism.L2.SG.Pf.G2
