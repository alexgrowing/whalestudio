import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory

theorem thetaSys_exists_norm_FF_eq :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (B : ℝ), (∀ (t : T) i, ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ ≤ B) → (∃ (t : T) (i : S.J), B ≤ ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖) → ∃ (k : _) (hk : S.FF T c k ∈ S.R), ‖y₀ ⟨S.FF T c k, hk⟩‖ = B := by
  intro o Ω _ _ _ hA S p _ y₀ hy T c B hle ⟨t, i, hge⟩
  have hN := S.N_ge
  have hr := S.r_pos
  have hrN : 2 ≤ S.r * S.N := le_trans hN (Nat.le_mul_of_pos_left _ hr)
  have hn : 1 < (S.r * S.N) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have : Fact (1 < (S.r * S.N) ^ 2) := ⟨hn⟩
  have : IsDomain o := hA.inj.isDomain _
  have : NeZero (S.r * S.N) := ⟨by omega⟩
  have := Fintype.ofFinite T
  have hmem := (thetaSys_FF_mem_finite_perp_proj o Ω S).1 T c
  set E : T → PadicAlgCl p := fun s =>
    ∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev s j, S.ev_mem s j⟩ with hE
  have hval : ∀ k : T → ZMod ((S.r * S.N) ^ 2), y₀ ⟨S.FF T c (i, k), hmem _⟩
      = ∑ s, y₀ (algebraMap o S.R S.ζ) ^ (k s).val * E s := fun k => by
    have : (⟨S.FF T c (i, k), hmem _⟩ : S.R) = ∑ s : T, algebraMap o S.R S.ζ ^ (k s).val *
        ∑ j, algebraMap o S.R (S.proj T c j i) * ⟨S.ev s j, S.ev_mem s j⟩ := by
      apply Subtype.ext
      simp [ThetaSys.FF, finsum_eq_sum_of_fintype]
    rw [this]
    simp [hE, map_sum]
  have hB : ‖E t‖ = B := le_antisymm (hle t i) hge
  have hB0 : 0 ≤ B := hB ▸ norm_nonneg _
  have h0 : ‖∑ s, E s‖ ≤ B :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun s _ => hle s i
  rcases h0.eq_or_lt with h0 | h0
  · refine ⟨(i, 0), hmem _, ?_⟩
    rw [hval]
    simpa using h0
  · have hu : IsUnit (1 - S.ζ) := by
      obtain ⟨m, hm⟩ : ∃ m, (S.r * S.N) ^ 2 = m + 1 + 1 := ⟨(S.r * S.N) ^ 2 - 2, by omega⟩
      have hp := S.prim
      rw [hm] at hp
      have h1 := hp.prod_one_sub_pow_eq_order
      have h2 : IsUnit ((((S.r * S.N) ^ 2 : ℕ)) : o) := by
        rw [Nat.cast_pow]; exact S.unit.pow _
      rw [hm, Nat.cast_succ, ← h1, Finset.prod_range_succ'] at h2
      simpa using isUnit_of_mul_isUnit_right h2
    have hone : ‖1 - y₀ (algebraMap o S.R S.ζ)‖ = 1 := by
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have h1 := hy (1 - S.ζ)
      have h2 := hy v
      have h3 : ‖y₀ (algebraMap o S.R (1 - S.ζ))‖ * ‖y₀ (algebraMap o S.R v)‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, hv, map_one, map_one, norm_one]
      rw [map_sub, map_sub, map_one, map_one] at h1 h3
      refine le_antisymm h1 ?_
      calc (1 : ℝ) = _ := h3.symm
        _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2
    refine ⟨(i, Pi.single t 1), hmem _, ?_⟩
    have hs : ∑ s, y₀ (algebraMap o S.R S.ζ) ^ ((Pi.single t 1 : T → ZMod ((S.r * S.N) ^ 2)) s).val * E s
        = ∑ s, E s + -((1 - y₀ (algebraMap o S.R S.ζ)) * E t) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t),
        ← Finset.add_sum_erase _ E (Finset.mem_univ t),
        Finset.sum_congr rfl (g := E) fun s hs => by
          rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hs), ZMod.val_zero, pow_zero,
            _root_.one_mul]]
      rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      ring
    have hn' : ‖-((1 - y₀ (algebraMap o S.R S.ζ)) * E t)‖ = B := by
      rw [norm_neg, norm_mul, hone, _root_.one_mul, hB]
    rw [hval, hs, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hn']; exact h0.ne),
      hn', max_eq_right h0.le]

end GlobalTheory
