import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv

open GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift

namespace GlobalTheory.Cyc.CocycleCount

theorem dependent_of_card_le : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (ψ : G →* ℤ_[l]ˣ) (C n : ℕ), (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ∧ Nat.card (ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ r))) ≤ C * l ^ (r * n)) → ∀ z : Fin (n + 1) → G → ℚ_[l], (∀ i, Continuous (z i)) → (∀ i g h, z i (g * h) = z i g + ((ψ g : ℤ_[l]) : ℚ_[l]) * z i h) → ∃ c : Fin (n + 1) → ℚ_[l], c ≠ 0 ∧ ∀ g, ∑ i, c i * z i g = 0 := by
  intro l _ G _ _ _ _ ψ C n hC z hz hcoc
  have hl : l.Prime := Fact.out
  by_contra hne
  push Not at hne

  obtain ⟨B, hB⟩ := (isCompact_range (continuous_pi hz : Continuous fun g i => z i g)).isBounded.exists_norm_le
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt ℚ_[l] (r := (max B 1)⁻¹) (by positivity)
  have ha1 : ∀ i g, ‖a * z i g‖ ≤ 1 := fun i g => by
    rw [norm_mul]
    have h1 : ‖z i g‖ ≤ max B 1 :=
      ((norm_le_pi_norm (fun i => z i g) i).trans (hB _ ⟨g, rfl⟩)).trans (le_max_left _ _)
    calc ‖a‖ * ‖z i g‖ ≤ (max B 1)⁻¹ * max B 1 := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have ha' : a ≠ 0 := norm_pos_iff.1 ha0
  let w : Fin (n + 1) → G → ℤ_[l] := fun i g => ⟨a * z i g, ha1 i g⟩
  have hw : ∀ i, Continuous (w i) := fun i => (continuous_const.mul (hz i)).subtype_mk _
  have hwc : ∀ i g h, w i (g * h) = w i g + (ψ g : ℤ_[l]) * w i h := fun i g h => Subtype.ext (by
    change a * z i (g * h) = a * z i g + ((ψ g : ℤ_[l]) : ℚ_[l]) * (a * z i h)
    rw [hcoc]; ring)
  let W : Fin (n + 1) → C(G, ℚ_[l]) := fun i => ⟨fun g => a * z i g, continuous_const.mul (hz i)⟩
  let L : (Fin (n + 1) → ℚ_[l]) →ₗ[ℚ_[l]] C(G, ℚ_[l]) := Fintype.linearCombination ℚ_[l] W
  have hL : ∀ c g, L c g = ∑ i, c i * (a * z i g) := fun c g => by
    simp [L, W, Fintype.linearCombination_apply, ContinuousMap.sum_apply]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    by_contra h0
    obtain ⟨g, hg⟩ := hne c h0
    apply hg
    have h1 := hL c g
    rw [hc, ContinuousMap.zero_apply] at h1
    apply mul_left_cancel₀ ha'
    rw [mul_zero, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  obtain ⟨v, hv⟩ := pow_unbounded_of_one_lt (K : ℝ) hl1
  have key : ∀ r : ℕ, 0 < r → l ^ r ≤ C * l ^ (v * n) := by
    intro r hr
    obtain ⟨hfin, hcard⟩ := hC (r + v) (by omega)
    let F : (Fin (n + 1) → Fin (l ^ r)) →
        ReciprocityTheory.Gal.Z1 (ReciprocityTheory.Gal.charRep (redChar ψ (r + v))) := fun c =>
      ⟨fun g => PadicInt.toZModPow (r + v) (∑ i, ((c i : ℕ) : ℤ_[l]) * w i g),
        (continuous_toZModPow _).comp
          (continuous_finset_sum _ fun i _ => continuous_const.mul (hw i)), fun g h => by
        rw [ReciprocityTheory.Gal.charRep_apply, redChar_apply, ← map_mul, ← map_add, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine congrArg (PadicInt.toZModPow (r + v)) ?_
        exact Finset.sum_congr rfl fun i _ => by rw [hwc]; ring⟩
    have hF : Function.Injective F := by
      intro c c' h
      let d : Fin (n + 1) → ℚ_[l] := fun i => ((((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) : ℤ) : ℚ_[l])
      have h1 : ‖L d‖ ≤ (l : ℝ) ^ (-((r + v : ℕ) : ℤ)) := by
        rw [ContinuousMap.norm_le _ (by positivity)]
        intro g
        have h2 : PadicInt.toZModPow (r + v) (∑ i, ((c i : ℕ) : ℤ_[l]) * w i g) =
            PadicInt.toZModPow (r + v) (∑ i, ((c' i : ℕ) : ℤ_[l]) * w i g) :=
          congrFun (congrArg Subtype.val h) g
        rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
          ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def] at h2
        refine le_of_eq_of_le (congrArg norm ?_) h2
        rw [hL, ← Finset.sum_sub_distrib]
        refine Eq.trans ?_ (map_sum (PadicInt.Coe.ringHom (p := l)) _ _).symm
        refine Finset.sum_congr rfl fun i _ => ?_
        change _ = ((((c i : ℕ) : ℤ_[l]) * w i g - ((c' i : ℕ) : ℤ_[l]) * w i g : ℤ_[l]) : ℚ_[l])
        have hwv : ((w i g : ℤ_[l]) : ℚ_[l]) = a * z i g := rfl
        rw [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_mul, PadicInt.coe_natCast,
          PadicInt.coe_natCast, hwv]
        simp only [d, Int.cast_sub, Int.cast_natCast]
        ring
      have h3 : ‖d‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
        have h4 := ZeroHomClass.bound_of_antilipschitz L hK d
        calc ‖d‖ ≤ K * ‖L d‖ := h4
          _ ≤ (l : ℝ) ^ v * (l : ℝ) ^ (-((r + v : ℕ) : ℤ)) := by gcongr
          _ = _ := by
            rw [← zpow_natCast, ← zpow_add₀ (by positivity)]
            congr 1
            push_cast; ring
      funext i
      have h5 := (Padic.norm_int_le_pow_iff_dvd (p := l) _ r).1 ((norm_le_pi_norm d i).trans h3)
      apply Fin.ext
      have h6 : ((c i : ℕ) : ℤ) - ((c' i : ℕ) : ℤ) = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd h5
        have e1 : ((c i : ℕ) : ℤ) < (l : ℤ) ^ r := by exact_mod_cast (c i).2
        have e2 : ((c' i : ℕ) : ℤ) < (l : ℤ) ^ r := by exact_mod_cast (c' i).2
        rw [abs_lt]
        constructor <;> omega
      omega
    have h7 := (Nat.card_le_card_of_injective F hF).trans hcard
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin] at h7
    have h8 : l ^ r * l ^ (r * n) ≤ (C * l ^ (v * n)) * l ^ (r * n) := by
      calc l ^ r * l ^ (r * n) = (l ^ r) ^ (n + 1) := by ring
        _ ≤ _ := h7
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h8 (pow_pos hl.pos _)
  have h9 := key (C * l ^ (v * n) + 1) (Nat.succ_pos _)
  have h10 : C * l ^ (v * n) + 1 < l ^ (C * l ^ (v * n) + 1) := Nat.lt_pow_self hl.one_lt
  omega

end GlobalTheory.Cyc.CocycleCount
