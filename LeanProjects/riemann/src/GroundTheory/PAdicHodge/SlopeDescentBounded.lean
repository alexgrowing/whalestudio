import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaEigenGlue
import GroundTheory.PAdicHodge.ExtRobbaLimit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem upperPart_eq_algebraMap (b : T.B) : ∃ w : Γ, T.upperPart b = algebraMap Γ T.B w := by
  obtain ⟨w, hw⟩ := T.mem_span_pow.1 (T.sub_partialSum_mem (T.num b) (T.den b))
  refine ⟨w, ?_⟩
  rw [upperPart, hw, map_mul, map_pow]
  calc algebraMap Γ T.B T.π ^ T.den b * algebraMap Γ T.B w * IsLocalization.Away.invSelf T.π ^ T.den b
      = algebraMap Γ T.B w * (algebraMap Γ T.B T.π * IsLocalization.Away.invSelf T.π) ^ T.den b := by
        ring
    _ = algebraMap Γ T.B w := by rw [IsLocalization.Away.mul_invSelf, one_pow, mul_one]

variable {T}

theorem gaussNorm_lowerPart_le_mul {b : T.B} (hb : T.ConvAll b) {r r' : ℝ} (h0 : 0 < r')
    (hle : r' ≤ r) (h1 : r' < 1) :
    gaussNorm (T.coeffB (T.lowerPart b)) r ≤ (r' / r) * gaussNorm (T.coeffB b) r' := by
  have hr0 : 0 < r := h0.trans_le hle
  refine gaussNorm_le fun n => ?_
  rw [coeffB_lowerPart]
  split_ifs with hn
  · have hq : 1 ≤ r / r' := (one_le_div h0).2 hle
    have hpow : (r / r') ^ n ≤ (r / r') ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq (by omega)
    rw [zpow_neg_one, inv_div] at hpow
    have h3 : r ^ n ≤ (r' / r) * r' ^ n := by
      calc r ^ n = (r / r') ^ n * r' ^ n := by
            rw [div_zpow, div_mul_cancel₀ _ (zpow_pos h0 n).ne']
        _ ≤ (r' / r) * r' ^ n := mul_le_mul_of_nonneg_right hpow (zpow_pos h0 n).le
    calc ‖T.coeffB b n‖ * r ^ n ≤ ‖T.coeffB b n‖ * ((r' / r) * r' ^ n) :=
          mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = (r' / r) * (‖T.coeffB b n‖ * r' ^ n) := by ring
      _ ≤ (r' / r) * gaussNorm (T.coeffB b) r' :=
          mul_le_mul_of_nonneg_left ((hb r' h0 h1).le_gaussNorm n) (by positivity)
  · rw [norm_zero, zero_mul]; exact mul_nonneg (by positivity) (gaussNorm_nonneg h0)

theorem exists_rpow_small {σ γ C η : ℝ} (hσ : 0 < σ) (hγ : 0 < γ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ t, 0 < t ∧ t ≤ σ ∧ C * t ^ γ ≤ η := by
  set a : ℝ := η / (C + 1) with ha
  have ha0 : 0 < a := by positivity
  refine ⟨min σ (a ^ γ⁻¹), lt_min hσ (Real.rpow_pos_of_pos ha0 _), min_le_left _ _, ?_⟩
  have ht0 : 0 ≤ min σ (a ^ γ⁻¹) := (lt_min hσ (Real.rpow_pos_of_pos ha0 _)).le
  have h1 : (min σ (a ^ γ⁻¹)) ^ γ ≤ a := by
    calc (min σ (a ^ γ⁻¹)) ^ γ ≤ (a ^ γ⁻¹) ^ γ :=
          Real.rpow_le_rpow ht0 (min_le_right _ _) hγ.le
      _ = a := Real.rpow_inv_rpow ha0.le hγ.ne'
  calc C * (min σ (a ^ γ⁻¹)) ^ γ ≤ C * a := mul_le_mul_of_nonneg_left h1 hC
    _ ≤ (C + 1) * a := by nlinarith
    _ = η := by rw [ha]; field_simp

theorem exists_gamma_of_extNorm_le [CompleteSpace L] {σ : Set.Ioo (0 : ℝ) 1} (x : T.RobbaExt σ) {C β : ℝ} (b : ℕ)
    (hb : β - 1 < b) (hx : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s x ≤ C * (s : ℝ) ^ (-β)) :
    ∃ w : Γ, ∃ hw : algebraMap Γ T.B w ∈ T.Econ σ,
      T.ofAll _ (convAll_π_pow b) σ * x = ((⟨algebraMap Γ T.B w, hw⟩ : T.Econ σ) : T.RobbaExt σ) := by
  have hσ0 : (0 : ℝ) < σ := σ.2.1
  have hσ1 : (σ : ℝ) < 1 := σ.2.2
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set y := T.ofAll _ (convAll_π_pow b) σ * x with hydef

  have hy : ∀ s : Set.Ioc (0 : ℝ) σ, T.extNorm σ s y ≤ C' * (s : ℝ) ^ ((b : ℝ) - β) := by
    intro s
    have hs0 : (0 : ℝ) < s := s.2.1
    rw [hydef, extNorm_mul, extNorm_ofAll, (gaussNorm_π_pow b hs0).2]
    have hxs : T.extNorm σ s x ≤ C' * (s : ℝ) ^ (-β) :=
      (hx s).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs0.le _))
    calc (s : ℝ) ^ b * T.extNorm σ s x ≤ (s : ℝ) ^ b * (C' * (s : ℝ) ^ (-β)) :=
          mul_le_mul_of_nonneg_left hxs (pow_nonneg hs0.le _)
      _ = C' * ((s : ℝ) ^ (b : ℝ) * (s : ℝ) ^ (-β)) := by rw [Real.rpow_natCast]; ring
      _ = C' * (s : ℝ) ^ ((b : ℝ) - β) := by rw [← Real.rpow_add hs0, sub_eq_add_neg]

  let r : ℕ → Set.Ioc (0 : ℝ) σ := fun j =>
    ⟨σ / (j + 1), by positivity, div_le_self hσ0.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])⟩
  let ε : ℕ → ℝ := fun j => 1 / (j + 1)
  have hε0 : ∀ j, 0 < ε j := fun j => by positivity
  choose d hd hdx using fun j : ℕ => exists_approx_convAll y (r j) (hε0 j)
  choose w hw using fun j => T.upperPart_eq_algebraMap (d j)
  have hr_anti : ∀ {j k : ℕ}, j ≤ k → ((r k : ℝ)) ≤ r j := fun {j k} hjk => by
    show σ / ((k : ℝ) + 1) ≤ σ / ((j : ℝ) + 1)
    exact div_le_div_of_nonneg_left hσ0.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hε_anti : ∀ {j k : ℕ}, j ≤ k → ε k ≤ ε j := fun {j k} hjk => by
    show 1 / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1)
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hsmall : ∀ η > (0 : ℝ), ∀ t > (0 : ℝ), ∃ J, ∀ j ≥ J, (r j : ℝ) ≤ t ∧ ε j ≤ η := by
    intro η hη t ht
    obtain ⟨J, hJ⟩ := exists_nat_gt (max (σ / t) (1 / η))
    refine ⟨J, fun j hj => ⟨?_, ?_⟩⟩
    · refine (hr_anti hj).trans ?_
      show σ / ((J : ℝ) + 1) ≤ t
      rw [div_le_iff₀ (by positivity)]
      have : σ / t < J := lt_of_le_of_lt (le_max_left _ _) hJ
      rw [div_lt_iff₀ ht] at this
      nlinarith
    · refine (hε_anti hj).trans ?_
      show 1 / ((J : ℝ) + 1) ≤ η
      rw [div_le_iff₀ (by positivity)]
      have : 1 / η < J := lt_of_le_of_lt (le_max_right _ _) hJ
      rw [div_lt_iff₀ hη] at this
      nlinarith

  have hdt : ∀ j (t : Set.Ioc (0 : ℝ) σ), (r j : ℝ) ≤ t →
      gaussNorm (T.coeffB (d j)) t ≤ max (C' * (t : ℝ) ^ ((b : ℝ) - β)) (ε j) := by
    intro j t ht
    rw [← extNorm_ofAll (hd j) t]
    have e : T.ofAll (d j) (hd j) σ = y + -(y - T.ofAll (d j) (hd j) σ) := by ring
    rw [e]
    refine (T.extNorm_add_le t _ _).trans (max_le_max (hy t) ?_)
    rw [extNorm_neg]; exact hdx j t ht

  have hA : ∀ η > (0 : ℝ), ∃ J, ∀ j ≥ J, gaussNorm (T.coeffB (T.lowerPart (d j))) σ ≤ η := by
    intro η hη
    have hγ : 0 < (b : ℝ) - β + 1 := by linarith
    obtain ⟨t, ht0, htσ, htC⟩ := exists_rpow_small hσ0 hγ (div_nonneg hC'0 hσ0.le) hη
    obtain ⟨J, hJ⟩ := hsmall η hη t ht0
    refine ⟨J, fun j hj => ?_⟩
    obtain ⟨hrj, hεj⟩ := hJ j hj
    have h1 := gaussNorm_lowerPart_le_mul (hd j) ht0 htσ (htσ.trans_lt hσ1)
    have h2 := hdt j ⟨t, ht0, htσ⟩ hrj
    refine h1.trans ?_
    have htσ' : t / σ ≤ 1 := (div_le_one hσ0).2 htσ
    calc t / σ * gaussNorm (T.coeffB (d j)) t
        ≤ t / σ * max (C' * t ^ ((b : ℝ) - β)) (ε j) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ max (C' / σ * t ^ ((b : ℝ) - β + 1)) (ε j) := by
          rw [mul_max_of_nonneg _ _ (by positivity)]
          refine max_le_max (le_of_eq ?_) ?_
          · rw [Real.rpow_add ht0, Real.rpow_one]; field_simp
          · calc t / σ * ε j ≤ 1 * ε j := mul_le_mul_of_nonneg_right htσ' (hε0 j).le
              _ = ε j := one_mul _
      _ ≤ η := max_le htC hεj

  have hup : ∀ j, T.ConvAll (algebraMap Γ T.B (w j)) := fun j => by
    rw [← hw j]; exact (hd j).upperPart
  have hconv : ∀ j, ConvergesAt (T.zcoeff (w j)) σ := fun j => by
    have := hup j σ hσ0 hσ1
    rwa [coeffB_algebraMap] at this
  have hsplit : ∀ j, T.ofAll (d j) (hd j) σ =
      T.ofAll _ (hd j).lowerPart σ + T.ofAll _ (hup j) σ := by
    intro j
    rw [← ofAll_add]
    exact ofAll_congr _ _ (by rw [← hw j, lowerPart_add_upperPart]) σ
  have hwsub : ∀ j k, gaussNorm (T.zcoeff (w j - w k)) σ =
      T.extNorm σ (topRad σ) (T.ofAll _ (hup j) σ - T.ofAll _ (hup k) σ) := by
    intro j k
    rw [← gaussNorm_ofAll_sub (hup j) (hup k), ← map_sub, coeffB_algebraMap]
    rfl

  have hB : ∀ η > (0 : ℝ), ∃ N, ∀ j ≥ N, ∀ k ≥ N, gaussNorm (T.zcoeff (w j - w k)) σ ≤ η := by
    intro η hη
    obtain ⟨J1, hJ1⟩ := hA η hη
    obtain ⟨J2, hJ2⟩ := hsmall η hη σ hσ0
    refine ⟨max J1 J2, fun j hj k hk => ?_⟩
    rw [hwsub]
    have e : T.ofAll _ (hup j) σ - T.ofAll _ (hup k) σ =
        -(y - T.ofAll (d j) (hd j) σ) + (y - T.ofAll (d k) (hd k) σ) +
          (T.ofAll _ (hd k).lowerPart σ - T.ofAll _ (hd j).lowerPart σ) := by
      rw [hsplit j, hsplit k]; ring
    rw [e]
    have hlow : ∀ i ≥ J1, T.extNorm σ (topRad σ) (T.ofAll _ (hd i).lowerPart σ) ≤ η := fun i hi => by
      rw [extNorm_ofAll]; exact hJ1 i hi
    have happ : ∀ i ≥ J2, T.extNorm σ (topRad σ) (y - T.ofAll (d i) (hd i) σ) ≤ η := fun i hi =>
      (hdx i (topRad σ) (hJ2 i hi).1).trans (hJ2 i hi).2
    refine (extNorm_add_add_le_max _ _ _ _).trans (max_le ?_ (max_le ?_ ?_))
    · rw [extNorm_neg]; exact happ j (le_of_max_le_right hj)
    · exact happ k (le_of_max_le_right hk)
    · rw [sub_eq_add_neg]
      refine (T.extNorm_add_le _ _ _).trans (max_le (hlow k (le_of_max_le_left hk)) ?_)
      rw [extNorm_neg]; exact hlow j (le_of_max_le_left hj)

  obtain ⟨-, hWc, hWlim⟩ := T.exists_limit_gaussNorm hσ0 hσ1 hconv hB
  set W := T.coeffLim w with hWdef
  have hWE : algebraMap Γ T.B W ∈ T.Econ σ := by
    rw [mem_Econ, coeffB_algebraMap]; exact hWc
  refine ⟨W, hWE, ?_⟩

  rw [← sub_eq_zero, ← T.extNorm_eq_zero_iff (topRad σ)]
  refine le_antisymm (le_of_forall_pos_le_add fun η hη => ?_) (T.extNorm_nonneg _ _)
  rw [zero_add]
  obtain ⟨J1, hJ1⟩ := hA η hη
  obtain ⟨J2, hJ2⟩ := hsmall η hη σ hσ0
  obtain ⟨J3, hJ3⟩ := hWlim η hη
  set j := max J1 (max J2 J3)
  have e : y - ((⟨algebraMap Γ T.B W, hWE⟩ : T.Econ σ) : T.RobbaExt σ) =
      (y - T.ofAll (d j) (hd j) σ) + T.ofAll _ (hd j).lowerPart σ +
        (T.ofAll _ (hup j) σ - ((⟨algebraMap Γ T.B W, hWE⟩ : T.Econ σ) : T.RobbaExt σ)) := by
    rw [hsplit j]; ring
  rw [e]
  refine (extNorm_add_add_le_max _ _ _ _).trans (max_le ?_ (max_le ?_ ?_))
  · exact (hdx j (topRad σ) (hJ2 j (le_max_of_le_right (le_max_left _ _))).1).trans
      (hJ2 j (le_max_of_le_right (le_max_left _ _))).2
  · rw [extNorm_ofAll]; exact hJ1 j (le_max_left _ _)
  · rw [ofAll, ← Completion.coe_sub, extNorm_coe]
    have := hJ3 j (le_max_of_le_right (le_max_right _ _))
    rw [← coeffB_algebraMap, map_sub] at this
    exact this

end TeichLift

end GroundTheory.PAdicHodge
