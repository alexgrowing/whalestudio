import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.StagePow

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem stage1_succ (c : ℕ) (hc : c ≠ 0) (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    ∃ ξ' : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)), ξ'.2.IsPrimitive ∧ ξ'.1 + 1 = c ∧
      ∀ n : ℕ, ξ'.2 (n : ZMod (ξ'.1 + 1)) = χ (n : ZMod c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  exact ⟨⟨k, χ⟩, hχ, rfl, fun _ => rfl⟩

private theorem stage1_prim (N₀ : ℕ) (hN : 0 < N₀) (ξ : DirichletCharacter ℂ N₀) :
    ∃ ξ' : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)), ξ'.2.IsPrimitive ∧ ξ'.1 + 1 ≤ N₀ ∧
      ∀ n : ℕ, n.Coprime N₀ → ξ'.2 (n : ZMod (ξ'.1 + 1)) = ξ (n : ZMod N₀) := by
  haveI : NeZero N₀ := ⟨hN.ne'⟩
  obtain ⟨ξ', h1, h2, h3⟩ := stage1_succ ξ.conductor (DirichletCharacter.conductor_ne_zero ξ)
    ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive
  refine ⟨ξ', h1, h2 ▸ Nat.le_of_dvd hN ξ.conductor_dvd_level, fun n hn => ?_⟩
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ξ.primitiveCharacter ξ.conductor_dvd_level
    (ZMod.unitOfCoprime n hn)
  rw [DirichletCharacter.changeLevel_primitiveCharacter, ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast ξ.conductor_dvd_level] at h
  rw [h3, h]

private theorem stage1_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in Filter.atTop, Real.log Y ^ 2 ≤ 1 / 2 * Y ^ (ε / 5) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show 0 < ε / 5 by positivity)).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [h, Filter.eventually_gt_atTop (0 : ℝ)] with Y hY hY0
  rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hY0.le _)] at hY
  exact hY

theorem stage1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε τ K η : ℝ) (N₀ : ℕ), 0 < ε → ε < 1 / 52 → 0 < τ → 1 ≤ K → 0 < η → 0 < N₀ → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀,
      (primePairSetFirst (Y ^ (ε / 5))).Nonempty ∧ ∀ B ⊆ primePairSetFirst (Y ^ (ε / 5)),
        (∀ q ∈ B, ¬ GoodQ N₀ C τ Y (Y ^ K) (Y ^ (ε / 5)) q) → (B.card : ℝ) ≤ η * (primePairSetFirst (Y ^ (ε / 5))).card := by
  classical
  obtain ⟨C, hC, hst⟩ := stage
  refine ⟨C, hC, fun ε τ K η N₀ hε hε' hτ hK hη hN => ?_⟩
  haveI : NeZero N₀ := ⟨hN.ne'⟩
  haveI : Fintype (DirichletCharacter ℂ N₀) := Fintype.ofFinite _
  choose g hg1 hg2 hg3 using stage1_prim N₀ hN
  obtain ⟨Y₁, hY₁⟩ := hst ε τ K η (Fintype.card (DirichletCharacter ℂ N₀)) hε (by linarith) hτ hK hη
  obtain ⟨Y₂, hY₂⟩ := Filter.eventually_atTop.1 ((stage1_log hε).and
    (((tendsto_rpow_atTop (show 0 < ε / 5 by positivity)).eventually_ge_atTop (2 * N₀ : ℝ)).and
    ((Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)).and (Filter.eventually_ge_atTop (1 : ℝ)))))
  refine ⟨max Y₁ Y₂, fun Y hY => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hY
  obtain ⟨hlog, hz, hl1, hY1⟩ := hY₂ Y hY.2
  have hN1 : (1 : ℝ) ≤ N₀ := by exact_mod_cast hN
  have hz0 : 0 ≤ Y ^ (ε / 5) := by linarith
  have hA : admitted ε Y (Real.exp (Y ^ (ε / 5))) 8 3 := by
    refine ⟨by norm_num, dvd_rfl, by norm_num, ?_, ?_, ?_⟩
    · rw [Real.log_exp]
      have h8 : Real.log ((8 : ℕ) : ℝ) ≤ 8 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((8 : ℕ) : ℝ) by norm_num)
        push_cast at this ⊢
        linarith
      have := mul_le_mul_of_nonneg_left h8 (sq_nonneg (Real.log Y))
      generalize Real.log ((8 : ℕ) : ℝ) = l at this ⊢
      linarith
    · rw [Real.log_exp]
      exact Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    · rw [Real.log_exp]
      exact le_mul_of_one_le_right hz0 (one_le_pow₀ hl1)
  have hp : ∀ p : ℕ, p.Prime → p ∣ 8 → (p : ℝ) ≤ Y ^ (ε / 5) ∨ (Y ^ K) ^ 400 < (p : ℝ) := by
    intro p hp hd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 3) (by simpa using hd)
    have : (p : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_dvd two_pos h2
    left
    linarith
  have hFU : (N₀ : ℝ) ≤ Real.exp (Y ^ (ε / 5)) ^ (1 / 2 : ℝ) := by
    rw [← Real.exp_mul]
    have := Real.add_one_le_exp (Y ^ (ε / 5) * (1 / 2))
    linarith
  obtain ⟨hne, hB⟩ := hY₁ Y hY.1 (Real.exp (Y ^ (ε / 5))) N₀ 8 3 (Finset.univ.image g) hA hp hN1 hFU
    (Finset.card_image_le.trans Finset.card_univ.le) (by
      intro ξ hξ
      obtain ⟨χ, -, rfl⟩ := Finset.mem_image.1 hξ
      exact ⟨hg1 χ, by exact_mod_cast hg2 χ⟩)
  refine ⟨hne, fun B hBs hbad => hB B hBs fun q hq => ?_⟩
  have hqp : q.Prime := (Finset.mem_filter.1 (hBs hq)).2.1
  have hb := hbad q hq
  unfold GoodQ at hb
  obtain ⟨χ, hχ⟩ := not_forall.1 hb
  refine ⟨g χ, Finset.mem_image_of_mem _ (Finset.mem_univ _), N₀ * q,
    mul_ne_zero hN.ne' hqp.ne_zero, fun h => hχ ?_⟩
  intro N _ ψ hI
  refine h N ψ ⟨hI.1, fun n hn => ?_⟩
  rw [hI.2 n hn]
  simp only
  rw [hg3 χ n (Nat.Coprime.coprime_mul_right_right hn)]

end QH
