import ReciprocityTheory.Chebotarev.KHoldA
import ReciprocityTheory.Chebotarev.CTrick
import ReciprocityTheory.Chebotarev.PowerSeriesDiagonalLinear

open NumberField NumberField.Units Filter Topology Set

open scoped Classical

namespace ReciprocityTheory.Cheb

theorem summable_gfun {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (c : NZIdeal E) {s : ℝ} (hs : 1 < s) : Summable (gfun χ c s) := by
  have h1 := affine_proper_base_change.1 E (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l))
    (fun a => DirichletCharacter.norm_le_one χ _) s hs
  have h2 := affine_proper_base_change.1 E (fun a => if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0)
    (fun a => by split_ifs <;> simp [DirichletCharacter.norm_le_one]) s hs
  refine (h1.sub (h2.mul_left (Ideal.absNorm c.1 : ℂ))).congr fun a => ?_
  simp only [gfun]
  split_ifs <;> ring

theorem tsum_gfun {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (c : NZIdeal E) {s : ℝ} (hs : 1 < s) :
    ∑' a, gfun χ c s a = Lser E χ s * (1 - (Ideal.absNorm c.1 : ℂ) *
      (χ ((Ideal.absNorm c.1 : ℕ) : ZMod l) * ((Ideal.absNorm c.1 : ℕ) : ℂ) ^ (-(s : ℂ)))) := by
  have h1 := affine_proper_base_change.1 E (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l))
    (fun a => DirichletCharacter.norm_le_one χ _) s hs
  have h2 := affine_proper_base_change.1 E (fun a => if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0)
    (fun a => by split_ifs <;> simp [DirichletCharacter.norm_le_one]) s hs
  have hd := tsum_dvd_eq χ c hs
  have e : (fun a => gfun χ c s a) = fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) *
      ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) - (Ideal.absNorm c.1 : ℂ) *
      ((if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0) *
        ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) := by
    funext a; simp only [gfun]; split_ifs <;> ring
  have e2 : (fun a : NZIdeal E => (if c.1 ∣ a.1 then χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) else 0) *
        ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) = fun a => if c.1 ∣ a.1 then
        χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) else 0 := by
    funext a; split_ifs <;> simp
  rw [e, h1.tsum_sub (h2.mul_left _), tsum_mul_left, e2, hd]
  simp only [Lser]
  ring

theorem k_holds : KProp := by
  intro E _ _ l _ hirr χ hχ
  choose b hb using fun C : ClassGroup (𝓞 E) => exists_cls_eq (E := E) C⁻¹
  have hM : (∏ C, Ideal.absNorm (b C).1) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun C _ => by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (b C).2
  obtain ⟨q, hqcop, hqχ⟩ := chebyshev_split_estimate E l hirr χ hχ _ hM
  let c : NZIdeal E := ⟨q.asIdeal, q.ne_bot⟩
  have hcop : ∀ C, Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm (b C).1) := fun C =>
    Nat.Coprime.coprime_dvd_right (by
      rw [mul_comm l]
      exact Nat.mul_dvd_mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ C)) l) hqcop
  choose F hF hFeq using fun C => exists_class_cont χ (b C) c (hcop C)
  set n : ℕ := Ideal.absNorm c.1 with hn
  have hn0 : n ≠ 0 := by rw [hn, Ne, Ideal.absNorm_eq_zero_iff]; exact c.2
  set D : ℝ → ℂ := fun s => ∑ C, ((torsionOrder E : ℕ) : ℂ)⁻¹ *
    ((Ideal.absNorm (b C).1 : ℕ) : ℂ) ^ (s : ℂ) * F C s with hD
  set den : ℝ → ℂ := fun s => 1 - (n : ℂ) * (χ (n : ZMod l) * (n : ℂ) ^ (-(s : ℂ))) with hden
  have hid : ∀ s ∈ Ioc (1 : ℝ) 2, Lser E χ s * den s = D s := by
    intro s hs
    rw [hden, hD]
    dsimp only
    rw [hn, ← tsum_gfun χ c hs.1, tsum_eq_sum_cls _ (summable_gfun χ c hs.1)]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [← hFeq C s hs (summable_gfun χ c hs.1)]
    congr 1; funext a
    rw [hb C, mul_inv_eq_one]
  have hDc : ContinuousOn D (Icc 1 2) := by
    refine continuousOn_finsetSum _ fun C _ => ?_
    refine ContinuousOn.mul (Continuous.continuousOn ?_) (hF C)
    refine continuous_const.mul (Continuous.const_cpow Complex.continuous_ofReal (Or.inl ?_))
    have : Ideal.absNorm (b C).1 ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (b C).2
    exact_mod_cast this
  have hdenc : Continuous den := continuous_const.sub (continuous_const.mul (continuous_const.mul
    (Continuous.const_cpow Complex.continuous_ofReal.neg (Or.inl (by exact_mod_cast hn0)))))
  have hden1 : den 1 ≠ 0 := by
    rw [hden]
    dsimp only
    rw [Complex.ofReal_one, Complex.cpow_neg_one, mul_left_comm, mul_inv_cancel₀ (by exact_mod_cast hn0),
      mul_one, sub_ne_zero]
    exact fun h => hqχ h.symm
  refine ⟨D 1 / den 1, ?_⟩
  have hcw : ContinuousWithinAt (fun s => D s / den s) (Icc 1 2) 1 :=
    (hDc 1 ⟨le_rfl, by norm_num⟩).div hdenc.continuousWithinAt hden1
  have ht : Tendsto (fun s => D s / den s) (𝓝[>] 1) (𝓝 (D 1 / den 1)) :=
    (hcw.mono_of_mem_nhdsWithin (mem_of_superset (Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2))
      Ioc_subset_Icc_self)).tendsto
  refine ht.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (1 : ℝ) < 2),
    nhdsWithin_le_nhds (hdenc.continuousAt.eventually_ne hden1)] with s hs hs0
  rw [div_eq_iff hs0, hid s hs]

end ReciprocityTheory.Cheb
