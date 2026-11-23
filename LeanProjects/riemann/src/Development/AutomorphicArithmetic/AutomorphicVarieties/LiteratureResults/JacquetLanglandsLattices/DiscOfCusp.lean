import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LocF
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.JacquetLanglandsLattices.ExistsIntertwinerIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar
import GroundTheory.AutomorphicForms.ReductionIdele
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.BasicNotions GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.JL

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.Reduction in

private theorem UpperTheory.V.Lit.JL.add_prop (F : Type) [Field F] [NumberField F] (f g : Ideles F → ℝ)
    (fc : Continuous f) (gc : Continuous g) (fm : ∀ a b, f (a * b) = f a + f b) (gm : ∀ a b, g (a * b) = g a + g b)
    (fd : ∀ k, f (diagUnits F k) = 0) (gd : ∀ k, g (diagUnits F k) = 0) (z₀ : Ideles F) (h₀ : g z₀ ≠ 0) :
    ∃ s : ℝ, ∀ z, f z = s * g z := by
  have key : ∀ h : Ideles F → ℝ, Continuous h → (∀ a b, h (a * b) = h a + h b) → (∀ k, h (diagUnits F k) = 0) →
      ∀ (b : ℝ) (z y : Ideles F), h y = 0 →
      (∀ n : ℕ, ∃ k : ℤ, 1 ≤ (ideleModule F (z ^ n * y ^ k) : ℝ) ∧ (ideleModule F (z ^ n * y ^ k) : ℝ) ≤ b) → h z = 0 := by
    intro h hc hm hd b z y hy hb
    let H : Ideles F →* Multiplicative ℝ := MonoidHom.mk' (fun a => Multiplicative.ofAdd (h a))
      fun a b => by rw [hm]; rfl
    have hp : ∀ (a : Ideles F) (k : ℤ), h (a ^ k) = k * h a := fun a k => by
      have := congrArg Multiplicative.toAdd (map_zpow H a k)
      simpa [H] using this
    obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos b
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (f := h) hc.continuousOn
    have hn : ∀ n : ℕ, (n : ℝ) * |h z| ≤ B := fun n => by
      obtain ⟨k, h1, h2⟩ := hb n
      obtain ⟨c, hc'⟩ := hSm _ h1 h2
      have h3 := hB _ hc'
      have h4 : h (diagonal F c) = 0 := hd c
      rw [hm, h4, hm, ← zpow_natCast, hp, hp, hy] at h3
      simpa [abs_mul] using h3
    by_contra hz
    obtain ⟨n, hn'⟩ := exists_nat_gt (B / |h z|)
    rw [div_lt_iff₀ (abs_pos.2 hz)] at hn'
    exact absurd (hn n) (not_le.2 hn')
  have g1 : g 1 = 0 := by simpa using gd 1
  have hm1 : (ideleModule F z₀ : ℝ) ≠ 1 := fun e => h₀ (key g gc gm gd 1 z₀ 1 g1 fun n => ⟨0, by
    have : (ideleModule F (z₀ ^ n * 1 ^ (0 : ℤ)) : ℝ) = 1 := by
      rw [zpow_zero, mul_one, map_pow, Positive.val_pow, e, one_pow]
    exact ⟨this.ge, this.le⟩⟩)
  let M : Ideles F →* ℝ := (MonoidHom.mk ⟨fun x : {r : ℝ // 0 < r} => (x : ℝ), rfl⟩ fun _ _ => rfl).comp (ideleModule F)
  have hM : ∀ x, M x = (ideleModule F x : ℝ) := fun _ => rfl
  have hpos : ∀ x, 0 < M x := fun x => (ideleModule F x).2
  have hinv : ∀ x, M x⁻¹ = (M x)⁻¹ := fun x => by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel, map_one]
  have hz : ∀ x (k : ℤ), M (x ^ k) = M x ^ k := fun x k => by
    cases k with
    | ofNat n => simp
    | negSucc n => simp [hinv]
  obtain ⟨y, hy, hy1⟩ : ∃ y, g y ≠ 0 ∧ 1 < M y := by
    rcases lt_or_gt_of_ne hm1 with h | h
    · refine ⟨z₀⁻¹, fun e => h₀ ?_, ?_⟩
      · have := gm z₀ z₀⁻¹
        rw [mul_inv_cancel, g1, e] at this
        linarith
      · rw [hinv]; exact (one_lt_inv₀ (hpos _)).2 h
    · exact ⟨z₀, h₀, h⟩
  refine ⟨f y / g y, fun z => sub_eq_zero.1 (key (fun z => f z - f y / g y * g z) (fc.sub (gc.const_mul _))
    (fun a b => by simp only [fm, gm]; ring) (fun k => by simp [fd, gd]) (M y) z y (by field_simp; ring) fun n => ?_)⟩
  obtain ⟨k, h1, h2⟩ := exists_mem_Ico_zpow (hpos (z ^ n)) hy1
  have hy0 := hpos y
  refine ⟨-k, ?_, ?_⟩
  · rw [← hM, map_mul, hz, zpow_neg, ← div_eq_mul_inv, one_le_div (zpow_pos hy0 _)]
    exact h1
  · rw [← hM, map_mul, hz, zpow_neg, ← div_eq_mul_inv, div_le_iff₀ (zpow_pos hy0 _), mul_comm, ← zpow_add_one₀ hy0.ne']
    exact h2.le

open GlobalTheory.Mem.Chr.CharModel in

private theorem UpperTheory.V.Lit.JL.abs_pow (F : Type) [Field F] [NumberField F] (ω : HChar F) :
    ∃ s : ℝ, ∀ z, ‖((ω.1 z : ℂˣ) : ℂ)‖ = Real.exp (s * logNorm F z) := by
  obtain ⟨z₀, h₀⟩ : ∃ z₀, logNorm F z₀ ≠ 0 := by
    by_contra hn
    push Not at hn
    refine absChar_not_unitary (F := F) fun z => ?_
    change ‖Complex.exp (1 * logNorm F z)‖ = 1
    simp [hn]
  have hne : ∀ z, ‖((ω.1 z : ℂˣ) : ℂ)‖ ≠ 0 := fun z => norm_ne_zero_iff.2 (Units.ne_zero _)
  obtain ⟨s, hs⟩ := add_prop F (fun z => Real.log ‖((ω.1 z : ℂˣ) : ℂ)‖) (logNorm F)
    ((Units.continuous_val.comp ω.2.1).norm.log hne) (continuous_logNorm F)
    (fun a b => by rw [map_mul, Units.val_mul, norm_mul, Real.log_mul (hne a) (hne b)]) (logNorm_mul F)
    (fun k => by rw [ω.2.2 k]; simp) (logNorm_principal F) z₀ h₀
  exact ⟨s, fun z => by rw [← hs, Real.exp_log (norm_pos_iff.2 (Units.ne_zero _))]⟩
