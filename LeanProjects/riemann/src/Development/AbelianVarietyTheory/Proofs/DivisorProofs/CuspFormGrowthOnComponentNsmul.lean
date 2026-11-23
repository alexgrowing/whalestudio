import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupShiftLe

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Filter
open scoped ENNReal NNReal

namespace GlobalTheory.GrowthMul

theorem limsup_le_iSup_classes {a : ℕ} (ha : 1 ≤ a) (f : ℕ → ℝ≥0∞) :
    limsup f atTop ≤ ⨆ j : Fin a, limsup (fun k => f (a * k + j)) atTop := by
  refine le_of_forall_gt_imp_ge_of_dense fun x hx => ?_
  have h1 : ∀ j : Fin a, ∀ᶠ k in atTop, f (a * k + j) < x := fun j =>
    eventually_lt_of_limsup_lt ((le_iSup (fun j : Fin a => limsup (fun k => f (a * k + j)) atTop) j).trans_lt hx)
  choose K hK using fun j => eventually_atTop.1 (h1 j)
  refine limsup_le_of_le (by isBoundedDefault) (eventually_atTop.2 ⟨a * Finset.univ.sup K, fun τ hτ => ?_⟩)
  have hm : τ % a < a := Nat.mod_lt _ (by omega)
  have hq : Finset.univ.sup K ≤ τ / a := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hτ)
  have := hK ⟨τ % a, hm⟩ (τ / a) ((Finset.le_sup (Finset.mem_univ _)).trans hq)
  rw [Nat.div_add_mod] at this
  exact this.le

theorem term_mul_eq (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) {k : ℕ} (hk : 1 ≤ k) :
    (D.factorial : ℝ≥0∞) * (r (a * k) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D =
      (a : ℝ≥0∞) ^ D * ((D.factorial : ℝ≥0∞) * (r (a * k) : ℝ≥0∞) / ((a * k : ℕ) : ℝ≥0∞) ^ D) := by
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  rw [Nat.cast_mul, mul_pow, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ ha0 hat, mul_comm]

theorem growth_mul_le (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) :
    growth D (fun k => r (a * k)) ≤ (a : ℝ≥0∞) ^ D * growth D r := by
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  set g : ℕ → ℝ≥0∞ := fun τ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D
  have h1 : growth D (fun k => r (a * k)) = limsup (fun k => (a : ℝ≥0∞) ^ D * g (a * k)) atTop :=
    limsup_congr ((eventually_ge_atTop 1).mono fun k hk => term_mul_eq D ha r hk)
  rw [h1, ENNReal.limsup_const_mul_of_ne_top hat, growth]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le)
  have ht : Tendsto (fun k : ℕ => a * k) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  exact (limsup_comp g (fun k => a * k) atTop).le.trans (limsup_le_limsup_of_le ht)

theorem limsup_class_le (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) (j c : ℕ)
    (h : ∀ k, r (a * k + j) ≤ r (a * (k + c))) :
    limsup (fun k => (D.factorial : ℝ≥0∞) * (r (a * k + j) : ℝ≥0∞) / ((a * k + j : ℕ) : ℝ≥0∞) ^ D) atTop ≤
      ((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k)) := by
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hit : ((a : ℝ≥0∞) ^ D)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ha0
  refine (limsup_le_limsup ((eventually_ge_atTop 1).mono fun k hk => ?_)).trans
    ((ENNReal.limsup_const_mul_of_ne_top hit).le.trans (by gcongr; exact GlobalTheory.GrowthShift.growth_shift_le D c _))
  show _ ≤ ((a : ℝ≥0∞) ^ D)⁻¹ * ((D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D)
  have hk0 : (k : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hkt : (k : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have e : ((a : ℝ≥0∞) ^ D)⁻¹ * ((D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D) =
      (D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / ((a : ℝ≥0∞) ^ D * (k : ℝ≥0∞) ^ D) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl ha0) (Or.inl hat)]
    ring
  rw [e]
  refine ENNReal.div_le_div (by gcongr; exact h k) ?_
  rw [← mul_pow]
  gcongr
  exact_mod_cast Nat.le_add_right _ _

theorem growth_mul_eq_of_classes (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞)
    (h : ∀ j, j < a → ∃ c, ∀ k, r (a * k + j) ≤ r (a * (k + c))) :
    growth D (fun k => r (a * k)) = (a : ℝ≥0∞) ^ D * growth D r := by
  refine le_antisymm (growth_mul_le D ha r) ?_
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have h1 : growth D r ≤ ((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k)) := by
    refine (limsup_le_iSup_classes ha _).trans (iSup_le fun j => ?_)
    obtain ⟨c, hc⟩ := h j j.2
    exact limsup_class_le D ha r j c hc
  calc (a : ℝ≥0∞) ^ D * growth D r ≤ (a : ℝ≥0∞) ^ D * (((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k))) :=
        mul_le_mul_of_nonneg_left h1 zero_le
    _ = growth D (fun k => r (a * k)) := by rw [← mul_assoc, ENNReal.mul_inv_cancel ha0 hat, one_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem pow_mul_mem_cuspOn {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ₀ τ : ℕ} {g f : Rul Xo c}
    (hg : g ∈ cuspOn U Z (τ₀ • G)) (hf : f ∈ cuspOn U Z (τ • G)) (n : ℕ) :
    g ^ n * f ∈ cuspOn U Z ((τ + n * τ₀) • G) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have e : (τ + (n + 1) * τ₀) • G = (τ + n * τ₀) • G + τ₀ • G := by rw [← add_nsmul]; ring_nf
    rw [e, pow_succ, mul_right_comm]
    exact GlobalTheory.DegTop.mul_mem_cuspOn (GlobalTheory.DegTop.even_nsmul hG _) (GlobalTheory.DegTop.even_nsmul hG _) ih hg.1

theorem rank_le_of_ne_zero {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ₀ : ℕ} {g : Rul Xo c}
    (hg : g ∈ cuspOn U Z (τ₀ • G)) (hg0 : g ≠ 0) (τ n : ℕ) :
    Module.rank c.F (cuspOn U Z (τ • G)) ≤ Module.rank c.F (cuspOn U Z ((τ + n * τ₀) • G)) := by
  have hv : genVal Z g ≠ 0 := fun h0 => hg0 (GlobalTheory.DegTop.eq_zero_of_genVal hg h0)
  rw [← GlobalTheory.DegTop.rank_map_mul (U := U) (G := τ • G) (θ := g ^ n) (by rw [map_pow]; exact pow_ne_zero _ hv)]
  refine (Submodule.rank_mono ?_).trans (rank_map_le (genVal Z).toLinearMap _)
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨_, pow_mul_mem_cuspOn hG hg hf n, rfl⟩

theorem classes_bound (Z : Comp Xo c) {G : WTZ E} (hG : Even G.2) {a : ℕ} (ha : 1 ≤ a) (j : ℕ) :
    ∃ c' : ℕ, ∀ k, Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k + j) • G))) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * (k + c')) • G))) := by
  by_cases hex : ∃ q : ℕ, ∃ g ∈ cuspOn U Z ((a * q + j) • G), g ≠ 0
  · obtain ⟨q, g, hg, hg0⟩ := hex
    refine ⟨j + (a - 1) * q, fun k => ?_⟩
    have e : a * (k + (j + (a - 1) * q)) = (a * k + j) + (a - 1) * (a * q + j) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [e]
    exact OrderHomClass.mono Cardinal.toENat (rank_le_of_ne_zero hG hg hg0 _ _)
  · push_neg at hex
    refine ⟨0, fun k => ?_⟩
    have h0 : cuspOn U Z ((a * k + j) • G) = ⊥ := (Submodule.eq_bot_iff _).2 (hex k)
    rw [h0, rank_bot, map_zero]
    exact zero_le

end GlobalTheory.GrowthMul

theorem GlobalTheory.GrowthMul.growthOn_nsmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ a : ℕ, 1 ≤ a → growthOn U Z (a • G) = (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U _ Z G hG a ha
  rw [growthOn, growthOn]
  convert GlobalTheory.GrowthMul.growth_mul_eq_of_classes (dimFlag Dw) ha (fun τ => Cardinal.toENat (Module.rank c.F (cuspOn U Z (τ • G))))
    (fun j _ => GlobalTheory.GrowthMul.classes_bound (U := U) Z hG ha j) using 4 with τ
  rw [smul_smul, mul_comm]
