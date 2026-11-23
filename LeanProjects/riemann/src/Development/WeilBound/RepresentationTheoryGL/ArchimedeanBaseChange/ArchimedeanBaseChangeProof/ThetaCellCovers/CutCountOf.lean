import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.Rs
open scoped ENNReal Pointwise

namespace PositivityTheory.Rg.BcB.E1

attribute [local instance] borelH

theorem cntPair_of (h : RatProper) (ht : ThetaBasic) : CntPair := by
  intro E _ _ _ a b
  obtain ⟨a1, a2, a3⟩ := ht E a
  obtain ⟨b1, b2, b3⟩ := ht E b
  have inv : ∀ x : H E a b, th (th x) = x := fun x => Prod.ext (a2 _) (b2 _)
  refine ⟨fun Ω x => ?_, (a1.comp continuous_fst).prodMk (b1.comp continuous_snd), fun φ x y => ?_⟩
  · let f : ratH E a b → ratH E a b := fun γ => ⟨th γ.1, by
      obtain ⟨_, γ, rfl⟩ := γ
      exact ⟨(thetaE E a γ.1, thetaE E b γ.2), Prod.ext (a3 _).symm (b3 _).symm⟩⟩
    have hf : Function.Involutive f := fun γ => Subtype.ext (inv _)
    unfold cnt
    rw [← hf.toPerm.tsum_eq]
    refine tsum_congr fun γ => ?_
    have e : (th x)⁻¹ * ((hf.toPerm f γ : ratH E a b) : H E a b) * th x = th (x⁻¹ * γ.1 * x) :=
      Prod.ext (by simp [th, f]) (by simp [th, f])
    rw [e]
    by_cases hz : th (x⁻¹ * γ.1 * x) ∈ Ω
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show _ ∈ th '' Ω from ⟨_, hz, inv _⟩)]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem]
      rintro ⟨z, h1, h2⟩
      exact hz (by rw [← h2, inv]; exact h1)
  · refine finsum_eq_of_bijective ((ratGL E a).prodMap (ratGL E b)).rangeRestrict
      ⟨fun p q e => ?_, MonoidHom.rangeRestrict_surjective _⟩ fun _ => rfl
    have e' := congrArg Subtype.val e
    exact Prod.ext ((h E a).1 (congrArg Prod.fst e')) ((h E b).1 (congrArg Prod.snd e'))

theorem wtDiag_of (h : RatProper) (h1 : CntBasic) (h2 : WtCount) : WtDiag := by
  intro E _ _ _ a b D φ hφ M hM
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  have c₀ : ∀ x, ‖kerH φ x x‖ₑ ≤ ENNReal.ofReal B * cnt (ratH E a b) (tsupport φ) x := (h1 (ctx h D)).2.2.2 φ B hφ hB
  have c := h2 E a b D _ hφ.2 M hM
  refine lt_of_le_of_lt (lintegral_mono fun x => mul_le_mul_right (c₀ x) _) ?_
  simp only [mul_left_comm _ (ENNReal.ofReal B)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top c.lt_top

theorem zpow_aux {r x C : ℝ} (M : ℕ) (hr : 0 ≤ r) (hx : 0 ≤ x) (hC : 0 ≤ C) (h : x ≤ C * (1 + r)) :
    ((1 + r) ^ M)⁻¹ ≤ (1 + C) ^ M * (1 + x) ^ (-(M : ℤ)) := by
  rw [_root_.zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) M

theorem wtCount_of (h : RatProper) (h1 : CellSum) (h2 : CellCover) (h3 : RedBasic) (h4 : RedCell) (h5 : LatSum) :
    WtCount := by
  intro E _ _ _ a b D Ω hΩ M hM
  obtain ⟨Ω₁, k₁, c₁⟩ := h2 E a
  obtain ⟨Ω₂, k₂, c₂⟩ := h2 E b
  obtain ⟨C₁, p₁, r₁⟩ := h4 E a Ω₁ k₁
  obtain ⟨C₂, p₂, r₂⟩ := h4 E b Ω₂ k₂
  have key := h1 (ctx h D) ((Fin a → ℤ) × (Fin b → ℤ))
    (fun m => (An.tor E fun i => (m.1 i : ℝ), An.tor E fun i => (m.2 i : ℝ))) (Ω₁ ×ˢ Ω₂) Ω
    (fun x : H E a b => ENNReal.ofReal (wt x ^ (-(2 * M : ℤ))))
    (fun m => (ENNReal.ofReal ((1 + C₁) ^ M) * ENNReal.ofReal ((1 + ‖fun i => (m.1 i : ℝ)‖) ^ (-(M : ℤ)))) *
      (ENNReal.ofReal ((1 + C₂) ^ M) * ENNReal.ofReal ((1 + ‖fun i => (m.2 i : ℝ)‖) ^ (-(M : ℤ))))) (k₁.prod k₂) hΩ
    (fun x : H E a b => by
      obtain ⟨γ₁, m₁, o₁, q₁, e₁⟩ := c₁ x.1
      obtain ⟨γ₂, m₂, o₂, q₂, e₂⟩ := c₂ x.2
      exact ⟨_, ⟨(γ₁, γ₂), rfl⟩, (m₁, m₂), (o₁, o₂), ⟨q₁, q₂⟩, Prod.ext e₁ e₂⟩)
    (by
      rintro _ ⟨γ, rfl⟩ (x : H E a b)
      have e : wt (((ratGL E a).prodMap (ratGL E b)) γ * (x : H E a b)) = wt (x : H E a b) := by
        rw [wt_eq, wt_eq, ← (h3 E a).1 γ.1 x.1, ← (h3 E b).1 γ.2 x.2]
        rfl
      exact congrArg (fun t : ℝ => ENNReal.ofReal (t ^ (-(2 * M : ℤ)))) e)
    (by
      rintro m ⟨o₁, o₂⟩ ⟨q₁, q₂⟩
      have s₁ := ((h3 E a).2.1 (An.tor E (fun i => (m.1 i : ℝ)) * o₁)).1
      have s₂ := ((h3 E b).2.1 (An.tor E (fun i => (m.2 i : ℝ)) * o₂)).1
      have t₁ := zpow_aux M s₁ (norm_nonneg _) p₁ (r₁ _ o₁ q₁).1
      have t₂ := zpow_aux M s₂ (norm_nonneg _) p₂ (r₂ _ o₂ q₂).1
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ (mul_le_mul t₁ t₂ (by positivity) (by positivity)))
      change (1 + red (An.tor E (fun i => (m.1 i : ℝ)) * o₁ : GA E a) + red (An.tor E (fun i => (m.2 i : ℝ)) * o₂ : GA E b)) ^
        (-(2 * M : ℤ)) ≤ _
      rw [← mul_inv, ← mul_pow, _root_.zpow_neg, show (2 * M : ℤ) = ((2 * M : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by nlinarith) M))
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (@IsCompact.measure_lt_top _ _ _ _ (ctx h D).haar.toIsFiniteMeasureOnCompacts _ (IsCompact.mul (k₁.prod k₂) hΩ)).ne ?_) key
  rw [ENNReal.tsum_prod']
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h5 a M (by omega)))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h5 b M (by omega)))

theorem cutCount_of (h1 : RedBasic) (h2 : CutRed) (h3 : WtCount) : CutCount := by
  intro E _ _ _ a b D Ω hΩ
  obtain ⟨C₁, p₁, r₁⟩ := h2 E a
  obtain ⟨C₂, p₂, r₂⟩ := h2 E b
  have hI := h3 E a b D Ω hΩ (2 * (a + b)) le_rfl
  set M := 2 * (a + b)
  set I := ∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * M : ℤ))) * cnt (ratH E a b) Ω x ∂D.ν with hI'
  refine ⟨(1 + C₁ + C₂) ^ (2 * M) * I.toReal, 2 * M, by positivity, fun τ hτ => ?_⟩
  rw [mul_right_comm, ← mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hI, hI',
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => Set.indicator_apply_le' (fun hx => ?_) fun _ => zero_le
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  refine le_mul_of_one_le_left' (ENNReal.one_le_ofReal.2 ?_)
  have s₁ := ((h1 E a).2.1 x.1).1
  have s₂ := ((h1 E b).2.1 x.2).1
  have t₁ := r₁ τ hτ _ hx.1
  have t₂ := r₂ τ hτ _ hx.2
  rw [wt_eq, _root_.zpow_neg, show (2 * M : ℤ) = ((2 * M : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← div_eq_mul_inv,
    one_le_div₀ (by positivity)]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) _

end PositivityTheory.Rg.BcB.E1

end
