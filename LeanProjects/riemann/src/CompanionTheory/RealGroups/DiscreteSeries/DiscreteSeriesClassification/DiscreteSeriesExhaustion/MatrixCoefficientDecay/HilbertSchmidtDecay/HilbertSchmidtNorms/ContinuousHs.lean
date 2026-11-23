import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HilbertSchmidtNorms.HsConjTranspose

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace CompanionTheory.RgExh.Dec.L.AB

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

structure Hyp {n : ℕ} (ε : Fin n → Bool) (S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (m : ℕ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℂ) (ν : ∀ j, Measure (PSub ε (A j))) (τ : Fin m → S7.UJ ε → ℝ)
    (r : Fin m → ℝ) (Z : Fin m → Finset ℂ) (M c₁ R₀ C : ℝ) : Prop where
  c1pos : 0 < c₁
  formula : ∀ j, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ F : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable (fun g : S7.UJ ε => F (S7.toM g)) → (∀ (g : S7.UJ ε) (k : S7.KG ε), F (S7.toM g * S7.toMK k) = F (S7.toM g)) →
      ∫⁻ g : S7.UJ ε, F (S7.toM g) ∂Measure.haar = κ * ∫⁻ x in {x : PSub ε (A j) | τ j x ∈ Set.Ico 0 1},
        (∫⁻ t : ℝ, F (S7.toM (x : S7.UJ ε) * aT (A j) t) * ENNReal.ofReal (Real.exp (2 * r j * t))) ∂(ν j)
  tauCont : ∀ j, Continuous (τ j)
  tauInv : ∀ j (x y : PSub ε (A j)) (k : S7.KG ε), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * S7.toMK k → τ j y = τ j x
  lines : ∀ j (x : PSub ε (A j)) (t : ℝ), ∃ y : PSub ε (A j), S7.toM (y : S7.UJ ε) = S7.toM (x : S7.UJ ε) * aT (A j) t ∧
      τ j y = τ j x + t
  cover : ∃ U : Fin m → Set (S7.UJ ε), (∀ j, MeasurableSet (U j)) ∧ (∀ j g (k : S7.KG ε), g ∈ U j → g * (k : S7.UJ ε) ∈ U j) ∧
      (∀ g : S7.UJ ε, R₀ < Formalism.REAL.hs (S7.toM g) → ∃ j, g ∈ U j) ∧
      ∀ j (x : PSub ε (A j)), (x : S7.UJ ε) ∈ U j → c₁ * Real.log (Formalism.REAL.hs (S7.toM (x : S7.UJ ε))) ≤ τ j x
  hsLine : ∀ j (x : PSub ε (A j)) (t : ℝ), 0 ≤ τ j x → 0 ≤ t →
      C⁻¹ * Real.exp (2 * t) * Formalism.REAL.hs (S7.toM (x : S7.UJ ε)) ≤ Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * aT (A j) t) ∧
        Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * aT (A j) t) ≤ C * Real.exp (2 * t) * Formalism.REAL.hs (S7.toM (x : S7.UJ ε))
  cont : ∀ f ∈ S, Continuous fun g : S7.UJ ε => f (S7.toM g)
  dom : ∀ f ∈ S, ∃ (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ), (∀ h ∈ T, h ∈ S) ∧
      ∀ (g : S7.UJ ε) (k k' : S7.KG ε), ‖f (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2
  chain : ∀ f ∈ S, ∀ j, ∃ (f₀ : Matrix (Fin n) (Fin n) ℂ → ℂ) (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)), Chain ε S (A j) (Z j) f f₀ ∧ (∀ h ∈ T, h ∈ S) ∧
      ∀ x : PSub ε (A j), 0 ≤ τ j x →
        ‖f₀ (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ j x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖
  qual : ∀ f ∈ S, ∀ j, ∀ᵐ (x : PSub ε (A j)) ∂(ν j), (∫⁻ t in Set.Ioi (0 : ℝ),
      ‖f (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (r j + 1) * t))) < ⊤
  level : ∀ f ∈ S, LevelF ε f (-M)

variable {n : ℕ}

def PsiK (ε : Fin n → Bool) (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ≥0∞ :=
  (⨆ k : S7.KG ε, ‖q (X * S7.toMK k)‖ₑ ^ 2) * ENNReal.ofReal (Formalism.REAL.hs X ^ w)

variable {ε : Fin n → Bool}

theorem psiK_inv (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (g : S7.UJ ε) (k : S7.KG ε) :
    PsiK ε q w (S7.toM g * S7.toMK k) = PsiK ε q w (S7.toM g) := by
  unfold PsiK
  rw [hs_mul_K]
  congr 1
  have e : ∀ k' : S7.KG ε, S7.toM g * S7.toMK k * S7.toMK k' = S7.toM g * S7.toMK (k * k') := by
    intro k'
    rw [Matrix.mul_assoc]
    rfl
  simp_rw [e]
  exact (Equiv.mulLeft k).iSup_comp (g := fun k' => ‖q (S7.toM g * S7.toMK k')‖ₑ ^ 2)

theorem continuous_hs : Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => Formalism.REAL.hs X) := by
  unfold Formalism.REAL.hs
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_id.matrix_elem i j).norm).pow 2

theorem psiK_meas (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (hq : Continuous fun g : S7.UJ ε => q (S7.toM g)) :
    Measurable fun g : S7.UJ ε => PsiK ε q w (S7.toM g) := by
  have h1 : ∀ k : S7.KG ε, Continuous fun g : S7.UJ ε => ‖q (S7.toM g * S7.toMK k)‖ₑ ^ 2 := by
    intro k
    have hc : Continuous fun g : S7.UJ ε => q (S7.toM (g * (k : S7.UJ ε))) :=
      hq.comp (continuous_mul_const (k : S7.UJ ε))
    exact (ENNReal.continuous_pow 2).comp hc.enorm
  have hsup : Measurable fun g : S7.UJ ε => ⨆ k : S7.KG ε, ‖q (S7.toM g * S7.toMK k)‖ₑ ^ 2 :=
    (lowerSemicontinuous_iSup fun k => (h1 k).lowerSemicontinuous).measurable
  have hw : Measurable fun g : S7.UJ ε => ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) :=
    ENNReal.measurable_ofReal.comp ((continuous_hs.comp (S7.continuous_toM ε)).measurable.pow_const w)
  exact hsup.mul hw

theorem psiK_ge (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (g : S7.UJ ε) :
    ‖q (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) ≤ PsiK ε q w (S7.toM g) := by
  unfold PsiK
  gcongr
  refine le_iSup_of_le (1 : S7.KG ε) ?_
  have : S7.toMK (1 : S7.KG ε) = 1 := rfl
  rw [this, Matrix.mul_one]

theorem psiK_le (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ)
    (hd : ∀ (g : S7.UJ ε) (k k' : S7.KG ε), ‖q (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2)
    (g : S7.UJ ε) :
    PsiK ε q w (S7.toM g) ≤ ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) := by
  unfold PsiK
  rw [← Finset.sum_mul, ← mul_assoc]
  gcongr
  refine iSup_le fun k => ?_
  have h := hd g 1 k
  have e1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
  rw [e1, Matrix.one_mul] at h
  have hn : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hn]
  calc ENNReal.ofReal (‖q (S7.toM g * S7.toMK k)‖ ^ 2) ≤ ENNReal.ofReal (Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal Cf * ENNReal.ofReal (∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2) :=
        ENNReal.ofReal_mul' (Finset.sum_nonneg fun _ _ => by positivity)
    _ = ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        simp_rw [hn]

theorem psiK_lint (q : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : ℝ) (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ)
    (hd : ∀ (g : S7.UJ ε) (k k' : S7.KG ε), ‖q (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2)
    (hT : ∀ h ∈ T, LevelF ε h w) (hTc : ∀ h ∈ T, Continuous fun g : S7.UJ ε => h (S7.toM g)) :
    ∫⁻ g : S7.UJ ε, PsiK ε q w (S7.toM g) ∂Measure.haar < ⊤ := by
  calc ∫⁻ g : S7.UJ ε, PsiK ε q w (S7.toM g) ∂Measure.haar
      ≤ ∫⁻ g : S7.UJ ε, ENNReal.ofReal Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) ∂Measure.haar :=
        lintegral_mono fun g => psiK_le q w T Cf hd g
    _ = ENNReal.ofReal Cf * ∑ h ∈ T, ∫⁻ g : S7.UJ ε, ‖h (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ w) ∂Measure.haar := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        intro h hh
        exact (((ENNReal.continuous_pow 2).comp (hTc h hh).enorm).measurable.mul
          (ENNReal.measurable_ofReal.comp ((continuous_hs.comp (S7.continuous_toM ε)).measurable.pow_const w))).aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun h hh => hT h hh)

end CompanionTheory.RgExh.Dec.L.AB
