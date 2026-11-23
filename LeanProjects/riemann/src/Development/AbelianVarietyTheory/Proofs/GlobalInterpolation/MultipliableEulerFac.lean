import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

noncomputable section

namespace GlobalTheory.DensityProductCompare

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

open private euler_factor_log_bound partial_sums_log_euler_factor_le from Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

theorem multipliable_eulerFac (E : Type) [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (M : ℕ) (hM : 2 ≤ M) :
    Multipliable (fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac E M P.1) := by
  have hpos : ∀ P : {P : Ideal (𝓞 E) // P.IsMaximal}, 0 < Formalism.HermitianLatticesTheory.eulerFac E M P.1 :=
    fun P => (euler_factor_log_bound E hE M (by omega) P.1 P.2).1
  have habs : Summable (fun P : {P : Ideal (𝓞 E) // P.IsMaximal} =>
      |Real.log (Formalism.HermitianLatticesTheory.eulerFac E M P.1)|) :=
    summable_of_sum_le (fun P => abs_nonneg _) (partial_sums_log_euler_factor_le E hE M hM)
  exact Real.multipliable_of_summable_log hpos habs.of_abs

section Defs

variable (F : Type) [Field F] [NumberField F]

theorem dualIndex_eq : IndefiniteRowSideFullHecke.LocalDualIndex.dualIndex F = IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.nIdx F := rfl

theorem normDifferentV_eq : IndefiniteRowSideFullHecke.LocalDualIndex.normDifferentV F = IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.normDiffV F := rfl

theorem resCard_eq : IndefiniteRowSideFullHecke.LocalDualIndex.resCard F = IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.resCard F := by
  funext v
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.resCard IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.resCard
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem absDiscr_eq : IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr F = ((|discr F| : ℤ) : ℝ) := by
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr
  rw [Int.cast_abs]

theorem mult_eq_one [IsTotallyReal F] (w : InfinitePlace F) : w.mult = 1 := by
  unfold InfinitePlace.mult
  rw [if_pos (IsTotallyReal.isReal w)]

theorem stdInf_eq [IsTotallyReal F] : IndefiniteRowSideFullHecke.LocalDualIndex.stdInf F = IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.stdInf F := by
  funext x
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.stdInf IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.stdInf IndefiniteRowSideFullHecke.LocalDualIndex.traceInf
  rw [← Complex.exp_sum, ← Finset.mul_sum]
  congr 2
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mult_eq_one]; simp

theorem isStdChar_iff [IsTotallyReal F] (ψ : AddChar (AF F) ℂ) :
    IndefiniteRowSideFullHecke.LocalDualIndex.IsStdChar F ψ ↔ IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.IsStdChar F ψ := by
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.IsStdChar IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.IsStdChar
  rw [stdInf_eq]

theorem isScalingInf_iff [IsTotallyReal F] (ψ : AddChar (AF F) ℂ) (a : Fˣ) :
    IndefiniteRowSideFullHecke.LocalDualIndex.IsScalingInf F ψ a ↔ IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.ScalesInf F ψ a := by
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.IsScalingInf IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.ScalesInf
  rw [stdInf_eq]

theorem absInf_eq [IsTotallyReal F] (a : Fˣ) :
    IndefiniteRowSideFullHecke.LocalDualIndex.absInf F a = IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.absInf F a := by
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.absInf IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.absInf
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [mult_eq_one, pow_one]

variable (E : Type) [Field E] [Algebra F E]

theorem etaV_eq : IndefiniteRowSideFullHecke.LocalDualIndex.etaV F E = IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.eta F E := rfl

theorem eulerInv_eq : IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv F E = IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.eulerInv F E := by
  funext M v
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.eulerInv
  rw [etaV_eq, resCard_eq]

theorem localDensity_eq : IndefiniteRowSideFullHecke.LocalDualIndex.localDensity F E = IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.locDens F E := by
  funext ψ M v
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.localDensity IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.locDens
  rw [dualIndex_eq, eulerInv_eq]

theorem eulerInv_pos (M : ℕ) (hM : 1 ≤ M) (v : HeightOneSpectrum (𝓞 F)) :
    0 < IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv F E M v := by
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.eulerInv
  have hq : 1 < IndefiniteRowSideFullHecke.LocalDualIndex.resCard F v := by
    unfold IndefiniteRowSideFullHecke.LocalDualIndex.resCard
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    omega
  have hq' : (1 : ℝ) < (IndefiniteRowSideFullHecke.LocalDualIndex.resCard F v : ℝ) := by exact_mod_cast hq
  have h1 : (IndefiniteRowSideFullHecke.LocalDualIndex.resCard F v : ℝ) ^ (-(M : ℤ)) < 1 :=
    zpow_lt_one_of_neg₀ hq' (by omega)
  have h0 : 0 < (IndefiniteRowSideFullHecke.LocalDualIndex.resCard F v : ℝ) ^ (-(M : ℤ)) := zpow_pos (by linarith) _
  have he : IndefiniteRowSideFullHecke.LocalDualIndex.etaV F E v ^ M ≤ 1 := by
    refine (le_abs_self _).trans ?_
    rw [abs_pow]
    unfold IndefiniteRowSideFullHecke.LocalDualIndex.etaV
    split_ifs <;> simp
  nlinarith

end Defs

theorem scaling_unique (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (ψ : AddChar (AF F) ℂ) (a b : F) (ha : IndefiniteRowSideFullHecke.LocalDualIndex.IsScalingInf F ψ a)
    (hb : IndefiniteRowSideFullHecke.LocalDualIndex.IsScalingInf F ψ b) : a = b := by
  by_contra hab
  have hc : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hn : (0 : ℝ) < Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
  set n : ℕ := Fintype.card (InfinitePlace F) with hndef
  set y : F := (a - b)⁻¹ * ((2 * n : ℕ) : F)⁻¹ with hy
  have h := (ha (algebraMap F (Ainf F) y)).symm.trans (hb (algebraMap F (Ainf F) y))
  rw [← map_mul, ← map_mul] at h
  have hay : a * y = b * y + ((2 * n : ℕ) : F)⁻¹ := by
    rw [hy]; field_simp; ring
  have htr : ∀ z : F, IndefiniteRowSideFullHecke.LocalDualIndex.traceInf F (algebraMap F (Ainf F) (z + ((2 * n : ℕ) : F)⁻¹)) =
      IndefiniteRowSideFullHecke.LocalDualIndex.traceInf F (algebraMap F (Ainf F) z) + 1 / 2 := by
    intro z
    unfold IndefiniteRowSideFullHecke.LocalDualIndex.traceInf
    have : ∀ w : InfinitePlace F, (w.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding w
        (algebraMap F (Ainf F) (z + ((2 * n : ℕ) : F)⁻¹) w)).re =
        (w.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding w
        (algebraMap F (Ainf F) z w)).re + ((2 * n : ℕ) : ℝ)⁻¹ := by
      intro w
      have e : ∀ u : F, algebraMap F (Ainf F) u w = algebraMap F w.Completion u := fun u => rfl
      rw [mult_eq_one, e, e, map_add, map_add, map_inv₀, map_natCast, map_inv₀, map_natCast,
        Complex.add_re, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
      simp
    rw [Finset.sum_congr rfl fun w _ => this w, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, ← hndef, nsmul_eq_mul]
    congr 1
    push_cast
    field_simp
  unfold IndefiniteRowSideFullHecke.LocalDualIndex.stdInf at h
  rw [hay, htr] at h
  rw [Complex.ofReal_add, mul_add, Complex.exp_add] at h
  have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    push_cast
    rw [show -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [h2] at h
  have h3 := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) *
    (IndefiniteRowSideFullHecke.LocalDualIndex.traceInf F (algebraMap F (Ainf F) (b * y)) : ℂ))
  apply h3
  linear_combination (-1 / 2 : ℂ) * h

section Conclusions

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

def FirstConclusion : Prop :=
  open IndefiniteRowSideFullHecke.LocalDualIndex in
    (∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀) ∧
    (∀ ψ₀, IsStdChar F ψ₀ → ∀ v : HeightOneSpectrum (𝓞 F),
      (∀ t : Fv F v, t ∈ dualV F ψ₀ v ↔
        ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) ∧
      dualIndex F ψ₀ v = normDifferentV F v) ∧
    ((Function.mulSupport (normDifferentV F)).Finite ∧
      ((∏ᶠ v, normDifferentV F v : ℕ) : ℝ) = absDiscr F ∧
      absDiscr F = (2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E) ∧
    (∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) ∧
    (∀ M : ℕ, 2 ≤ M → 0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      HasProd (fun v => (eulerInv F E M v)⁻¹) (Formalism.HermitianLatticesTheory.lValEta E M)) ∧
    (∀ ψ, IsCharAF F ψ →
      (∀ v, (intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧
      ∀ a : F, a ≠ 0 → IsScalingInf F ψ a → ∀ M : ℕ, 2 ≤ M →
        Summable (fun v => |localDensity F E ψ M v - 1|) ∧
        ∃ P : ℝ, 0 < P ∧ HasProd (localDensity F E ψ M) P ∧
          absInf F a ^ ((M : ℝ) - 1 / 2) * P =
            absDiscr F ^ ((1 : ℝ) / 2 - M) / Formalism.HermitianLatticesTheory.lValEta E M)

def SecondConclusion : Prop :=
  open IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual in
    CharsAreTwists F ∧ DifferentProduct F ∧ ((|discr F| : ℤ) : ℝ) = dF E ∧
    ∀ M : ℕ, 2 ≤ M →
      LValue F E M ∧
      ∀ ψ, IsCharAF F ψ →
        (∃ a : Fˣ, ScalesInf F ψ a) ∧ ∀ a : Fˣ, ScalesInf F ψ a → DensityProduct F E ψ a M

theorem hypotheses_iff (σ : E →ₐ[F] E) :
    (IsCMExt F E σ ∧ (∀ x : E, star x = σ x) ∧ Formalism.HermitianLatticesTheory.IsCMUnram E) ↔
      (IsCMExt F E σ ∧ Formalism.HermitianLatticesTheory.IsCMUnram E) :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.star_eq_sigma σ h.1 h.2, h.2⟩⟩

theorem second_of_first [IsTotallyReal F] (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (h : FirstConclusion F E) : SecondConclusion F E := by
  obtain ⟨⟨ψ₁, hψ₁, -⟩, hdual, ⟨hfin, hprod, hd⟩, htw, hL, hdens⟩ := h
  refine ⟨⟨⟨ψ₁, (isStdChar_iff F _).1 hψ₁⟩, ?_⟩, ⟨?_, ?_, hfin, ?_⟩, ?_, ?_⟩
  · intro ψ₀ h₀ ψ hψ
    have h₀' := (isStdChar_iff F _).2 h₀
    obtain ⟨a, ha, hx⟩ := htw ψ₀ h₀' ψ hψ
    refine ⟨Units.mk0 a ha, hx, fun b hb => Units.ext ?_⟩
    exact scaling_unique F ψ _ _ (IndefiniteRowSideFullHecke.LocalDualIndex.isScalingInf_of_eq F h₀' hb)
      (IndefiniteRowSideFullHecke.LocalDualIndex.isScalingInf_of_eq F h₀' hx)
  · intro ψ₀ h₀
    exact hdual ψ₀ ((isStdChar_iff F _).2 h₀)
  · intro v h0
    have h1 := (hdual ψ₁ hψ₁ v).2
    obtain ⟨h2, h3⟩ := (hdens ψ₁ hψ₁.1).1 v
    rw [normDifferentV_eq, h0, Nat.cast_zero, IndefiniteRowSideFullHecke.LocalDualIndex.dualIndex, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · exact h2 (by exact_mod_cast h1)
    · exact h3 (by exact_mod_cast h1)
  · rw [absDiscr_eq, normDifferentV_eq] at hprod
    exact Int.cast_injective (α := ℝ) (by rw [Int.cast_natCast]; exact hprod)
  · rw [← absDiscr_eq]; exact hd
  · intro M hM
    refine ⟨⟨multipliable_eulerFac E hE M hM, (hL M hM).1, ?_⟩, fun ψ hψ => ⟨?_, ?_⟩⟩
    · rw [← eulerInv_eq]; exact (hL M hM).2
    · obtain ⟨a, ha, hx⟩ := htw ψ₁ hψ₁ ψ hψ
      exact ⟨Units.mk0 a ha, (isScalingInf_iff F ψ _).1 (IndefiniteRowSideFullHecke.LocalDualIndex.isScalingInf_of_eq F hψ₁ hx)⟩
    · intro a ha
      obtain ⟨hidx, hrest⟩ := hdens ψ hψ
      obtain ⟨hs, P, hP, hPr, hval⟩ := hrest a a.ne_zero ((isScalingInf_iff F ψ a).2 ha) M hM
      unfold IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.DensityProduct
      rw [← localDensity_eq, hPr.tprod_eq, ← absInf_eq]
      refine ⟨hidx, fun v => ?_, hs, hPr.multipliable, hP, ?_⟩
      · refine mul_pos (Real.rpow_pos_of_pos (div_pos ?_ ?_) _) (eulerInv_pos F E M (by omega) v)
        · exact_mod_cast Nat.pos_of_ne_zero (hidx v).1
        · exact_mod_cast Nat.pos_of_ne_zero (hidx v).2
      · rw [hval, hd]; rfl

theorem first_of_second [IsTotallyReal F] (h : SecondConclusion F E) : FirstConclusion F E := by
  obtain ⟨⟨⟨ψ₁, hψ₁⟩, htw⟩, ⟨hdual, -, hfin, hprod⟩, hd, hM⟩ := h
  have hψ₁' := (isStdChar_iff F _).2 hψ₁
  have hd' : IndefiniteRowSideFullHecke.LocalDualIndex.absDiscr F = IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.dF E := by rw [absDiscr_eq]; exact hd
  refine ⟨⟨ψ₁, hψ₁', fun ψ₂ hψ₂ => ?_⟩, ?_, ⟨hfin, ?_, hd'⟩, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := htw ψ₁ hψ₁ ψ₂ hψ₂.1
    have h1 : (a : F) = 1 := scaling_unique F ψ₂ _ _
      (IndefiniteRowSideFullHecke.LocalDualIndex.isScalingInf_of_eq F hψ₁' ha) hψ₂.isScalingInf_one
    ext x
    rw [ha x, h1, map_one, one_mul]
  · intro ψ₀ h₀
    exact hdual ψ₀ ((isStdChar_iff F _).1 h₀)
  · rw [absDiscr_eq, normDifferentV_eq, ← hprod, Int.cast_natCast]
  · intro ψ₀ h₀ ψ hψ
    obtain ⟨a, ha, -⟩ := htw ψ₀ ((isStdChar_iff F _).1 h₀) ψ hψ
    exact ⟨a, a.ne_zero, ha⟩
  · intro M h2
    obtain ⟨⟨-, hpos, hPr⟩, -⟩ := hM M h2
    rw [eulerInv_eq]
    exact ⟨hpos, hPr⟩
  · intro ψ hψ
    refine ⟨?_, fun a ha hsc M h2 => ?_⟩
    · obtain ⟨⟨a, ha⟩, hall⟩ := (hM 2 le_rfl).2 ψ hψ
      exact (hall a ha).1
    · obtain ⟨-, -, hs, hmul, hpos, hval⟩ :=
        ((hM M h2).2 ψ hψ).2 (Units.mk0 a ha) ((isScalingInf_iff F ψ (Units.mk0 a ha)).1 hsc)
      rw [localDensity_eq, hd']
      refine ⟨hs, _, hpos, hmul.hasProd, ?_⟩
      rw [← hval, ← absInf_eq]; rfl

theorem conclusions_iff (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    FirstConclusion F E ↔ SecondConclusion F E :=
  haveI := h.1
  ⟨second_of_first F E hE, first_of_second F E⟩

end Conclusions

theorem densityProduct_iff :
    IndefiniteRowSideFullHecke.LocalDualIndex.DensityProduct ↔ IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.EulerProductOfDensities := by
  constructor
  · intro h F E _ _ _ _ _ _ σ hσ hE
    exact (conclusions_iff F E σ hσ hE).1
      (h F E σ hσ ((hypotheses_iff F E σ).2 ⟨hσ, hE⟩).2.1 hE)
  · intro h F E _ _ _ _ _ _ σ hσ _ hE
    exact (conclusions_iff F E σ hσ hE).2 (h F E σ hσ hE)

end GlobalTheory.DensityProductCompare
