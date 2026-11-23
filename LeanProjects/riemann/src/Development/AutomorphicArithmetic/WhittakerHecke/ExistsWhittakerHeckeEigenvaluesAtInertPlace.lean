import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
import Development.AutomorphicArithmetic.WhittakerHecke.PowerSeriesCompleteHomogeneousTwoMulEqOne
import Development.AutomorphicArithmetic.WhittakerHecke.EigAtCmDatumOperatorOfEigAt
import Development.AutomorphicArithmetic.WhittakerHecke.EigenformShintaniFormulaAtPlace
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsGoodCharacterOfInertCMDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) (z : (A E)ˣ)
    (h : (z : A E) = AdeleBaseChange.adeleMap ℚ E (y : A ℚ)) : em E (aE y) = aE z := by
  apply Units.ext
  ext i j
  rw [UpperTheory.ConvolutionTheory.RankTwoDescent.em, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [aE, h]

theorem UpperTheory.exists_whittaker_heckeEigenvalues_at_inert_place :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
          CenN P ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ) φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∀ v : H.P ℚ, ¬ Bad N v → ∀ w : H.P E, w.under (𝓞 ℚ) = v → H.Inert D v w →
          ∃ m : ℕ → ℂ, m 0 = 1 ∧
            (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (pv v ^ k)) * g) = m k * Wo D φ g) ∧
            ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) =
              PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := by
  intro E _ _ _ D P ω χ _ _ L N φ hA hG a hIs v hv w hw hI
  obtain ⟨-, B, hsat, hEig⟩ := hG.fix w (by rw [hw]; exact hv)
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk P w B).1 hsat))
  obtain ⟨-, -, hleft, -⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hA
  have hEw := UpperTheory.eigAt_cmDatumOperator_of_eigAt E D φ w _ hA.cont hEig
  obtain ⟨χw, hχ, hχe⟩ := UpperTheory.exists_good_character_of_inert_CMDatum E D v w (hG.pl v hv) hI
  have hnl : ∀ b h, Wo D φ (H.lc w (H.nL b) * h) = χw b * Wo D φ h := fun b h => by
    obtain ⟨u, t, e1, e2⟩ := hχe b
    rw [(H.lcLaws E w).1, e1, ← e2]
    exact hleft ![u, t] h
  obtain ⟨ϖ', hϖ', hz, -⟩ := hI.unif (atFin v (unif v)) (unif_spec v)
  have hem : ∀ k : ℕ, em E (aE (pv v ^ k)) = aE (H.idl w ϖ' ^ k) := fun k => by
    refine em_aE _ _ ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, hz, Dat.mkE, map_zero, zero_mul, add_zero]
    rfl
  have hnv : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  have hqw : H.q w = (normV v : ℂ) ^ 2 := by
    have : H.q w = (normV w : ℂ) := by simp [H.q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [this, hI.norm]
    push_cast
    rfl
  have hqv : (normV v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsq : H.q w ^ (1 / 2 : ℂ) = (normV v : ℂ) := by
    rw [hqw]
    have e : ((normV v : ℂ) ^ 2) = ((((normV v : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
    rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    simp
  refine ⟨fun k => ((normV v : ℂ) ^ k)⁻¹ * ∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i), by simp,
    fun k g hg => ?_, fun _ => ?_⟩
  · have h := UpperTheory.eigenform_shintani_formula_at_place E w ϖ' hϖ' χw hχ α β _ hEw hnl g (hg w hw) k
    rw [hsq] at h
    rw [hem, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hqv), one_mul]
  · have h1 := hIs.inert v hv w hw hI.norm α β hsat
    have h2 := UpperTheory.powerSeries_completeHomogeneous_two_mul_eq_one ((α * χ.val v : ℂˣ) : ℂ) ((β * χ.val v : ℂˣ) : ℂ)
    have h3 : (PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k *
        (((normV v : ℂ) ^ k)⁻¹ * ∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i))) =
        PowerSeries.mk fun k : ℕ => ∑ i ∈ Finset.range (k + 1),
          ((α * χ.val v : ℂˣ) : ℂ) ^ i * ((β * χ.val v : ℂˣ) : ℂ) ^ (k - i) := by
      congr 1
      funext k
      rw [Nat.cast_pow, mul_comm ((normV v : ℂ) ^ k), mul_assoc, ← mul_assoc ((normV v : ℂ) ^ k),
        mul_inv_cancel₀ (pow_ne_zero k hqv), one_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
      rw [Nat.add_sub_cancel_left, Units.val_mul, Units.val_mul]
      ring
    rw [h3]
    linear_combination (PowerSeries.mk fun k : ℕ => ∑ i ∈ Finset.range (k + 1),
          ((α * χ.val v : ℂˣ) : ℂ) ^ i * ((β * χ.val v : ℂˣ) : ℂ) ^ (k - i)) * h1 -
      (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) * h2
