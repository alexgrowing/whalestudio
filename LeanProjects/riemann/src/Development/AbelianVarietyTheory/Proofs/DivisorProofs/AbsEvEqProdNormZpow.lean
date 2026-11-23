import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntValuationNormEqSumResidueDegreeMul

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.UnrTate.completion_norms

open GroundTheory.Global.SemiLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_eq_zpow (v : Pl F) {a : Fv F v} (ha : a ≠ 0) :
    ‖a‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (Valued.v a) := by
  have h0 : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  obtain ⟨c, hc⟩ := WithZero.ne_zero_iff_exists.mp h0
  have : Multiplicative.toAdd (WithZero.unzero h0) = WithZero.log (Valued.v a) := by
    simp only [← hc]; rfl
  rw [this]
  push_cast
  rfl

theorem complMap_eq (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (h : w.under (𝓞 F) = v) (a : Fv F v) : complMap h a = completionMap v w a := by
  subst h
  rw [complMap_rfl]
  refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val w _ fun n => ?_)
  have hc := continuous_completionMap (w.under (𝓞 F)) w
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le (w.under (𝓞 F)) (-(n : ℤ))).preimage (continuous_sub_left a)
  have h2 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le w (-(n : ℤ))).preimage
    ((continuous_sub_left (completionMap _ w a)).comp hc)
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F)
    (w.under (𝓞 F))).exists_mem_open (h1.inter h2) ⟨a, by simp, by simp⟩
  have e : GlobalTheory.AdeleBaseChange.locMap F w a - completionMap (w.under (𝓞 F)) w a =
      GlobalTheory.AdeleBaseChange.locMap F w (a - algebraMap F ((w.under (𝓞 F)).adicCompletion F) k) -
        (completionMap (w.under (𝓞 F)) w a -
          completionMap (w.under (𝓞 F)) w (algebraMap F ((w.under (𝓞 F)).adicCompletion F) k)) := by
    rw [map_sub, GlobalTheory.AdeleBaseChange.locMap_algebraMap, completionMap_algebraMap,
      IsScalarTower.algebraMap_apply F E (w.adicCompletion E)]
    ring
  rw [e]
  exact Valuation.map_sub_le _ (GlobalTheory.AdeleBaseChange.locMap_valued w n _ hk1) hk2

theorem toCompl_eq (v : Pl F) (w : PlacesOver E v) (h : w.1.under (𝓞 F) = v) (y : Fv F v ⊗[F] E) :
    toCompl h y = tensorEquiv E v y w := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [toCompl_tmul, tensorEquiv_tmul, Pi.mul_apply, complMap_eq v w.1 h]; rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz]; rfl

theorem continuous_norm_completionsOver (v : Pl F) :
    Continuous (Algebra.norm (Fv F v) : CompletionsOver E v → Fv F v) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Module.Finite (Fv F v) (CompletionsOver E v) := Module.Finite.equiv (tensorEquiv E v).toLinearEquiv
  let b := Module.finBasis (Fv F v) (CompletionsOver E v)
  have hlin : Continuous (Algebra.leftMulMatrix b : CompletionsOver E v → Matrix _ _ (Fv F v)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h : (Algebra.norm (Fv F v) : CompletionsOver E v → Fv F v) =
      fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]; exact hlin.matrix_det

theorem mem_aboveF_iff (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) :
    w ∈ Formalism.L2.Host.aboveF (L := E) F v ↔ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
  rw [mem_aboveF]
  constructor
  · rintro rfl; rfl
  · intro h; exact HeightOneSpectrum.ext h

theorem absNorm_eq_pow (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 E) w.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal v.asIdeal, map_pow]

end GlobalTheory.UnrTate.completion_norms

namespace GlobalTheory.UnrTate.completion_norms

theorem prod_zpow_eq {ι : Type} (q : ℝ) (hq : q ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, q ^ a i = q ^ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hq]

theorem lt_of_le_exp_log_sub_one {t s : WithZero (Multiplicative ℤ)} (ht : t ≠ 0)
    (hs : s ≤ WithZero.exp (WithZero.log t - 1)) : s < t := by
  refine lt_of_le_of_lt hs ?_
  conv_rhs => rw [← WithZero.exp_log ht]
  exact WithZero.exp_lt_exp.2 (by omega)

end GlobalTheory.UnrTate.completion_norms

namespace GlobalTheory.UnrTate

open GroundTheory.Global.SemiLocal completion_norms

theorem absEv_eq_prod_absNorm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) (x : (Fv F v ⊗[F] E)ˣ), ((absEv F E v x : ℝ≥0) : ℝ) =
      ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, (Ideal.absNorm w.asIdeal : ℝ) ^ (-GlobalTheory.UnrTate.ordAt v w x) := by
  intro F E _ _ _ _ _ v x
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set z : CompletionsOver E v := tensorEquiv E v x.1 with hz
  have hN : Algebra.norm (Fv F v) x.1 = Algebra.norm (Fv F v) z :=
    (Algebra.norm_eq_of_algEquiv (tensorEquiv E v) x.1).symm
  have hzu : IsUnit z := x.isUnit.map (tensorEquiv E v)
  have hzw : ∀ w, z w ≠ 0 := fun w => (hzu.map (Pi.evalRingHom _ w)).ne_zero
  have hNz : Algebra.norm (Fv F v) z ≠ 0 := (hzu.map (Algebra.norm (Fv F v))).ne_zero
  set c : Fv F v := Algebra.norm (Fv F v) z with hc
  have hc0 : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hNz
  have hzw0 : ∀ w, Valued.v (z w) ≠ 0 := fun w => (Valuation.ne_zero_iff _).2 (hzw w)
  let U : Set (CompletionsOver E v) :=
    (⋂ w, {y | Valued.v (y w - z w) ≤ WithZero.exp (WithZero.log (Valued.v (z w)) - 1)}) ∩
      {y | Valued.v (Algebra.norm (Fv F v) y - c) ≤ WithZero.exp (WithZero.log (Valued.v c) - 1)}
  have hU : IsOpen U := by
    refine (isOpen_iInter_of_finite fun w => ?_).inter ?_
    · exact IsOpen.preimage (f := fun y : CompletionsOver E v => y w - z w)
        ((continuous_apply w).sub continuous_const)
        (GlobalTheory.Mem.UnitOpen.isOpen_val_le w.1 (WithZero.log (Valued.v (z w)) - 1))
    · exact IsOpen.preimage (f := fun y : CompletionsOver E v => Algebra.norm (Fv F v) y - c)
        ((continuous_norm_completionsOver v).sub continuous_const)
        (GlobalTheory.Mem.UnitOpen.isOpen_val_le v (WithZero.log (Valued.v c) - 1))
  have hzU : z ∈ U := by
    refine ⟨Set.mem_iInter.2 fun w => ?_, ?_⟩
    · show Valued.v (z w - z w) ≤ _
      rw [sub_self, map_zero]; exact zero_le'
    · show Valued.v (c - c) ≤ _
      rw [sub_self, map_zero]; exact zero_le'
  obtain ⟨b, hb1, hb2⟩ := (denseRange_algebraMap_completionsOver E v).exists_mem_open hU ⟨z, hzU⟩
  have hbw : ∀ w : PlacesOver E v, Valued.v (algebraMap E (w.1.adicCompletion E) b) = Valued.v (z w) := fun w =>
    Valuation.map_eq_of_sub_lt _ (lt_of_le_exp_log_sub_one (hzw0 w) (Set.mem_iInter.1 hb1 w))
  have hbN : Valued.v (Algebra.norm (Fv F v) (algebraMap E (CompletionsOver E v) b)) = Valued.v c :=
    Valuation.map_eq_of_sub_lt _ (lt_of_le_exp_log_sub_one hc0 hb2)
  have hNb : Algebra.norm (Fv F v) (algebraMap E (CompletionsOver E v) b) =
      algebraMap F (Fv F v) (Algebra.norm F b) := by
    rw [← tensorEquiv_one_tmul, Algebra.norm_eq_of_algEquiv, norm_one_tmul]
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [hNb, Algebra.norm_zero, map_zero, map_zero] at hbN
    exact hc0 hbN.symm
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors (I := v.asIdeal)).2
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot)

  have hL : ((absEv F E v x : ℝ≥0) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^
      ∑ w ∈ Formalism.L2.Host.aboveF (L := E) F v,
        (w.asIdeal.inertiaDeg (𝓞 F) : ℤ) * WithZero.log (w.valuation E b) := by
    rw [GlobalTheory.Doubling.absEv_apply, coe_nnnorm, hN, norm_eq_zpow v hNz, ← hbN, hNb,
      Formalism.UG.P.levelaf_valued_algebraMap]
    exact congrArg _ (GlobalTheory.NormValuation.log_valuation_norm_eq_sum F E v (Units.mk0 b hb0) _ (mem_aboveF_iff v))
  rw [hL, ← prod_zpow_eq _ hq]
  refine Finset.prod_congr rfl fun w hw => ?_
  have h := mem_aboveF.1 hw
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h]; rfl⟩
  have hval : -ordAt v w x = WithZero.log (w.valuation E b) := by
    rw [ordAt, neg_neg, valAt_of_under h, toCompl_eq v ⟨w, inferInstance⟩ h, ← hz, ← hbw ⟨w, inferInstance⟩,
      Formalism.UG.P.levelaf_valued_algebraMap]
  rw [hval, absNorm_eq_pow v w, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]

end GlobalTheory.UnrTate
