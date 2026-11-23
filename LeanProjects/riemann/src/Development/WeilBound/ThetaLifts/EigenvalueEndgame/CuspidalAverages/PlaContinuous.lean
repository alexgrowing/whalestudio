import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.KeyThree
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

noncomputable section

namespace PositivityTheory.ThKEnd.Cusp

open scoped TensorProduct
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem pla_le_one_iff {v : Pl F} (x : Fv F v) :
    ValuativeRel.valuation (Fv F v) x ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F v)) Valued.v).le_one_iff_le_one

theorem pla_continuous (v : Pl F) (t : E →ₐ[F] Fv F v) : Continuous (piW t) :=
  (continuous_splitProj t).comp (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap
    (fun a b => map_mul (evFin F v) a b) ((RestrictedProduct.continuous_eval v).comp continuous_snd))

theorem pla_int (z : AE F E) : ∀ᶠ v : Pl F in cofinite, ∀ t : E →ₐ[F] Fv F v, piW t z ∈ v.adicCompletionIntegers F := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v t => by rw [map_zero]; exact zero_mem _
  | add y z hy hz => filter_upwards [hy, hz] with v h h' t using by rw [map_add]; exact add_mem (h t) (h' t)
  | tmul a e =>
    have : Algebra.IsAlgebraic ℤ E := IsFractionRing.comap_isAlgebraic_iff.2 (inferInstance : Algebra.IsAlgebraic ℚ E)
    obtain ⟨d, hd, hi⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) e).exists_integral_multiple
    have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
    have h1 : ∀ᶠ v : Pl F in cofinite, algebraMap F (Fv F v) (d : F)⁻¹ ∈ v.adicCompletionIntegers F :=
      (algebraMap F (Af F) (d : F)⁻¹).2
    have h2 : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F := a.2.2
    filter_upwards [h1, h2] with v hv hv' t
    have h3 : t (d • e) ∈ v.adicCompletionIntegers F := apply_coe_mem t (⟨d • e, hi⟩ : 𝓞 E)
    have h4 : t e = algebraMap F (Fv F v) (d : F)⁻¹ * t (d • e) := by
      rw [← Int.cast_smul_eq_zsmul F, map_smul, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul]
    show evFin F v a * t e ∈ _
    rw [h4]
    exact mul_mem hv' (mul_mem hv h3)

theorem places : Places := by
  intro F E _ _ _ _ _ σ h
  refine ⟨pla_continuous, fun z => (pla_int z).mono fun v hv t => (pla_le_one_iff _).2 (hv t), fun χ T hχ v hv t x hx => ?_,
    fun hf => ?_⟩
  · refine hχ (splitPrime t) (fun hm => hv (splitPrime_under t ▸ hm)) _ ?_
    have h1 : Valued.v (complMap (splitPrime_under t) (x : Fv F v)) ≤ 1 := complMap_mem _ ((pla_le_one_iff _).1 hx.le)
    have h2 : Valued.v (complMap (splitPrime_under t) ((x : Fv F v)⁻¹)) ≤ 1 :=
      complMap_mem _ ((pla_le_one_iff _).1 (by rw [map_inv₀, hx, inv_one]))
    have h3 : Valued.v (complMap (splitPrime_under t) (x : Fv F v)) ≠ 0 := by simp
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 h3)] at h2
    exact le_antisymm h1 h2
  · obtain ⟨v, hv, hn⟩ := GlobalTheory.Orb.exists_split_place_notMem h hf.toFinset
    exact hv (hf.mem_toFinset.2 hn)

end PositivityTheory.ThKEnd.Cusp

end
