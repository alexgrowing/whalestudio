import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntAdCpctOpen

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Metric

namespace Formalism.L2.SG.Pf.RescaleCore.NCov

def AdCocpt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ C : Set (AF F), IsCompact C ∧ ∀ a : AF F, ∃ x : F, a - algebraMap F (AF F) x ∈ C

namespace AdCocptW

variable {F : Type} [Field F] [NumberField F]

theorem NCovAd_ball_compact (v : InfinitePlace F) (R : ℝ) :
    IsCompact (closedBall (0 : v.Completion) R) := by
  first
  | exact isCompact_closedBall (0 : v.Completion) R
  | exact (haveI : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion
      isCompact_closedBall (0 : v.Completion) R)
  | exact (by
      have hi := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v
      have hc := (hi.isClosedEmbedding).isCompact_preimage (isCompact_closedBall (0 : ℂ) R)
      have e : (NumberField.InfinitePlace.Completion.extensionEmbedding v) ⁻¹' closedBall 0 R =
          closedBall (0 : v.Completion) R := by
        ext z
        simp only [Set.mem_preimage, mem_closedBall, dist_zero_right]
        rw [hi.norm_map_of_map_zero (map_zero _)]
      rw [e] at hc
      exact hc)

theorem NCovAd_inf_approx : ∃ R : ℝ, ∀ x : Ainf F, ∃ β : 𝓞 F,
    ∀ v : InfinitePlace F, ‖(x - algebraMap F (Ainf F) (β : F)) v‖ ≤ R := by
  classical
  set b := NumberField.mixedEmbedding.latticeBasis F with hb
  have hB : ∃ R : ℝ, ∀ y ∈ ZSpan.fundamentalDomain b, ‖y‖ ≤ R := by
    first
    | exact (ZSpan.fundamentalDomain_isBounded b).exists_norm_le
    | exact isBounded_iff_forall_norm_le.mp (ZSpan.fundamentalDomain_isBounded b)
  obtain ⟨R, hR⟩ := hB
  refine ⟨R, fun x => ?_⟩
  obtain ⟨⟨w, hw⟩, hwD, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)
  have hc' : ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ, ∑ i, c i • b i = w := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
    | exact Submodule.mem_span_range_iff_exists_fun.mp hw
  obtain ⟨c, hc⟩ := hc'
  let γ : 𝓞 F := ∑ i, c i • NumberField.RingOfIntegers.basis F i
  have hγ : NumberField.mixedEmbedding F (algebraMap (𝓞 F) F γ) = w := by
    rw [← hc]
    simp only [γ, map_sum, map_zsmul, hb, NumberField.mixedEmbedding.latticeBasis_apply,
      NumberField.integralBasis_apply]
  refine ⟨-γ, fun v => ?_⟩
  have hneg : ((-γ : 𝓞 F) : F) = -(algebraMap (𝓞 F) F γ) := by
    first
    | rfl
    | simp
    | (push_cast; rfl)
  set z := x - algebraMap F (Ainf F) ((-γ : 𝓞 F) : F) with hzdef
  have hz : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z ∈ ZSpan.fundamentalDomain b := by
    have e : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z = w + NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x := by
      rw [hzdef, hneg, map_neg, sub_neg_eq_add, map_add, ← hγ,
        NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, add_comm]
    rw [e]
    first
    | exact hwD
    | (rw [Submodule.vadd_def, vadd_eq_add] at hwD; exact hwD)
    | (simpa [Submodule.vadd_def] using hwD)
  have hn := hR _ hz
  by_cases hv : v.IsReal
  · calc ‖z v‖ = ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).1 ⟨v, hv⟩‖ := by
          rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          exact ((NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).1‖ := norm_le_pi_norm _ _
      _ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_fst_le _
      _ ≤ R := hn
  · have hv' : v.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
    calc ‖z v‖ = ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).2 ⟨v, hv'⟩‖ := by
          rw [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          exact ((NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
            (map_zero _) _).symm
      _ ≤ ‖(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z).2‖ := norm_le_pi_norm _ _
      _ ≤ ‖NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F z‖ := norm_snd_le _
      _ ≤ R := hn

theorem NCovAd_int_mem (β : 𝓞 F) : algebraMap F (Af F) (β : F) ∈ Formalism.UG.intAd F := by
  show ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    (algebraMap F (Af F) (β : F)) v ∈ v.adicCompletionIntegers F
  intro v
  first
  | exact v.coe_mem_adicCompletionIntegers β
  | exact (v.mem_adicCompletionIntegers F).mpr (by
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using v.valuation_le_one β)
  | exact (v.mem_adicCompletionIntegers F).mpr (by
      show Valued.v ((β : F) : v.adicCompletion F) ≤ 1
      rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      simpa using v.valuation_le_one β)

theorem NCovAd_fin_approx (a : Af F) : ∃ x : F, a - algebraMap F (Af F) x ∈ Formalism.UG.intAd F := by
  obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a
  obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma m hm
  refine ⟨(β : F) / m, ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F) := (map_natCast _ m).symm
  have hu : IsUnit ((m : ℕ) : Af F) := by
    rw [hcast]
    exact (isUnit_iff_ne_zero.2 hmF).map _
  have e1 : ((m : ℕ) : Af F) * (a - algebraMap F (Af F) ((β : F) / m)) = (m : Af F) * y := by
    rw [mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    ring
  rw [hu.mul_left_cancel e1]
  exact hy

end AdCocptW

end Formalism.L2.SG.Pf.RescaleCore.NCov
