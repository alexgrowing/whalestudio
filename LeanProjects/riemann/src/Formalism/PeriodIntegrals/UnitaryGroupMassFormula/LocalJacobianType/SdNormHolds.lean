import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.IsCompactDbox

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

theorem real_box (ι : Type) [Fintype ι] (lam : Measure (Fv F v ⊗[F] E)) [SigmaFinite lam]
    (s : NNReal) (S : Set (Fv F v ⊗[F] E)) :
    ((s • Measure.pi (fun _ : ι => lam)) (Set.univ.pi fun _ => S)).toReal =
      (s : ℝ) * (lam S).toReal ^ Fintype.card ι := by
  rw [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, ENNReal.coe_toReal]

theorem sdNorm_holds : SdNorm (E := E) ψ v := by
  by_cases hK : OpenKer v ψ
  · by_cases hnt : ∃ r, psiV F ψ v r ≠ 1
    · right
      set lam : Measure (Fv F v ⊗[F] E) := Measure.addHaar
      set a : ℝ := lam.real (OEv (E := E) v)
      set d : ℝ := lam.real (D1 (E := E) v ψ)
      have ha : 0 < a := ENNReal.toReal_pos
        ((isOpen_oev (E := E) v).measure_ne_zero lam ⟨0, oev_zero (E := E) v⟩) (isCompact_oev (E := E) v).measure_lt_top.ne
      have hd : 0 < d := ENNReal.toReal_pos
        ((conductor_isOpen (E := E) v ψ hK).measure_ne_zero lam ⟨0, diagonal_phase_first_vector (E := E) v ψ⟩)
        (conductor_isCompact (E := E) v ψ hK hnt).measure_lt_top.ne
      refine ⟨Real.sqrt (a / d), Real.sqrt_pos.2 (div_pos ha hd), fun ι _ => ?_⟩
      have hex := exists_sd (E := E) v ψ hK hnt ι
      have hs : sdE (E := E) ψ v ι = hex.choose := by
        rw [sdE_eq, dif_pos hex]
      have hμ := hex.choose_spec
      have := hμ.1
      refine ⟨by rw [hs]; exact hμ.1, ?_⟩
      rw [hs]
      obtain ⟨s, hsμ⟩ : ∃ s : NNReal, hex.choose = s • Measure.pi (fun _ : ι => lam) :=
        ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
      have h1 := sd_test (E := E) v ψ ι hex.choose hμ (isOpen_dbox (E := E) v ψ hK ι).measurableSet
        (isCompact_dbox (E := E) v ψ hK hnt ι).measure_lt_top
      have hO : hex.choose.real (Obox (E := E) v ι) = (s : ℝ) * a ^ Fintype.card ι := by
        rw [Measure.real, hsμ, Obox, real_box]; rfl
      have hD : hex.choose.real (Dbox (E := E) v ψ ι) = (s : ℝ) * d ^ Fintype.card ι := by
        rw [Measure.real, hsμ, Dbox, real_box]; rfl
      rw [hO, hD] at h1
      show (hex.choose (Obox (E := E) v ι)).toReal = _
      rw [← Measure.real, hO]
      have hsq : ((s : ℝ) * a ^ Fintype.card ι) ^ 2 = (Real.sqrt (a / d) ^ Fintype.card ι) ^ 2 := by
        rw [← pow_mul, mul_comm _ 2, pow_mul, Real.sq_sqrt (div_pos ha hd).le, div_pow]
        have hdn : d ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hd.ne'
        rw [eq_div_iff hdn]
        linear_combination (a ^ Fintype.card ι) * h1
      exact (pow_left_inj₀ (mul_nonneg s.2 (pow_nonneg ha.le _))
        (pow_nonneg (Real.sqrt_nonneg _) _) two_ne_zero).1 hsq
    · left
      push Not at hnt
      intro ι _ _
      rw [sdE_eq, dif_neg (no_sd_triv (E := E) v ψ ι hnt)]
  · left
    intro ι _ _
    rw [sdE_eq, dif_neg (no_sd_noKer (E := E) v ψ ι hK)]

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
