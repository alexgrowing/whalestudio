import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KmuInclDenseRange
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TchOfIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.SemilinNormPowSubPow
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormSqrtNegPowPrimeSqSub
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonH
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgMulN
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgFinA
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ShortWIntModel
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.EndIntegral
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgLevel

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem integral_of_map_kur {l : ℕ} [Fact l.Prime] {f : PowerSeries (MaximalUnramifiedExtension l)}
    (h : IntegralPS (PowerSeries.map (MaximalUnramifiedExtension l).subtype f)) : IntegralPS f := fun n => by
  have := h n
  rw [PowerSeries.coeff_map] at this
  exact this

theorem cm3 : CM3 := by
  intro d L _hsq hd hCM l _ hl hld hin ι g2 g3 hg
  obtain ⟨hg2, hg3, hn2, hn3, -, -⟩ := id hg
  have : CompleteSpace (MaximalUnramifiedExtension l) := kur_complete l
  obtain ⟨σ, hσ⟩ := kurFrob l
  have hR := kur_resClosed l
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι (omegaK_quad d hd)
    simpa using this
  obtain ⟨-, ha1, ha', haσ⟩ := kur_quad l d hd (by omega) hld hin _ hquad
  have haσ' := haσ σ hσ
  have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := by
    have := norm_natCast_of_coprime (K := MaximalUnramifiedExtension l) hσ.prime hσ.norm_l 2
      (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have hlaw := curve_law (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ hn2 hn3 h2
  have hD : HD σ (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) _
      ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
        (C (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))
      ⟨ι (omegaK d), ha'⟩ :=
    { toLawD := hlaw
      A0 := mult_const _ _ _
      Aint := integral_of_map_kur (by
        rw [mult_map]
        exact end_integral d L hd hCM l hl hld hin ι g2 g3 hg)
      Alog := mult_log _ _ _
      a_ne := by
        rw [haσ']
        have : ‖((1 - (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])‖ = 1 := by
          have e : ((1 - (⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) - ⟨ι (omegaK d), ha'⟩ : MaximalUnramifiedExtension l) : ℂ_[l])
              = 1 - 2 * ι (omegaK d) := by
            push_cast; ring
          rw [e]; exact ha1
        exact this
      a_sq := by
        rw [haσ', map_sub, map_one, haσ']; ring }
  have he : IntegralPS ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)) := by
    obtain ⟨e', h0, hint, hlog⟩ := mulN_integral hlaw l
    rw [← mult_unique _ _ _ e' h0 hlog]
    exact hint
  have hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩))‖ = 1 := by
    obtain ⟨i, hi, hu⟩ := level_le L l hl ι g2 g3 hg
    refine ⟨i, hi, ?_⟩
    have hm := mult_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ ((l : ℕ) : MaximalUnramifiedExtension l)
    have hl' : (MaximalUnramifiedExtension l).subtype ((l : ℕ) : MaximalUnramifiedExtension l) = ((l : ℕ) : ℂ_[l]) := map_natCast _ _
    rw [hl'] at hm
    have hc := congrArg (coeff i) hm
    rw [PowerSeries.coeff_map] at hc
    have : ‖(MaximalUnramifiedExtension l).subtype (coeff i ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
      (C ((l : ℕ) : MaximalUnramifiedExtension l) * lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)))‖ = 1 := by
      rw [hc]; exact hu
    exact this
  obtain ⟨c, hc, hT⟩ := hon_main hσ hD (mult_const _ _ _) he (mult_log _ _ _) hlev
  obtain ⟨ε, hε, hcε⟩ := lang_semilinear hσ hR c hc
  have hfin := fin_integral hσ (uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩) (lgS (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩)
    (lgS_const _ _) (lgS_coeff_one _ _) (uSer_const _ _) (uSer_subst_lgS _ _) c ε hc hε hcε hT
  refine ⟨ε, ε.2, hε, fun n => ?_⟩
  have hm := lt_map (MaximalUnramifiedExtension l).subtype (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩ l (by omega) ε
  have hc' := congrArg (coeff n) hm
  rw [PowerSeries.coeff_map] at hc'
  have hc'' : coeff n ((uSer g2 g3).subst (C (ε : ℂ_[l]) * ltLog ℂ_[l] l))
      = (MaximalUnramifiedExtension l).subtype (coeff n ((uSer (⟨g2, hg2⟩ : MaximalUnramifiedExtension l) ⟨g3, hg3⟩).subst
          (C ε * ltLog (MaximalUnramifiedExtension l) l))) := hc'.symm
  rw [hc'']
  exact ⟨SetLike.coe_mem _, hfin n⟩

end ReciprocityTheory.ChartRestriction.L1
