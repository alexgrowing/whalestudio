import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.GelfandCentralHolds

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem gen_eq_A (p : Fin n × Fin n) : Formalism.L2.SG.Pf.admitted.gen ε p = casGen ε p := by
  unfold Formalism.L2.SG.Pf.admitted.gen casGen casSg Formalism.L2.SG.Pf.admitted.sg
  split_ifs <;> simp

theorem coef_eq_A (p : Fin n × Fin n) :
    (((Formalism.L2.SG.Pf.admitted.wt p * Formalism.L2.SG.Pf.admitted.sg ε p : ℝ)) : ℂ) = casWt p * casSg ε p := by
  unfold Formalism.L2.SG.Pf.admitted.wt Formalism.L2.SG.Pf.admitted.sg casWt casSg
  split_ifs <;> push_cast <;> ring

theorem cas_eq_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : smD ε σ) :
    Formalism.L2.SG.Pf.admitted.Cas ε σ v = ((casimir (smE ε σ) v : smD ε σ) : H) := by
  rw [← casU_eq_casimir (isDerivedOn_smE hσ) v]
  unfold Formalism.L2.SG.Pf.admitted.Cas casU
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coef_eq_A, gen_eq_A]
  rfl

theorem admissibleProjection_of_irreducible_indefUnitary [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : Formalism.MainNotions.BridgeCPX.AdmProjAt ε σ :=
  Formalism.MainNotions.BridgeCPX.HCAdm_of_mult (fun n ε H _ _ _ σ h1 h2 S h3 h4 => CompanionTheory.HCMult.harish_chandra_multiplicity n ε H σ h1 h2 S h3 h4)
    n ε H σ hσ hirr

theorem casimirActsByScalar_indefUnitary : CasScal := by
  intro n ε H _ _ _ σ hσ hirr
  by_cases hex : ∃ w : H, Formalism.MainNotions.S.IsKFin ε σ w ∧ w ≠ 0
  · obtain ⟨w, hwK, hw⟩ := hex
    obtain ⟨c, hc⟩ := Formalism.L2.SG.Pf.admitted.casScalar n ε H σ hσ hirr w hw
    have hK : ∀ (x : smD ε σ), Formalism.MainNotions.S.IsKFin ε σ (x : H) →
        casimir (smE ε σ) x = (c : ℂ) • x := fun x hx => by
      have h1 := hc x (Formalism.MainNotions.BridgeCPX.kfin_mem_Vsub hσ hirr (admissibleProjection_of_irreducible_indefUnitary hσ hirr) hw hx)
      rw [cas_eq_A hσ] at h1
      exact Subtype.ext (by rw [h1]; rfl)
    refine ⟨c, fun v => ?_⟩
    have hy : ((casimir (smE ε σ) v - (c : ℂ) • v : smD ε σ) : H) = 0 := by
      refine eq_zero_of_perp_A hσ (Submodule.coe_mem _) fun a ha => ?_
      have haS := mem_smD_of_isKFin hσ hirr ha
      have h1 := casimir_symm_A hσ ⟨a, haS⟩ v
      rw [hK ⟨a, haS⟩ ha, inner_smul_left, Complex.conj_ofReal] at h1
      rw [Submodule.coe_sub, Submodule.coe_smul, inner_sub_right, inner_smul_right]
      have h2 : ⟪a, ((casimir (smE ε σ) v : smD ε σ) : H)⟫_ℂ = (c : ℂ) * ⟪a, (v : H)⟫_ℂ := by
        have := h1.symm
        simpa using this
      rw [h2, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (by simpa using hy))
  · push Not at hex
    refine ⟨0, fun v => ?_⟩
    have h0 : (v : H) = 0 := eq_zero_of_perp_A hσ v.2 fun a ha => by
      rw [show a = 0 by by_contra h; exact h (hex a ha) |>.elim]
      simp
    have hv : v = 0 := Subtype.ext h0
    rw [hv, map_zero, smul_zero]

end CompanionTheory.D.gk.HC
