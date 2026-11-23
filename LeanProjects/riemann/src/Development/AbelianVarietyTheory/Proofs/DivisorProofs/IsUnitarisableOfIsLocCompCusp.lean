import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSqIntegrableAndIsDiscreteSplitCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacterStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem nu_zero_isUnitary (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : (nu E 0).IsUnitary := by
  intro x
  simp [nu, GlobalTheory.HeckeGal.Model.absPow, GlobalTheory.Mem.Chr.CharModel.absHom_val]

theorem isUnitarisable_of_twRep {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {χ : G →* ℂˣ} (hχ : ∀ g, ‖((χ g : ℂˣ) : ℂ)‖ = 1) (h : GlobalTheory.SmGL.IsUnitarisable (twRep ρ χ)) :
    GlobalTheory.SmGL.IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  have e := h3 g v w
  simp only [twRep_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at e
  have hc : ((χ g : ℂˣ) : ℂ) * starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ g]; simp
  rw [← e]
  linear_combination (-(B (ρ g v) (ρ g w))) * hc

theorem isUnitarisable_of_isLocComp_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (x : CuspSub E a), 1 ≤ a → x.IsUnitary → ∀ (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), x.IsLocComp w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ := by
  intro E _ _ _ a x ha hu w σ hσ
  have hcex := (GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨a, x⟩).1
  have hr : rexp (⟨a, x⟩ : Letter E) = 0 := ((GlobalTheory.T.cuspidalLetterRealExponent_eq_zero_iff_isUnitary E ⟨a, x⟩ ha).1).2 hu
  have hd : (0 : ℝ) < (a : ℝ) * Module.finrank ℚ E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    positivity
  have hre : (cex (⟨a, x⟩ : Letter E)).re = 0 := by
    have h := hr
    unfold rexp at h
    rcases div_eq_zero_iff.1 h with h | h
    · exact h
    · exact absurd h hd.ne'
  have hdc : ((a : ℂ) * (Module.finrank ℚ E : ℂ)) = (((a : ℝ) * Module.finrank ℚ E : ℝ) : ℂ) := by push_cast; ring
  obtain ⟨χ, hz, -, hn, -⟩ := GlobalTheory.T.exists_idelic_absValue_cpow_character E (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ)))
  have hzre : (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ))).re = 0 := by
    rw [hdc, Complex.div_ofReal_re, Complex.neg_re, hre]; simp
  have hχu : χ.IsUnitary := fun y => by rw [hn y, hzre]; exact nu_zero_isUnitary E y
  have hnorm : IsNormalised (x.twist χ) := by
    have h4 := GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨a, x.twist χ⟩
    refine h4.2.2.2.1.1 (h4.2.2.2.2 0 ?_)
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 x.ne_bot
    refine ⟨mulChi a χ φ, ⟨φ, hφ, rfl⟩, fun h => h0 ((mulChi a χ).map_eq_zero_iff.1 h), ?_⟩
    have e1 : zc E a φ = cex (⟨a, x⟩ : Letter E) • φ := hcex φ hφ
    have e2 : cex (⟨a, x⟩ : Letter E) + (a : ℂ) * (Module.finrank ℚ E : ℂ) *
        (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ))) = 0 := by
      have : ((a : ℂ) * (Module.finrank ℚ E : ℂ)) ≠ 0 := by
        rw [hdc]; exact_mod_cast hd.ne'
      rw [mul_div_cancel₀ _ this]; ring
    change zc E a (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ
    rw [hz, e1, ← add_smul, e2, zero_smul, map_zero, zero_smul]
  have hdisc := (GlobalTheory.T.cuspForm_sqIntegrable_and_isDiscrete_splitCentre E a).2 _ hnorm
  obtain ⟨f, h0, hf⟩ := hσ.twist χ
  have hgl : IsLocCompGL (x.twist χ).V w (σ.twist (CuspSub.locDet a χ w) (CuspSub.isOpen_ker_locDet χ w)) :=
    ⟨(x.twist χ).V.subtype ∘ₗ f, fun h => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h v)),
      fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩
  have hU := GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E a _ hdisc w _ hgl
  exact isUnitarisable_of_twRep (χ := CuspSub.locDet a χ w) (fun g => hχu _) hU

end GlobalTheory.ResW
