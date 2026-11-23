import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CoefficientSpans.FiniteCoeffSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm

theorem UpperTheory.V.Af.formsFiniteGL :
    GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  refine CoefficientSpans.finite_of (CoefficientSpans.charFinite_of Fin.formsFinite) (fun E _ _ _ a φ h => (Cm.isAutForm_iff φ).1 h)
    (fun E _ _ _ a => ⟨(Cm.cptEq E a).symm, fun φ k g => ?_⟩)
    (fun E _ _ _ a z hz => ⟨Cm.uTC E a z, ?_, fun _ _ => rfl⟩)
  · obtain ⟨k, rfl⟩ := (Cm.cptEq E a).surjective k
    rw [MulEquiv.symm_apply_apply, Cm.infEmb_cptEq]
    rfl
  · have h := Cm.uTC_mem_Zalg hz
    rw [Cm.Zalg_eq_map, Cm.center_UC, AlgHom.map_adjoin] at h
    refine Algebra.adjoin_mono ?_ h
    rintro _ ⟨_, ⟨τ, u, rfl⟩, rfl⟩
    exact ⟨τ, u, Cm.uC_capC τ u⟩
