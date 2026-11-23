import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardCompUnfLe
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsPerfectTraceIdeal
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

theorem log_card_comp_le_of_rows : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * zBase large₂ ^ 2 := by
  intro D T h large₂ ⟨h2, hrL, hrd, hf, hg, h16⟩ j hj σ hσ
  obtain ⟨ξ, AA, hsk, hne, hFG, hA, hdual⟩ := PerfectTrace.exists_perfect_trace_ideal D
  obtain ⟨-, -, hM, -, -, hfin, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hJ j hj
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hfd : FD.fdeg D.host.E = D.R.f := by
    unfold FD.fdeg; rw [hfin]; omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast (by omega : 0 < D.R.f)
  have hdisc : 0 < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hdE : Real.log (FD.dE D.host.E) ≤ 4 * FD.fdeg D.host.E * large₂.sc.L := by
    unfold Formalism.BasicNotions.Host.rdE at hrd
    rw [Real.log_rpow hdisc, hfin, one_div_mul_eq_div, div_le_iff₀ (by push_cast; positivity)] at hrd
    push_cast at hrd
    rw [hfd]
    unfold FD.dE
    linarith
  have hML : Real.log T.Q.l.M' ≤ 30 * large₂.sc.L := by
    rw [hM, hMg]
    have h0 := hg 0
    have h1 := hg 1
    have a := (D.host.g_prime 0).pos
    have b := (D.host.g_prime 1).pos
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a.ne') (by exact_mod_cast b.ne')]
    linarith
  have key := GlobalTheory.log_card_comp_unf_le GlobalTheory.QNorm.hasseNormSt GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
    D.host.E _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr hσ ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ))
    ξ AA hsk hne hFG hA hdual large₂.sc.L (by rw [hfd]; exact h16) h2 hdE hrL
    (by rw [hfd]; exact hf) hML
  rw [hfd] at key
  exact key

end GlobalTheory.EtaAn
