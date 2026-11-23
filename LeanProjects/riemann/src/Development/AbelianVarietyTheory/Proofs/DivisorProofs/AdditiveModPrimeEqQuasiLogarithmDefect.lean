import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleModIdealEqCoboundaryQuasiLogStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefectCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealOfPowerSeriesIffImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesLiftQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemIdealOfFormalGroupCoboundaryOneCoeffMemAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalSeriesOfCoboundaryDvdPStatement

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

namespace DefectSurj

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_const {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) : ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ n ih =>
    intro i
    rw [nmul, Function.iterate_succ_apply', ← nmul, op, at2]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [ih]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

theorem powerSeriesPullbackTwoGroups_add_smul {φ : Fin d → MvPowerSeries (Fin d) R} (hφ : ∀ i, constantCoeff (φ i) = 0)
    (a : R) (κ h : MvPowerSeries (Fin d ⊕ Fin d) R) :
    pull2 φ (κ + a • h) = pull2 φ κ + a • pull2 φ h := by
  have hs : HasSubst (Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j))) := by
    refine hasSubst_of_constantCoeff_zero ?_
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) (hφ j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) (hφ j)
  unfold pull2 at2
  rw [subst_add hs, subst_smul hs]

end DefectSurj

theorem additive_mod_p_is_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f ∧ map (algebraMap O E) s = defect c.μ p f ∧ c.ev 1 s = b + (p : O) • y := by
  intro p _ O E _ _ _ hF G d c b z hb
  obtain ⟨κ, B, y, h0, h2, hsw, hB, hev⟩ := GlobalTheory.T.exists_formalSeries_of_coboundary_dvd_p p O G d c (-b) (-z)
    (by rw [map_neg, hb, smul_neg])
  obtain ⟨f, hf, -, hin⟩ := GlobalTheory.T.symmetricCocycle_modIdeal_eq_coboundary_quasiLog p O E hF d c.μ c.isLaw (p : O) dvd_rfl κ h0 h2 hsw
  obtain ⟨t, ht, hmt⟩ := (GlobalTheory.series_in_ideal_iff_image O E _ _ _).1.1 hin
  obtain ⟨h, rfl⟩ := ((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) t).1
    (fun α => Ideal.mem_span_singleton.1 (ht α))
  have hκ : map (algebraMap O E) (κ + (p : O) • h) = cob1 (up E c.μ) f := by
    rw [map_add, hmt]; abel
  obtain ⟨s, hs, -⟩ := (GlobalTheory.T.defect_ev_succ_eq_mulP_add_p_pow_smul p O E hF G d c f hf).1 p
  have hc := ((GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f _ hκ).2.2 p s hs).1
  rw [DefectSurj.powerSeriesPullbackTwoGroups_add_smul (DefectSurj.nmul_const c.isLaw.const p)] at hc
  obtain ⟨u, hu⟩ := ((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) _).1 hB
  have hsum : cob1 c.μ (s + B) =
      (p : O) • (κ + (p : O) • h - pull2 (nmul c.μ p) h + u) := by
    rw [formalCoboundary_add c.isLaw.const, hc, smul_add _ _ u, smul_sub, ← hu]; abel
  have hdiv := GlobalTheory.T.coeff_mem_of_coeff_cob1_mem p O G d c (Ideal.span {(p : O)}) (Ideal.mem_span_singleton_self _)
    (s + B) (fun α => Ideal.mem_span_singleton.2
      (((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) _).2 ⟨_, hsum⟩ α))
  obtain ⟨w, hw⟩ := ((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) _).1
    (fun α => Ideal.mem_span_singleton.1 (hdiv α))
  refine ⟨f, s, c.ev 1 w - y, hf, hs, ?_⟩
  have := congrArg (c.ev 1) hw
  rw [map_add, map_smul, hev] at this
  rw [smul_sub, ← this]; abel

end GlobalTheory.QLog
