import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSubInOfCob2InStatement

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.LogLin

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem mvPowerSeriesMap_evalTwoGroups (h : R →+* S) {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (at2 c u v) = at2 (map h c) (fun i => map h (u i)) (fun i => map h (v i)) := by
  unfold at2
  rw [map_subst (CobCob.elim_has hu hv)]
  congr 1
  funext j
  cases j <;> rfl

theorem map_op (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {τ : Type}
    {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    op (fun i => map h (μ i)) (fun i => map h (u i)) (fun i => map h (v i)) =
      fun i => map h (op μ u v i) :=
  funext fun i => (mvPowerSeriesMap_evalTwoGroups h hu hv (μ i)).symm

theorem map_threeGroupsFirstVariables (h : R →+* S) : (fun i => map h (x1 (R := R) (d := d) i)) = x1 := by
  funext i; simp [x1]

theorem map_threeGroupsSecondVariables (h : R →+* S) : (fun i => map h (x2 (R := R) (d := d) i)) = x2 := by
  funext i; simp [x2]

theorem map_threeGroupsThirdVariables (h : R →+* S) : (fun i => map h (x3 (R := R) (d := d) i)) = x3 := by
  funext i; simp [x3]

theorem map_assoc (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) (ha : op μ (op μ x1 x2) x3 = op μ x1 (op μ x2 x3)) :
    op (fun i => map h (μ i)) (op (fun i => map h (μ i)) x1 x2) x3 =
      op (fun i => map h (μ i)) x1 (op (fun i => map h (μ i)) x2 x3) := by
  have h12 := CobCob.op_const hc (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
  have h23 := CobCob.op_const hc (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
  rw [← map_threeGroupsFirstVariables h, ← map_threeGroupsSecondVariables h, ← map_threeGroupsThirdVariables h, map_op h μ CobCob.constantCoeff_threeGroupsFirstVariables CobCob.constantCoeff_threeGroupsSecondVariables,
    map_op h μ CobCob.constantCoeff_threeGroupsSecondVariables CobCob.constantCoeff_threeGroupsThirdVariables, map_op h μ h12 CobCob.constantCoeff_threeGroupsThirdVariables,
    map_op h μ CobCob.constantCoeff_threeGroupsFirstVariables h23, ha]

theorem map_swap (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (swap c) = swap (map h c) := by
  unfold swap
  rw [mvPowerSeriesMap_evalTwoGroups h (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_formalGroupLawCoboundaryOne_eq (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    map h (cob1 μ f) = cob1 (fun i => map h (μ i)) (map h f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hc),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem constantCoeff_formalGroupLawCoboundaryOne_eq_zero (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (cob1 μ f) = 0 := by
  unfold cob1 inL inR
  rw [map_sub, map_sub,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hc) hc hf,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) hf,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) hf, sub_zero, sub_zero]

theorem lin_form (w : Fin d → R) (i : Fin d) :
    lin (∑ j, w j • (X j : MvPowerSeries (Fin d) R)) i = w i := by
  classical
  unfold lin
  simp [coeff_X, Finsupp.single_left_inj]

end GlobalTheory.QLog.LogLin

open GlobalTheory.QLog.LogLin in

theorem GlobalTheory.QLog.exists_log_of_lin : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ w : Fin d → O, ∃ f : MvPowerSeries (Fin d) C, constantCoeff f = 0 ∧ (∀ i, lin f i = algebraMap O C (w i)) ∧ cob1 (up C μ) f = 0 := by
  intro p _ O C _ _ _ hF d μ hμ w
  classical
  let F : MvPowerSeries (Fin d) O := ∑ j, w j • (X j : MvPowerSeries (Fin d) O)
  have hF0 : constantCoeff F = 0 := by simp [F]
  let h : O →+* C := algebraMap O C
  have hup : up C μ = fun i => map h (μ i) := rfl
  have hc' : ∀ i, constantCoeff (up C μ i) = 0 := fun i => by
    rw [hup]; simp only [constantCoeff_map, hμ.const i, map_zero]
  have hcmap : cob1 (up C μ) (map h F) = map h (cob1 μ F) :=
    (map_formalGroupLawCoboundaryOne_eq h μ hμ.const F).symm
  have hlift : IsLift (RingHom.id O) μ :=
    ⟨hμ.const, hμ.unit, hμ.comm, by simpa using hμ⟩
  have rules := formalGroupLawCoboundaryTwo_coboundaryOne_alt C d (up C μ) hc' (map h F)
  have hass : op (up C μ) (op (up C μ) x1 x2) x3 = op (up C μ) x1 (op (up C μ) x2 x3) :=
    map_assoc h μ hμ.const hμ.assoc
  have hcomm : (fun i => swap (up C μ i)) = up C μ := by
    funext i; rw [hup]; dsimp only; rw [← map_swap, hμ.comm i]
  obtain ⟨g, hg0, hglin, -, hgc⟩ := GlobalTheory.T.swap_sub_in_of_cob2_in p O O C (RingHom.id O) hF d μ hlift ⊥ ⊤ bot_le
    (cob1 (up C μ) (map h F)) (Or.inl hμ)
    (by rw [hcmap, constantCoeff_map, constantCoeff_formalGroupLawCoboundaryOne_eq_zero μ hμ.const hF0, map_zero])
    (fun α => ⟨0, coeff α (cob1 μ F), Submodule.mem_top, by
      rw [pow_zero, one_mul, hcmap, coeff_map]⟩)
    (fun α => ⟨0, Submodule.zero_mem _, by
      rw [rules.1, hass, sub_self, map_zero, map_zero]⟩)
    (fun α => ⟨0, Submodule.zero_mem _, by
      rw [rules.2.1, hcomm, sub_self, map_zero, map_zero]⟩)
  have hzero : cob1 (up C μ) (map h F) - cob1 (up C μ) g = 0 := by
    ext α
    obtain ⟨b, hb, he⟩ := hgc α
    rw [Ideal.mem_bot] at hb
    rw [he, hb, map_zero, map_zero]
  refine ⟨map h F - g, ?_, fun i => ?_, ?_⟩
  · rw [map_sub, constantCoeff_map, hF0, map_zero, hg0, sub_zero]
  · have := congrFun hglin i
    unfold lin at this ⊢
    rw [map_sub, coeff_map, this, Pi.zero_apply, sub_zero]
    exact congrArg h (lin_form w i)
  · rw [sub_eq_add_neg, formalCoboundary_add hc', ← neg_one_smul C g, formalCoboundary_smul hc', neg_one_smul,
      ← sub_eq_add_neg, hzero]
