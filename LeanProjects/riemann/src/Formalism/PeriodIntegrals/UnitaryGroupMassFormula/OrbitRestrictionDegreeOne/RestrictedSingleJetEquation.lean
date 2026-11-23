import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitRestrictionDegreeOne.Lemmas

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G
open MvPowerSeries PI.OrbShared

variable {D : D7}

theorem restricted_single_jet_equation (p : ℕ) [Fact p.Prime] (hn : nP D p = 1) {N0 N1 : ℕ} (z : Pl D)
    (Th U : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) (ep0 : ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) (hbe : ∀ z, constantCoeff (be z) = 0)
    (ep sg : Pl D → ℂ_[p])
    (hEq : subst (fun v : Pl D × Fin N0 × Fin N1 => C ep0 * logPl D p v) Th =
        U * subst (logPl D p (β := Fin N0 × Fin N1))
          (OJ.expS ℂ_[p] (∑ z : Pl D, (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
            subst (fun s : ZMod 2 => if s = 0 then
                (X (z, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
              else C (ep z) * X (z, a, b)) (be z)))) :
    subst (fun v : ZMod 1 × Fin N0 × Fin N1 => C ep0 * jetLogG p 1 v) (restr1 D p z Th) =
      killCompl (embOne z N0 N1) U * subst (jetLogG p 1 (β := Fin N0 × Fin N1))
        (OJ.expS ℂ_[p] ((sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
          subst (fun s : ZMod 2 => if s = 0 then
              (X ((0 : ZMod 1), a, b) : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p])
            else C (ep z) * X ((0 : ZMod 1), a, b)) (be z))) := by
  set e := embOne z N0 N1 with he
  have hA : HasSubst (fun v : Pl D × Fin N0 × Fin N1 => (C ep0 * logPl D p v : MvPowerSeries _ ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero (fun v => by simp [constantCoeff_logPl])
  have hL : HasSubst (logPl D p (β := Fin N0 × Fin N1)) :=
    hasSubst_of_constantCoeff_zero (fun v => constantCoeff_logPl p v)
  have hJ : HasSubst (jetLogG p 1 (β := Fin N0 × Fin N1)) :=
    hasSubst_of_constantCoeff_zero (fun v => constantCoeff_jetLogG p 1 v)
  have hB : HasSubst (fun v : ZMod 1 × Fin N0 × Fin N1 => (C ep0 * jetLogG p 1 v : MvPowerSeries _ ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero (fun v => by simp [constantCoeff_jetLogG])
  have hρ : HasSubst (fun v : Pl D × Fin N0 × Fin N1 => killCompl e (X v : MvPowerSeries _ ℂ_[p])) :=
    hasSubst_killCompl e HasSubst.X
  have hσ0 : ∀ (y : Pl D) (a : Fin N0) (b : Fin N1) (s : ZMod 2),
      constantCoeff (if s = 0 then (X (y, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
        else C (ep y) * X (y, a, b)) = 0 := by
    intro y a b s; split_ifs <;> simp
  have hσ : ∀ (y : Pl D) (a : Fin N0) (b : Fin N1), HasSubst (fun s : ZMod 2 =>
      if s = 0 then (X (y, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
        else C (ep y) * X (y, a, b)) :=
    fun y a b => hasSubst_of_constantCoeff_zero (hσ0 y a b)
  set S : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] := ∑ z : Pl D, (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
      subst (fun s : ZMod 2 => if s = 0 then
          (X (z, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
        else C (ep z) * X (z, a, b)) (be z) with hSdef
  have hS : constantCoeff S = 0 := by
    rw [hSdef, map_sum]
    apply Finset.sum_eq_zero
    intro y _
    rw [← coeff_zero_eq_constantCoeff_apply, map_smul, map_sum]
    rw [Finset.sum_eq_zero, smul_zero]
    intro a _
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro b _
    rw [coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_subst_eq_zero (hσ y a b) (hσ0 y a b) (hbe y)
  have hκS : killCompl e S = (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1,
      subst (fun s : ZMod 2 => if s = 0 then
          (X ((0 : ZMod 1), a, b) : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p])
        else C (ep z) * X ((0 : ZMod 1), a, b)) (be z) := by
    rw [hSdef, map_sum, Finset.sum_eq_single z]
    · rw [map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [killCompl_subst e (hσ z a b)]
      congr 1
      funext s
      split_ifs
      · rw [he, killCompl_X_one, if_pos rfl]
      · rw [map_mul, killCompl_C, he, killCompl_X_one, if_pos rfl]
    · intro y _ hy
      rw [map_smul, map_sum]
      rw [Finset.sum_eq_zero, smul_zero]
      intro a _
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro b _
      rw [killCompl_subst e (hσ y a b)]
      have h0 : (fun s : ZMod 2 => killCompl e (if s = 0 then
          (X (y, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
            else C (ep y) * X (y, a, b))) = 0 := by
        funext s
        have hx : killCompl e (X (y, a, b) : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) = 0 := by
          rw [he, killCompl_X_one, if_neg hy]
        split_ifs
        · rw [hx]; rfl
        · rw [map_mul, hx, mul_zero]; rfl
      rw [h0, subst_zero_of_constantCoeff_zero (hbe y)]
    · intro h; exact absurd (Finset.mem_univ z) h
  have h1 := congrArg (killCompl e) hEq
  rw [killCompl_subst e hA, map_mul, killCompl_subst e hL] at h1
  rw [restr1_eq_killCompl, ← he, killCompl_eq_subst e Th, subst_comp_subst_apply hρ hB]
  have eA : (fun v : Pl D × Fin N0 × Fin N1 => subst (fun v : ZMod 1 × Fin N0 × Fin N1 =>
      (C ep0 * jetLogG p 1 v : MvPowerSeries _ ℂ_[p])) (killCompl e (X v : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]))) =
      fun v => killCompl e (C ep0 * logPl D p v) := by
    funext v
    rw [he, subst_killCompl_X_one p z hB, map_mul, killCompl_C, killCompl_logPl p hn]
    split_ifs <;> simp
  rw [eA, h1]
  congr 1
  have eL : (fun v : Pl D × Fin N0 × Fin N1 => killCompl e (logPl D p v)) =
      fun v => subst (jetLogG p 1 (β := Fin N0 × Fin N1)) (killCompl e (X v : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])) := by
    funext v
    rw [he, subst_killCompl_X_one p z hJ, killCompl_logPl p hn]
  rw [eL, ← subst_comp_subst_apply hρ hJ, ← killCompl_eq_subst e, killCompl_expS e S hS, hκS]

end PI.OrbJet

end
