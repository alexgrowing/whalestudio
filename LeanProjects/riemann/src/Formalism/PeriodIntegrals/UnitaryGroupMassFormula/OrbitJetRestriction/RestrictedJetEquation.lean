import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.ConstantCoeffZeroOfVanishing

noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbShared

theorem hasSubst_Clog (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (ep : ℂ_[p]) :
    HasSubst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => by rw [map_mul, cc_logPl, mul_zero])

theorem hasSubst_log (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} :
    HasSubst (logPl D p (β := Fin N0 × Fin N1)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_logPl D p v)

theorem hasSubst_Cjet (l d : ℕ) [Fact l.Prime] [NeZero d] {N0 N1 : ℕ} (ep : ℂ_[l]) :
    HasSubst (fun v : ZMod d × Fin N0 × Fin N1 => C ep * jetLogG l d v) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => by rw [map_mul, cc_jetLogG, mul_zero])

theorem hasSubst_jet (l d : ℕ) [Fact l.Prime] [NeZero d] {N0 N1 : ℕ} :
    HasSubst (jetLogG l d (β := Fin N0 × Fin N1)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_jetLogG l d v)

theorem restricted_jet_equation (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (hR : IsReps D p R)
    (ep : ℂ_[p]) (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p])
    (hcc : ∀ r ∈ R, constantCoeff (be r) = 0)
    (Th U : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
    (hEq : subst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) Th =
      U * subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (beAll D p R sg be)))
    {r : Pl D} (hr : r ∈ R) :
    subst (fun v : ZMod (nP D p) × Fin N0 × Fin N1 => C ep * jetLogG p (nP D p) v) (restr D p r Th) =
      killCompl (orbEmb D p r (Fin N0 × Fin N1)) U *
        subst (jetLogG p (nP D p) (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (sg r • ∑ a : Fin N0, ∑ b : Fin N1,
          subst (fun s : ZMod (nP D p) =>
            (X (s, a, b) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p])) (be r))) := by
  set e := orbEmb D p r (Fin N0 × Fin N1) with he
  have hk := congrArg (killCompl e) hEq
  have hA : killCompl e (subst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) Th) =
      subst (fun v : ZMod (nP D p) × Fin N0 × Fin N1 => C ep * jetLogG p (nP D p) v) (killCompl e Th) := by
    refine killCompl_subst_of e _ _ (hasSubst_Clog D p ep) (hasSubst_Cjet p (nP D p) ep) ?_ ?_ Th
    · intro w
      rw [map_mul, killCompl_C, he, killCompl_logPl_emb]
    · intro t ht
      rw [map_mul, killCompl_logPl_off D p r t ht, mul_zero]
  have hL : ∀ F : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p],
      killCompl e (subst (logPl D p (β := Fin N0 × Fin N1)) F) =
        subst (jetLogG p (nP D p) (β := Fin N0 × Fin N1)) (killCompl e F) := by
    intro F
    refine killCompl_subst_of e _ _ (hasSubst_log D p) (hasSubst_jet p (nP D p)) ?_ ?_ F
    · intro w; rw [he, killCompl_logPl_emb]
    · intro t ht; exact killCompl_logPl_off D p r t ht
  have hccAll : constantCoeff (beAll D p (N0 := N0) (N1 := N1) R sg be) = 0 := by
    unfold beAll
    rw [map_sum]
    have hsm : ∀ (c : ℂ_[p]) (f : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]),
        constantCoeff f = 0 → constantCoeff (c • f) = 0 := by
      intro c f h
      rw [← coeff_zero_eq_constantCoeff_apply] at h ⊢
      simp [h]
    refine Finset.sum_eq_zero fun r' hr' => hsm _ _ ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    exact constantCoeff_subst_eq_zero (hasSubst_orbX D p r' a b) (fun s => by simp) (hcc r' hr')
  have hE : killCompl e (OJ.expS ℂ_[p] (beAll D p (N0 := N0) (N1 := N1) R sg be)) =
      OJ.expS ℂ_[p] (killCompl e (beAll D p (N0 := N0) (N1 := N1) R sg be)) := by
    unfold OJ.expS PowerSeries.subst
    exact killCompl_subst e (hasSubst_of_constantCoeff_zero fun _ => hccAll) _
  rw [map_mul, hA, hL, hE, killCompl_beAll D p R hR sg be hcc hr] at hk
  rw [restr_eq_killCompl, ← he]
  exact hk

end PI.OrbJet.OrbW
