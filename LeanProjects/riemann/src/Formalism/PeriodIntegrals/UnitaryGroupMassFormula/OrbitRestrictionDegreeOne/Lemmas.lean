import Formalism.PeriodIntegrals.OrbRestrOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.KillSubst

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet

open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G
open MvPowerSeries PI.OrbShared

variable {D : D7}

def embOne (z : Pl D) (N0 N1 : ℕ) : ZMod 1 × Fin N0 × Fin N1 ↪ Pl D × Fin N0 × Fin N1 where
  toFun v := (z, v.2)
  inj' _ _ h := Prod.ext (Subsingleton.elim _ _) (congrArg (fun x => x.2) h)

theorem restr1_eq_killCompl (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D)
    (Th : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]) :
    restr1 D p z Th = killCompl (embOne z N0 N1) Th := by
  ext m
  rw [MvPowerSeries.coeff_killCompl, Finsupp.embDomain_eq_mapDomain]
  rfl

theorem killCompl_X_one (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D) (v : Pl D × Fin N0 × Fin N1) :
    killCompl (embOne z N0 N1) (X v : MvPowerSeries _ ℂ_[p]) =
      if v.1 = z then X ((0 : ZMod 1), v.2) else 0 := by
  split_ifs with h
  · have hv : v = embOne z N0 N1 ((0 : ZMod 1), v.2) := Prod.ext h rfl
    conv_lhs => rw [hv]
    rw [MvPowerSeries.killCompl_X]
  · apply MvPowerSeries.killCompl_X_eq_zero
    rintro ⟨w, hw⟩
    exact h (congrArg Prod.fst hw).symm

theorem subst_killCompl_X_one (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (z : Pl D)
    {B : ZMod 1 × Fin N0 × Fin N1 → MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p]} (hB : HasSubst B)
    (v : Pl D × Fin N0 × Fin N1) :
    subst B (killCompl (embOne z N0 N1) (X v : MvPowerSeries _ ℂ_[p])) =
      if v.1 = z then B ((0 : ZMod 1), v.2) else 0 := by
  rw [killCompl_X_one]
  split_ifs with h
  · exact MvPowerSeries.subst_X hB _
  · rw [← MvPowerSeries.coe_substAlgHom hB, map_zero]

theorem pow_sq_pow_ne_zero (p : ℕ) [hp : Fact p.Prime] (e : ℕ) : (p ^ 2) ^ e ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp.out.ne_zero)

theorem constantCoeff_logPl (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) :
    constantCoeff (logPl D p v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ e ∈ Finset.range (JetTdeg (0 : Pl D × β →₀ ℕ) + 1),
    if (0 : Pl D × β →₀ ℕ) = Finsupp.single (backPl D p v.1 (2 * e), v.2) ((p ^ 2) ^ e)
    then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = 0
  simp only [JetTdeg, Finsupp.sum_zero_index, zero_add, Finset.sum_range_one, pow_zero]
  rw [if_neg]
  intro h
  exact (Finsupp.single_ne_zero.2 one_ne_zero) h.symm

theorem constantCoeff_jetLogG (p : ℕ) [Fact p.Prime] (d : ℕ) {β : Type*} (v : ZMod d × β) :
    constantCoeff (jetLogG p d v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ e ∈ Finset.range (JetTdeg (0 : ZMod d × β →₀ ℕ) + 1),
    if (0 : ZMod d × β →₀ ℕ) = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((p ^ 2) ^ e)
    then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = 0
  simp only [JetTdeg, Finsupp.sum_zero_index, zero_add, Finset.sum_range_one, pow_zero]
  rw [if_neg]
  intro h
  exact (Finsupp.single_ne_zero.2 one_ne_zero) h.symm

theorem backPl₂ (p : ℕ) (hn : nP D p = 1) (y : Pl D) (e : ℕ) : backPl D p y e = y := by
  simp [backPl, posPl, partner, hn]

theorem JetTdeg_embDomain {α β : Type*} (f : α ↪ β) (m : α →₀ ℕ) :
    JetTdeg (Finsupp.embDomain f m) = JetTdeg m := by
  unfold JetTdeg
  rw [Finsupp.sum_embDomain]

theorem coeff_logPl (p : ℕ) [Fact p.Prime] {β : Type} (v : Pl D × β) (m : Pl D × β →₀ ℕ) :
    coeff m (logPl D p v) = ∑ e ∈ Finset.range (JetTdeg m + 1),
      if m = Finsupp.single (backPl D p v.1 (2 * e), v.2) ((p ^ 2) ^ e) then (((p : ℂ_[p]) ^ e)⁻¹) else 0 := rfl

theorem coeff_jetLogG (p : ℕ) [Fact p.Prime] (d : ℕ) {β : Type*} (v : ZMod d × β) (m : ZMod d × β →₀ ℕ) :
    coeff m (jetLogG p d v) = ∑ e ∈ Finset.range (JetTdeg m + 1),
      if m = Finsupp.single (v.1 - 2 * (e : ZMod d), v.2) ((p ^ 2) ^ e) then (((p : ℂ_[p]) ^ e)⁻¹) else 0 := rfl

theorem killCompl_logPl (p : ℕ) [Fact p.Prime] (hn : nP D p = 1) {N0 N1 : ℕ} (z : Pl D)
    (v : Pl D × Fin N0 × Fin N1) :
    killCompl (embOne z N0 N1) (logPl D p v) =
      if v.1 = z then jetLogG p 1 ((0 : ZMod 1), v.2) else 0 := by
  ext m
  rw [MvPowerSeries.coeff_killCompl, coeff_logPl, JetTdeg_embDomain]
  split_ifs with h
  · rw [coeff_jetLogG]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [backPl₂ p hn]
    have key : Finsupp.embDomain (embOne z N0 N1) m = Finsupp.single (v.1, v.2) ((p ^ 2) ^ e) ↔
        m = Finsupp.single (((0 : ZMod 1), v.2).1 - 2 * (e : ZMod 1), ((0 : ZMod 1), v.2).2) ((p ^ 2) ^ e) := by
      have hv : ((v.1, v.2) : Pl D × Fin N0 × Fin N1) =
          embOne z N0 N1 (((0 : ZMod 1), v.2).1 - 2 * (e : ZMod 1), ((0 : ZMod 1), v.2).2) := Prod.ext h rfl
      rw [hv, ← Finsupp.embDomain_single, Finsupp.embDomain_inj]
    simp only [key]
    split_ifs <;> rfl
  · rw [map_zero]
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]
    intro heq
    rw [backPl₂ p hn] at heq
    have hk : (p ^ 2) ^ e ≠ 0 := pow_sq_pow_ne_zero p e
    have hmem : ((v.1, v.2) : Pl D × Fin N0 × Fin N1) ∈ (Finsupp.embDomain (embOne z N0 N1) m).support := by
      rw [heq, Finsupp.support_single_ne_zero _ hk]
      exact Finset.mem_singleton_self _
    rw [Finsupp.support_embDomain, Finset.mem_map] at hmem
    obtain ⟨w, _, hw⟩ := hmem
    exact h (congrArg Prod.fst hw).symm

theorem killCompl_expS {τ υ : Type*} {K : Type*} [Field K] [CharZero K] (e : υ ↪ τ)
    (f : MvPowerSeries τ K) (hf : constantCoeff f = 0) :
    killCompl e (OJ.expS K f) = OJ.expS K (killCompl e f) := by
  unfold OJ.expS PowerSeries.subst
  rw [PI.OrbShared.killCompl_subst e (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero hf))]

theorem constantCoeff_zero_of_jet_bound (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l])
    (h : OJ.B3 l d be) : constantCoeff be = 0 := by
  by_contra hne
  have h0 := h 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
  exact h0.1 (by simp [OJ.bideg])

end PI.OrbJet

end
