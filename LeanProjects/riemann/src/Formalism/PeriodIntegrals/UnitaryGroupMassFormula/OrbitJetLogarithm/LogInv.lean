import Formalism.PeriodIntegrals.OrbJetBase
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.ExpSum

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries

variable (p : ℕ) [Fact p.Prime]

def Lp : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => ∑ e ∈ Finset.range (n + 1), if n = (p ^ 2) ^ e then ((p : ℂ_[p]) ^ e)⁻¹ else 0

theorem Lp_const : PowerSeries.constantCoeff (Lp p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Lp]

theorem Lp_one : PowerSeries.coeff 1 (Lp p) = 1 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have h : (1 : ℕ) ≠ (p ^ 2) ^ 1 := by
    rw [pow_one]; exact (Nat.one_lt_pow two_ne_zero hp).ne
  simp [Lp, Finset.sum_range_succ]
  intro h'
  have := Nat.one_lt_pow two_ne_zero hp
  omega

instance Lp_inv : Invertible (PowerSeries.coeff 1 (Lp p)) :=
  invertibleOfNonzero (by rw [Lp_one]; exact one_ne_zero)

def Ep : PowerSeries ℂ_[p] := PowerSeries.substInv (Lp p)

theorem Ep_const : PowerSeries.constantCoeff (Ep p) = 0 := PowerSeries.constantCoeff_substInv _

theorem Ep_Lp : PowerSeries.subst (Lp p) (Ep p) = PowerSeries.X :=
  PowerSeries.subst_substInv_left _ (Lp_const p)

theorem Lp_Ep : PowerSeries.subst (Ep p) (Lp p) = PowerSeries.X :=
  PowerSeries.subst_substInv_right _ (Lp_const p)

theorem hs_Lp : PowerSeries.HasSubst (Lp p) := PowerSeries.HasSubst.of_constantCoeff_zero' (Lp_const p)
theorem hs_Ep : PowerSeries.HasSubst (Ep p) := PowerSeries.HasSubst.of_constantCoeff_zero' (Ep_const p)

variable {τ : Type*}

theorem cc_psubst (g : MvPowerSeries τ ℂ_[p]) (hg : constantCoeff g = 0) (f : PowerSeries ℂ_[p])
    (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (PowerSeries.subst g f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hg f hf

def phiA (c : ℂ_[p]) : τ → MvPowerSeries τ ℂ_[p] :=
  fun v => C c * PowerSeries.subst (X v) (Lp p)

def psiA (c : ℂ_[p]) : τ → MvPowerSeries τ ℂ_[p] :=
  fun v => PowerSeries.subst (C c⁻¹ * X v) (Ep p)

variable [Finite τ]

theorem hs_phiA (c : ℂ_[p]) : HasSubst (phiA p c (τ := τ)) :=
  hasSubst_of_constantCoeff_zero fun v => by
    simp only [phiA, map_mul, cc_psubst p _ (constantCoeff_X v) _ (Lp_const p), mul_zero]

theorem hs_psiA (c : ℂ_[p]) : HasSubst (psiA p c (τ := τ)) :=
  hasSubst_of_constantCoeff_zero fun v => cc_psubst p _ (by simp) _ (Ep_const p)

theorem phi_psi_X (c : ℂ_[p]) (hc : c ≠ 0) (v : τ) :
    subst (phiA p c) (psiA p c v) = X v := by
  have hX : PowerSeries.HasSubst (C c⁻¹ * X v : MvPowerSeries τ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [psiA, PI.OrbShared.ExpSum.subst_psubst (hs_phiA p c) hX, subst_mul (hs_phiA p c), subst_X (hs_phiA p c)]
  have hC : subst (phiA p c) (C c⁻¹ : MvPowerSeries τ ℂ_[p]) = C c⁻¹ := by
    exact subst_C _
  rw [hC, phiA, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul,
    ← PowerSeries.subst_comp_subst_apply (hs_Lp p) (PowerSeries.HasSubst.X v), Ep_Lp,
    PowerSeries.subst_X (PowerSeries.HasSubst.X v)]

theorem psi_phi_X (c : ℂ_[p]) (hc : c ≠ 0) (v : τ) :
    subst (psiA p c) (phiA p c v) = X v := by
  have hX : PowerSeries.HasSubst (X v : MvPowerSeries τ ℂ_[p]) := PowerSeries.HasSubst.X v
  have hX' : PowerSeries.HasSubst (C c⁻¹ * X v : MvPowerSeries τ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hC : subst (psiA p c) (C c : MvPowerSeries τ ℂ_[p]) = C c := by
    exact subst_C _
  rw [phiA, subst_mul (hs_psiA p c), hC, PI.OrbShared.ExpSum.subst_psubst (hs_psiA p c) hX,
    subst_X (hs_psiA p c), psiA, ← PowerSeries.subst_comp_subst_apply (hs_Ep p) hX', Lp_Ep,
    PowerSeries.subst_X hX', ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]

theorem phi_psi (c : ℂ_[p]) (hc : c ≠ 0) (F : MvPowerSeries τ ℂ_[p]) :
    subst (phiA p c) (subst (psiA p c) F) = F := by
  rw [subst_comp_subst_apply (hs_psiA p c) (hs_phiA p c)]
  simp only [phi_psi_X p c hc]
  exact congrFun subst_self F

theorem psi_phi (c : ℂ_[p]) (hc : c ≠ 0) (F : MvPowerSeries τ ℂ_[p]) :
    subst (psiA p c) (subst (phiA p c) F) = F := by
  rw [subst_comp_subst_apply (hs_phiA p c) (hs_psiA p c)]
  simp only [psi_phi_X p c hc]
  exact congrFun subst_self F

omit [Finite τ] in
theorem coeff_X_Lp (v : τ) (m : τ →₀ ℕ) :
    coeff m (PowerSeries.subst (X v : MvPowerSeries τ ℂ_[p]) (Lp p)) =
      ∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1),
        if m = Finsupp.single v ((p ^ 2) ^ e) then ((p : ℂ_[p]) ^ e)⁻¹ else 0 := by
  by_cases h : ∃ n, m = Finsupp.single v n
  · obtain ⟨n, rfl⟩ := h
    rw [PowerSeries.coeff_subst_single, if_pos (by simp)]
    have hT : Formalism.BasicNotions.JetTdeg (Finsupp.single v n) = n := by
      simp [Formalism.BasicNotions.JetTdeg, Finsupp.sum_single_index]
    simp only [Finsupp.single_eq_same, Lp, PowerSeries.coeff_mk, hT]
    refine Finset.sum_congr rfl fun e _ => ?_
    have : Finsupp.single v n = Finsupp.single v ((p ^ 2) ^ e) ↔ n = (p ^ 2) ^ e :=
      ⟨fun h => by simpa using congrArg (fun f => f v) h, fun h => h ▸ rfl⟩
    simp only [this]
  · rw [PowerSeries.coeff_subst_single, if_neg (fun h' => h ⟨_, h'⟩)]
    symm
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨_, h'⟩

theorem jetLogG_one {β : Type*} (v : ZMod 1 × β) :
    Formalism.BasicNotions.jetLogG p 1 v = PowerSeries.subst (X v : MvPowerSeries (ZMod 1 × β) ℂ_[p]) (Lp p) := by
  ext m
  rw [coeff_X_Lp]
  have h : ∀ e : ℕ, ((v.1 - 2 * (e : ZMod 1), v.2) : ZMod 1 × β) = v :=
    fun e => Prod.ext (Subsingleton.elim _ _) rfl
  show (∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod 1), v.2) ((p ^ 2) ^ e) then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = _
  simp only [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem logPl_one (D : Formalism.BasicNotions.D7) (hn : Formalism.MainNotions.G.nP D p = 1) {β : Type} (v : Pl D × β) :
    logPl D p v = PowerSeries.subst (X v : MvPowerSeries (Pl D × β) ℂ_[p]) (Lp p) := by
  ext m
  rw [coeff_X_Lp]
  have h : ∀ e : ℕ, ((backPl D p v.1 (2 * e), v.2) : Pl D × β) = v := by
    intro e
    refine Prod.ext ?_ rfl
    simp [backPl, hn, Formalism.BasicNotions.posPl_zero]
  show (∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1),
    if m = Finsupp.single (backPl D p v.1 (2 * e), v.2) ((p ^ 2) ^ e) then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = _
  simp only [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> first | rfl | (exfalso; tauto)

end PI.OrbJet.AO

end
