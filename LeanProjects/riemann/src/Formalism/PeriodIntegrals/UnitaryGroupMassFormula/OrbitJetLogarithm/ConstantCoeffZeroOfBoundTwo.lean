import Formalism.PeriodIntegrals.OrbAddOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetRen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ProdMonomialOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ApplyAt0EqZeroOfOrder

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet.OJ

variable {p : ℕ} [Fact p.Prime]

def ptE (D : D7) (z : Pl D) : ZMod 1 ↪ Pl D := ⟨fun _ => z, fun a b _ => Subsingleton.elim a b⟩

@[simp] theorem ptE_apply (D : D7) (z : Pl D) (s : ZMod 1) : ptE D z s = z := rfl

def gSub {τ : Type*} (ep : ℂ_[p]) (v : τ) : ZMod 2 → MvPowerSeries τ ℂ_[p] :=
  fun s => if s = 0 then (X v : MvPowerSeries τ ℂ_[p]) else C ep * X v

theorem hs_gSub {τ : Type*} (ep : ℂ_[p]) (v : τ) : HasSubst (gSub ep v) := by
  have h0 : ∀ s, constantCoeff (gSub (p := p) ep v s) = 0 := fun s => by
    unfold gSub
    split_ifs <;> simp
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  | exact ⟨fun s => by rw [h0 s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩

theorem cc_gSub {τ : Type*} (ep : ℂ_[p]) (v : τ) (be : MvPowerSeries (ZMod 2) ℂ_[p])
    (hbe : constantCoeff be = 0) : constantCoeff (subst (gSub ep v) be) = 0 := by
  have h0 : ∀ s, constantCoeff (gSub (p := p) ep v s) = 0 := fun s => by
    unfold gSub
    split_ifs <;> simp
  first
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hs_gSub ep v) h0 hbe
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hs_gSub ep v) hbe h0
  | (rw [MvPowerSeries.constantCoeff_subst (hs_gSub ep v)]
     apply finsum_eq_zero_of_forall_eq_zero
     intro d
     by_cases hd : d = 0
     · subst hd
       simp [hbe]
     · obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 hd
       simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
       rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 hs)]
       · simp
       · simp [h0 s, zero_pow hs])

theorem constantCoeff_zero_of_bound_two (be : MvPowerSeries (ZMod 2) ℂ_[p]) (h : OJ.B3 p 2 be) : constantCoeff be = 0 := by
  by_contra hne
  have h0 := h 0 (by simpa using hne)
  simp [bideg] at h0

def f1 (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  (sg / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub ep ((0 : ZMod 1), a, b)) be

def fAll (D : D7) (N0 N1 : ℕ) (ep sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) :
    MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ z : Pl D, (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub (ep z) (z, a, b)) (be z)

theorem constantCoeff_jet_series (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) (hbe : constantCoeff be = 0) :
    constantCoeff (f1 N0 N1 ep sg be) = 0 := by
  simp [f1, cc_gSub _ _ _ hbe]

theorem rename_jet_series (D : D7) (z : Pl D) (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) :
    rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (f1 N0 N1 ep sg be) =
      (sg / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub ep (z, a, b)) be := by
  simp only [f1, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [rename_subst' _ (hs_gSub _ _)]
  congr 1
  funext s
  unfold gSub
  split_ifs
  · rw [rename_X]
    rfl
  · simp [rename_X]
    left
    rfl

def Y1 (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  subst (jetLogG p 1 (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (f1 N0 N1 ep sg be))

def T1 (N0 N1 : ℕ) (c ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) (j : ZMod 1 × Fin N0 × Fin N1 →₀ ℕ) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  subst (psiA p c) (monomial j 1 * Y1 N0 N1 ep sg be)

theorem jetLog_eq_phiA (N0 N1 : ℕ) (c : ℂ_[p]) :
    (fun v : ZMod 1 × Fin N0 × Fin N1 => C c * jetLogG p 1 v) = phiA p c := by
  funext v
  simp [phiA, jetLogG_one]

theorem subst_log_jet_monomial (N0 N1 : ℕ) (c ep sg : ℂ_[p]) (hc : c ≠ 0) (be : MvPowerSeries (ZMod 2) ℂ_[p])
    (j : ZMod 1 × Fin N0 × Fin N1 →₀ ℕ) :
    subst (fun v : ZMod 1 × Fin N0 × Fin N1 => C c * jetLogG p 1 v) (T1 N0 N1 c ep sg be j) =
      monomial j 1 * Y1 N0 N1 ep sg be := by
  rw [jetLog_eq_phiA]
  unfold T1
  exact phi_psi (p := p) c hc _

end PI.OrbJet.AO

end
