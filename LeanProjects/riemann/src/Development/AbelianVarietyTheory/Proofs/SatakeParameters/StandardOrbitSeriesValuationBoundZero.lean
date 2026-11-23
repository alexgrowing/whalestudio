import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.HurwitzSubstituteTwoSeries
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AddCoordExponentIntegralJetsUnramifiedStatement

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE expF xOfZ)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob lgF at1)
open Formalism.L2.KerInert.Jet (Hur fc fc_of_subset hur_subst hur_mul hur_sum hur_zero hur_neg hur_C hur_X hur_of_int hur_substInv cc_subst)

namespace GlobalTheory.KerZero

def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_ball {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} : x ∈ ball K ↔ ‖x‖ ≤ 1 := Iff.rfl

section Gen

variable {K : Type} [Field K] [CharZero K] (R : Subring K)

theorem coeff_one_lgF {l : ℕ} (hl : 2 ≤ l) : PowerSeries.coeff 1 (lgF K l) = 1 := by
  unfold lgF
  rw [PowerSeries.coeff_mk, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    have h1 : 1 < (l ^ 2) ^ j := Nat.one_lt_pow hj (Nat.one_lt_pow two_ne_zero (by omega))
    omega
  · simp

theorem cc_lgF (l : ℕ) : PowerSeries.constantCoeff (lgF K l) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold lgF
  rw [PowerSeries.coeff_mk]
  simp

theorem lgF_deriv_int {l : ℕ} (hl : 2 ≤ l) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.derivative K (lgF K l)) ∈ R := by
  rw [PowerSeries.coeff_derivative]
  unfold lgF
  rw [PowerSeries.coeff_mk, Finset.sum_mul]
  refine R.sum_mem fun j _ => ?_
  split_ifs with h
  · have hp : (l : K) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
    have e : ((n : K) + 1) = (l : K) ^ j * (l : K) ^ j := by
      rw [← pow_add, ← two_mul, pow_mul]
      exact_mod_cast h
    rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j hp), one_mul]
    exact R.pow_mem (natCast_mem R l) j
  · rw [zero_mul]
    exact R.zero_mem

theorem hur_expF {l : ℕ} (hl : 2 ≤ l) : Hur R ((expF K l : PowerSeries K) : MvPowerSeries Unit K) := by
  have hu : IsUnit (PowerSeries.coeff 1 (lgF K l)) := by rw [coeff_one_lgF hl]; exact isUnit_one
  unfold expF
  rw [dif_pos hu]
  refine hur_substInv R (cc_lgF l) hu ?_ (lgF_deriv_int R hl)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, coeff_one_lgF hl]
  simp

theorem hur_psubst {τ : Type} [Finite τ] {a : MvPowerSeries τ K} (ha0 : MvPowerSeries.constantCoeff a = 0) (ha : Hur R a)
    {g : PowerSeries K} (hg : Hur R (g : MvPowerSeries Unit K)) : Hur R (PowerSeries.subst a g) := by
  rw [PowerSeries.subst_def]
  exact hur_subst R (fun _ => ha0) (fun _ => ha) hg

theorem cc_psubst {τ : Type} [Finite τ] {a : MvPowerSeries τ K} (ha0 : MvPowerSeries.constantCoeff a = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a g) = 0 := by
  rw [PowerSeries.subst_def, cc_subst (fun _ => ha0)]
  exact hg

theorem hur_exp : Hur R ((PowerSeries.exp K : PowerSeries K) : MvPowerSeries Unit K) := by
  intro n
  have hn : n = Finsupp.single () (n ()) := by
    ext u
    simp
  have hc : MvPowerSeries.coeff n (PowerSeries.exp K : MvPowerSeries Unit K) = PowerSeries.coeff (n ()) (PowerSeries.exp K) := by
    conv_lhs => rw [hn]
    rfl
  have hf : (fc n : K) = ((n ()).factorial : K) := by
    rw [fc_of_subset (S := Finset.univ) (Finset.subset_univ _)]
    simp
  rw [hc, hf, PowerSeries.coeff_exp]
  have : ((n ()).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp [this]

end Gen

theorem hur_mvExp {K : Type} [NormedField K] [CharZero K] (R : Subring K) {τ : Type} [Finite τ] {h : MvPowerSeries τ K}
    (h0 : MvPowerSeries.constantCoeff h = 0) (hh : Hur R h) : Hur R (Formalism.DworkPowerSeriesWeights.mvExp h) :=
  hur_psubst R h0 hh (hur_exp R)

section Cp

variable {l : ℕ} [Fact l.Prime]

theorem norm_frob_le {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) {a : MaximalUnramifiedExtension l} (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by
  have h1 : ‖σ a - a ^ l‖ ≤ 1 := (hσ.2.2.2.2 a ha).trans (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  have h2 : ‖a ^ l‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have e : ((σ a : MaximalUnramifiedExtension l) : ℂ_[l]) = ((σ a - a ^ l : MaximalUnramifiedExtension l) : ℂ_[l]) + ((a ^ l : MaximalUnramifiedExtension l) : ℂ_[l]) := by
    push_cast; ring
  show ‖((σ a : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ 1
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem norm_iter_le {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) {a : MaximalUnramifiedExtension l} (ha : ‖a‖ ≤ 1) (k : ℕ) : ‖σ^[k] a‖ ≤ 1 := by
  induction k with
  | zero => simpa using ha
  | succ k ih => rw [Function.iterate_succ_apply']; exact norm_frob_le hσ ih

variable {d N0 N1 : ℕ} [NeZero d]

theorem hur_linTerm (c : ℂ_[l]) (hc : ‖c‖ ≤ 1) (v : ZMod d × Fin N0 × Fin N1) :
    Hur (ball ℂ_[l]) (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) :=
  hur_mul _ (hur_C _ hc) (hur_X _ v)

def uL (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (c : MaximalUnramifiedExtension l) (a : Fin N0) (b : Fin N1) : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l] :=
  ∑ s : ZMod d, if s.val % 2 = 0 then
    MvPowerSeries.C ((MaximalUnramifiedExtension l).subtype (σ^[s.val] c)) * (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) else 0

def vL (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (c : MaximalUnramifiedExtension l) (a : Fin N0) (b : Fin N1) : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l] :=
  ∑ s : ZMod d, if s.val % 2 = 0 then 0 else
    MvPowerSeries.C ((MaximalUnramifiedExtension l).subtype (σ^[s.val] c)) * (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l])

theorem uL_spec {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) {c : MaximalUnramifiedExtension l} (hc : ‖c‖ ≤ 1) (a : Fin N0) (b : Fin N1) :
    Hur (ball ℂ_[l]) (uL (d := d) σ c a b) ∧ MvPowerSeries.constantCoeff (uL (d := d) σ c a b) = 0 := by
  constructor
  · refine hur_sum _ _ _ fun s _ => ?_
    split_ifs
    · exact hur_linTerm _ (norm_iter_le hσ hc _) _
    · exact hur_zero _
  · unfold uL
    rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs <;> simp

theorem vL_spec {σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l} (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) {c : MaximalUnramifiedExtension l} (hc : ‖c‖ ≤ 1) (a : Fin N0) (b : Fin N1) :
    Hur (ball ℂ_[l]) (vL (d := d) σ c a b) ∧ MvPowerSeries.constantCoeff (vL (d := d) σ c a b) = 0 := by
  constructor
  · refine hur_sum _ _ _ fun s _ => ?_
    split_ifs
    · exact hur_zero _
    · exact hur_linTerm _ (norm_iter_le hσ hc _) _
  · unfold vL
    rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs <;> simp

theorem cc_expF (hl : 2 ≤ l) : PowerSeries.constantCoeff (expF ℂ_[l] l) = 0 :=
  (Formalism.L2.Th1.D.expSpec ℂ_[l] l hl).1

variable {ι : Type}

theorem xOfZ_false (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (om oms : ι → MaximalUnramifiedExtension l) (r : ι) (a : Fin N0) (b : Fin N1) :
    xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms (false, r, a, b) = PowerSeries.subst (uL (d := d) σ (oms r) a b) (expF ℂ_[l] l) := by
  simp [xOfZ, uL]

theorem xOfZ_true (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (om oms : ι → MaximalUnramifiedExtension l) (r : ι) (a : Fin N0) (b : Fin N1) :
    xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms (true, r, a, b) = PowerSeries.subst (vL (d := d) σ (om r) a b) (expF ℂ_[l] l) := by
  simp [xOfZ, vL]

theorem xOfZ_spec (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (om oms : ι → MaximalUnramifiedExtension l)
    (hO : ∀ r, ‖om r‖ ≤ 1 ∧ ‖oms r‖ ≤ 1) (x : Bool × ι × Fin N0 × Fin N1) :
    Hur (ball ℂ_[l]) (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms x) ∧
      MvPowerSeries.constantCoeff (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms x) = 0 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨t, r, a, b⟩ := x
  cases t
  · rw [xOfZ_false]
    have h := uL_spec (d := d) hσ (hO r).2 a b
    exact ⟨hur_psubst _ h.2 h.1 (hur_expF _ hl), cc_psubst h.2 (cc_expF hl)⟩
  · rw [xOfZ_true]
    have h := vL_spec (d := d) hσ (hO r).1 a b
    exact ⟨hur_psubst _ h.2 h.1 (hur_expF _ hl), cc_psubst h.2 (cc_expF hl)⟩

theorem hur_addC (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (h : ∀ n : Fin 2 →₀ ℕ, ‖(((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) * MvPowerSeries.coeff n (addC l be0)‖ ≤ 1) :
    Hur (ball ℂ_[l]) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (addC l be0)) := by
  intro n
  have hf : (fc n : ℂ_[l]) = (((n 0).factorial * (n 1).factorial : ℕ) : ℂ_[l]) := by
    rw [fc_of_subset (S := Finset.univ) (Finset.subset_univ _), Fin.prod_univ_two]
    push_cast
    rfl
  rw [hf, MvPowerSeries.coeff_map]
  have := h n
  rw [mem_ball]
  simpa using this

theorem map_addC (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) :
    MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (addC l be0) =
      MvPowerSeries.subst ![at1 (0 : Fin 2) (expF ℂ_[l] l), at1 (1 : Fin 2) (expF ℂ_[l] l)]
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hcc : ∀ (K : Type) [Field K] [CharZero K] (i : Fin 2), MvPowerSeries.constantCoeff (at1 i (expF K l)) = 0 :=
    fun K _ _ i => cc_psubst (by simp) (Formalism.L2.Th1.D.expSpec K l hl).1
  unfold addC
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    fin_cases i
    · exact hcc _ 0
    · exact hcc _ 1))]
  congr 1
  funext i
  have hat : ∀ i : Fin 2, MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (at1 i (expF (MaximalUnramifiedExtension l) l)) = at1 i (expF ℂ_[l] l) := by
    intro i
    unfold at1
    have := PowerSeries.map_subst (PowerSeries.HasSubst.X (S := MaximalUnramifiedExtension l) i) (h := (MaximalUnramifiedExtension l).subtype) (expF (MaximalUnramifiedExtension l) l)
    rw [this, Formalism.L2.Th1.Top.PAdicPowerSeriesCoefficients.map_expF _ hl, MvPowerSeries.map_X]
  fin_cases i
  · exact hat 0
  · exact hat 1

end Cp

section Main

variable {l : ℕ} [Fact l.Prime] {d N0 N1 : ℕ} [NeZero d] {ι : Type} [Fintype ι]

theorem hur_pair (u v : MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) (hu : Hur (ball ℂ_[l]) u)
    (hu0 : MvPowerSeries.constantCoeff u = 0) (hv : Hur (ball ℂ_[l]) v) (hv0 : MvPowerSeries.constantCoeff v = 0)
    (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (hb : Hur (ball ℂ_[l]) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (addC l be0))) :
    Hur (ball ℂ_[l]) (MvPowerSeries.subst ![PowerSeries.subst u (expF ℂ_[l] l), PowerSeries.subst v (expF ℂ_[l] l)]
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0)) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff ((![u, v] : Fin 2 → MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) i) = 0 := by
    intro i; fin_cases i
    · exact hu0
    · exact hv0
  have h1 : ∀ i : Fin 2, Hur (ball ℂ_[l]) ((![u, v] : Fin 2 → MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) i) := by
    intro i; fin_cases i
    · exact hu
    · exact hv
  have hs2 := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  have hc : ∀ i : Fin 2, MvPowerSeries.constantCoeff (at1 i (expF ℂ_[l] l)) = 0 :=
    fun i => cc_psubst (by simp) (cc_expF hl)
  have hs1 : MvPowerSeries.HasSubst (![at1 (0 : Fin 2) (expF ℂ_[l] l), at1 (1 : Fin 2) (expF ℂ_[l] l)] :
      Fin 2 → MvPowerSeries (Fin 2) ℂ_[l]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
      fin_cases i
      · exact hc 0
      · exact hc 1)
  have hat : ∀ i : Fin 2, MvPowerSeries.subst ![u, v] (at1 i (expF ℂ_[l] l)) =
      PowerSeries.subst ((![u, v] : Fin 2 → MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]) i) (expF ℂ_[l] l) := by
    intro i
    unfold at1
    rw [PowerSeries.subst_def, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)) hs2]
    congr 1
    funext _
    rw [MvPowerSeries.subst_X hs2]
  have e : MvPowerSeries.subst ![PowerSeries.subst u (expF ℂ_[l] l), PowerSeries.subst v (expF ℂ_[l] l)]
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0) =
      MvPowerSeries.subst ![u, v] (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (addC l be0)) := by
    rw [map_addC, MvPowerSeries.subst_comp_subst_apply hs1 hs2]
    congr 1
    funext i
    fin_cases i
    · exact (hat 0).symm
    · exact (hat 1).symm
  rw [e]
  exact hur_subst _ h0 h1 hb

theorem subst_sumE {a : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries (ZMod d × Fin N0 × Fin N1) ℂ_[l]}
    (ha : ∀ x, MvPowerSeries.constantCoeff (a x) = 0) (B : MvPowerSeries (Fin 2) ℂ_[l]) :
    MvPowerSeries.subst a (sumE (ι := ι) (N0 := N0) (N1 := N1) B) =
      ∑ e : ι × Fin N0 × Fin N1, MvPowerSeries.subst ![a (false, e), a (true, e)] B := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  unfold sumE
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hs,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)) hs]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X hs]
  fin_cases i <;> simp

theorem cc_sumE (B : MvPowerSeries (Fin 2) ℂ_[l]) (h : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.constantCoeff (sumE (ι := ι) (N0 := N0) (N1 := N1) B) = 0 := by
  unfold sumE
  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [cc_subst (fun _ => by simp), h]

theorem hur_theta (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l))
    (hb0 : MvPowerSeries.constantCoeff be0 = 0)
    (hj : ∀ n : Fin 2 →₀ ℕ, ‖(((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) * MvPowerSeries.coeff n (addC l be0)‖ ≤ 1)
    (om oms : ι → MaximalUnramifiedExtension l) (hO : ∀ r, ‖om r‖ ≤ 1 ∧ ‖oms r‖ ≤ 1)
    (U0 : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) ℂ_[l]) (hU : Formalism.DworkPowerSeriesWeights.Integral U0) :
    Hur (ball ℂ_[l]) (thetaInZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms
      (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) * U0)) := by
  have ha0 : ∀ x : Bool × ι × Fin N0 × Fin N1, MvPowerSeries.constantCoeff (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms x) = 0 :=
    fun x => (xOfZ_spec σ hσ om oms hO x).2
  have ha1 : ∀ x : Bool × ι × Fin N0 × Fin N1, Hur (ball ℂ_[l]) (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms x) :=
    fun x => (xOfZ_spec σ hσ om oms hO x).1
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hB0 : MvPowerSeries.constantCoeff (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hb0, map_zero]
  have hS0 := cc_sumE (ι := ι) (N0 := N0) (N1 := N1) _ hB0
  have hadd := hur_addC be0 hj
  have hS : Hur (ball ℂ_[l]) (MvPowerSeries.subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l (MaximalUnramifiedExtension l).subtype σ om oms)
      (sumE (ι := ι) (N0 := N0) (N1 := N1) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) := by
    rw [subst_sumE ha0]
    refine hur_sum _ _ _ fun e _ => ?_
    obtain ⟨r, a, b⟩ := e
    rw [xOfZ_false, xOfZ_true]
    have h1 := uL_spec (d := d) hσ (hO r).2 a b
    have h2 := vL_spec (d := d) hσ (hO r).1 a b
    exact hur_pair _ _ h1.1 h1.2 h2.1 h2.2 be0 hadd
  unfold thetaInZ
  rw [MvPowerSeries.subst_mul hs]
  refine hur_mul _ ?_ (hur_subst _ ha0 ha1 (hur_of_int _ hU))
  have hN : MvPowerSeries.constantCoeff (-(sumE (ι := ι) (N0 := N0) (N1 := N1) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) = 0 := by
    rw [map_neg, hS0, neg_zero]
  unfold Formalism.DworkPowerSeriesWeights.mvExp
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hN)) hs]
  have hneg : MvPowerSeries.subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l (MaximalUnramifiedExtension l).subtype σ om oms)
      (-(sumE (ι := ι) (N0 := N0) (N1 := N1) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) =
      -MvPowerSeries.subst (xOfZ (d := d) (N0 := N0) (N1 := N1) l (MaximalUnramifiedExtension l).subtype σ om oms)
        (sumE (ι := ι) (N0 := N0) (N1 := N1) (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0)) := by
    rw [← MvPowerSeries.coe_substAlgHom hs, map_neg]
  refine hur_subst _ (fun _ => ?_) (fun _ => ?_) (hur_exp _)
  · rw [cc_subst ha0, hN]
  · rw [hneg]
    exact hur_neg _ hS

theorem jets_of_scaled {τ : Type} [Finite τ] (ep : ℂ_[l]) (hep : ‖ep‖ = 1) (Th : MvPowerSeries τ ℂ_[l])
    (h : Hur (ball ℂ_[l]) (MvPowerSeries.subst (fun v : τ => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries τ ℂ_[l])) Th))
    (n : τ →₀ ℕ) : ‖(fc n : ℂ_[l]) * MvPowerSeries.coeff n Th‖ ≤ 1 := by
  have e : (fun v : τ => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries τ ℂ_[l])) =
      ((fun _ : τ => ep) • (MvPowerSeries.X : τ → MvPowerSeries τ ℂ_[l])) := by
    funext v
    simp [MvPowerSeries.smul_eq_C_mul]
  have hn := h n
  rw [e, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale, mem_ball, norm_mul, norm_mul] at hn
  have hp : ‖n.prod fun _ m => ep ^ m‖ = 1 := by
    unfold Finsupp.prod
    rw [norm_prod]
    exact Finset.prod_eq_one fun x _ => by rw [norm_pow, hep, one_pow]
  rw [norm_mul]
  simpa [hp] using hn

end Main

theorem kvalGe_zero : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]), ‖ep‖ = 1 → BeStd Lc.l Lc.d be → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) be → product_zeroth_first_parts.KvalGe Lc.N0 Lc.N1 Lc.l Lc.nu Lc.Th 0 := by
  rintro Lc ep be hep ⟨σ, F, be0, om, oms, ζ, hD, rfl⟩ hB
  obtain ⟨U0, hU, hTh⟩ := GlobalTheory.T.exists_integral_orbit_series Lc ep σ F be0 om oms ζ hD hB
  obtain ⟨hσ, hF, h1, h2, hO, hT, -⟩ := hD
  have hb0 : MvPowerSeries.constantCoeff be0 = 0 := h1.1 0 (Or.inl rfl)
  have hH := hur_theta (d := Lc.d) (N0 := Lc.N0) (N1 := Lc.N1) σ hσ be0 hb0 (GlobalTheory.T.addCoord_exponent_integral_jets_unramified Lc.l σ F be0 hσ hF h1 h2) om oms hO.1 U0 hU
  rw [← hTh] at hH
  have hJ := jets_of_scaled ep hep Lc.Th hH
  intro I m
  rw [neg_zero, Real.rpow_zero]
  unfold product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine (ball ℂ_[Lc.l]).sum_mem fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc]
    exact (ball ℂ_[Lc.l]).mul_mem (intCast_mem _ _) (hJ _)
  · exact (ball ℂ_[Lc.l]).zero_mem

end GlobalTheory.KerZero
