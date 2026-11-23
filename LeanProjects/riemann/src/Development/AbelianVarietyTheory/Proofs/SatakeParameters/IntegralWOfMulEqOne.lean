import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffRenameEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralSubst
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPowDivFactorialLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical
open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.CompareInert

section Letters

variable (D : D7) (p : ℕ) [Fact p.Prime]

variable {D p}

def beT (N N' : ℕ) (r : Bool × HH D) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) :
    MvPowerSeries (TeichmullerFactorisation.Var D N N') ℂ_[p] :=
  ∑ a : Fin N, ∑ b : Fin N', MvPowerSeries.subst
    (fun s : ZMod (nP D p) => TeichmullerFactorisation.zOf D p ((TeichmullerFactorisation.letter D p r s, a, b) : TeichmullerFactorisation.Var D N N')) be

end Letters

section Rings

open Formalism.MainNotions.GL3Theta

variable {l : ℕ} [Fact l.Prime]

theorem mem_Wp_of_kur {x : ℂ_[l]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) : x ∈ Wp l := by
  have hp : l.Prime := Fact.out
  have hB := ((Formalism.L2.Th1.D.kurIntegers l).1 x).2 ⟨hx, h1⟩
  have hS : Formalism.L2.Th1.D.muPrime l = {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} := by
    ext ζ
    simp only [Formalism.L2.Th1.D.muPrime, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn), h⟩
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hn), h⟩
  unfold Formalism.L2.Th1.D.ringB Formalism.L2.Th1.D.ringA at hB
  rw [hS] at hB
  exact hB

theorem Wp_subset_Kur {x : ℂ_[l]} (hx : x ∈ Wp l) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  refine closure_mono (s := ((Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} : Subring ℂ_[l]) : Set ℂ_[l])) ?_ hx
  intro y hy
  have hle : Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} ≤
      (Subfield.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro ζ ⟨n, h0, hn, h⟩
    exact Subfield.subset_closure ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (Nat.coprime_comm.mp hn), h⟩
  exact hle hy

theorem Wp_subset_Wfrac {x : ℂ_[l]} (hx : x ∈ Wp l) : x ∈ product_zeroth_first_parts.Wfrac l := by
  refine closure_mono (s := ((Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} : Subring ℂ_[l]) : Set ℂ_[l])) ?_ hx
  intro y hy
  have hle : Subring.closure {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n l ∧ ζ ^ n = 1} ≤
      (Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)).toSubring :=
    Subring.closure_le.2 fun ζ hζ => Algebra.subset_adjoin hζ
  exact hle hy

theorem exists_pow_norm_le {K : Type*} [NormedField K] {a : K} (ha : ‖a‖ < 1) (x : K) : ∃ k : ℕ, ‖a ^ k * x‖ ≤ 1 := by
  by_cases hr : x = 0
  · exact ⟨0, by simp [hr]⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hr)) ha
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_pow]
  have h0 : 0 < ‖x‖ := norm_pos_iff.2 hr
  calc ‖a‖ ^ k * ‖x‖ ≤ ‖x‖⁻¹ * ‖x‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ h0.ne'

theorem algebraMap_mem_Kur (r : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] r ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  have hl : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  obtain ⟨k, hk⟩ := exists_pow_norm_le hl r
  have h1 := Wp_subset_Kur (GlobalTheory.BiextInhab.algebraMap_mem_Wp hk)
  have h2 : algebraMap ℚ_[l] ℂ_[l] r =
      (((l : ℂ_[l]) ^ k)⁻¹) * algebraMap ℚ_[l] ℂ_[l] ((l : ℚ_[l]) ^ k * r) := by
    have hc : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    rw [map_mul, map_pow, map_natCast]
    field_simp
  rw [h2]
  exact mul_mem (inv_mem (pow_mem (natCast_mem _ l) k)) h1

def kurAlg (l : ℕ) [Fact l.Prime] : Subalgebra ℚ_[l] ℂ_[l] :=
  { (Formalism.L2.Th1.CM.MaximalUnramifiedExtension l).toSubring with
    algebraMap_mem' := algebraMap_mem_Kur }

theorem Wfrac_subset_Kur {x : ℂ_[l]} (hx : x ∈ product_zeroth_first_parts.Wfrac l) : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension l := by
  have h1 : Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) ≤ kurAlg l :=
    Algebra.adjoin_le fun ζ hζ => Wp_subset_Kur (Subring.le_topologicalClosure _ (Subring.subset_closure hζ))
  have hx' : x ∈ closure (Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) := by
    rw [← Subalgebra.topologicalClosure_coe]; exact hx
  have hc : IsClosed (Formalism.L2.Th1.CM.MaximalUnramifiedExtension l : Set ℂ_[l]) := Subfield.isClosed_topologicalClosure _
  exact closure_minimal (fun y hy => h1 hy) hc hx'

theorem norm_l_lt : ‖(l : ℂ_[l])‖ < 1 := by
  have h : ‖(l : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l]
    exact norm_algebraMap' ℂ_[l] _
  rw [h]
  exact Padic.norm_p_lt_one

theorem mem_Wint_iff {x : ℂ_[l]} : x ∈ product_zeroth_first_parts.Wint l ↔ x ∈ Wp l := by
  constructor
  · rintro ⟨h1, h2⟩
    exact mem_Wp_of_kur (Wfrac_subset_Kur h1) h2
  · intro h
    exact ⟨Wp_subset_Wfrac h, GlobalTheory.UnitModel.norm_le_one_of_mem_Wp h⟩

theorem mem_Wfrac_iff {x : ℂ_[l]} : x ∈ product_zeroth_first_parts.Wfrac l ↔ InWf x := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_pow_norm_le (norm_l_lt) x
    exact ⟨k, mem_Wp_of_kur (mul_mem (pow_mem (natCast_mem _ l) k) (Wfrac_subset_Kur h)) hk⟩
  · rintro ⟨k, hk⟩
    have hc : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    have h1 := Wp_subset_Wfrac hk
    have h2 : x = algebraMap ℚ_[l] ℂ_[l] (((l : ℚ_[l]) ^ k)⁻¹) * ((l : ℂ_[l]) ^ k * x) := by
      rw [map_inv₀, map_pow, map_natCast]
      field_simp
    rw [h2]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) h1

end Rings

section Props

open Formalism.MainNotions.GL3Theta MvPowerSeries

variable {l d : ℕ} [Fact l.Prime] [NeZero d]

def twoB (d : ℕ) : ZMod d × Fin 2 ≃ ZMod d × Bool := (Equiv.refl _).prodCongr finTwoEquiv

def cobT (r : ℕ) (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d × Fin 2) ℂ_[l] × MvPowerSeries (ZMod d × Fin 2) ℂ_[l] :=
  (subst (fun s : ZMod d => if s.val % 2 = r then jetLogG l d (s, 0) + jetLogG l d (s, 1) else jetLogG l d (s, (0 : Fin 2))) be,
   subst (fun s : ZMod d => jetLogG l d (s, (0 : Fin 2))) be +
    subst (fun s : ZMod d => if s.val % 2 = r then jetLogG l d (s, 1) else jetLogG l d (s, (0 : Fin 2))) be)

end Props

section Sign

open Formalism.MainNotions.GL3Theta MvPowerSeries

variable {l d : ℕ} [Fact l.Prime] [NeZero d]

end Sign

section Reps

variable (D : D7) (p : ℕ)

theorem posPl_back (z : Bool × HH D) (e : ℕ) : posPl D p (posPl D p z e) (e * (nP D p - 1)) = z := by
  have hn : 1 ≤ nP D p := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
  have h : e + e * (nP D p - 1) = e * nP D p := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    rw [hm]; simp; ring
  rw [posPl_add, h, ← posPl_mod, Nat.mul_mod_left, posPl_zero]

def orbSetoid : Setoid (Bool × HH D) where
  r a b := ∃ e : ℕ, posPl D p a e = b
  iseqv :=
    ⟨fun a => ⟨0, posPl_zero D p a⟩,
      fun {a b} ⟨e, h⟩ => ⟨e * (nP D p - 1), by rw [← h]; exact posPl_back D p a e⟩,
      fun {a b c} ⟨e, h⟩ ⟨f, k⟩ => ⟨e + f, by rw [← posPl_add, h, k]⟩⟩

end Reps

section Hyp

end Hyp

section Statements

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

end Statements

section Units

open MvPowerSeries

variable {D : D7} {p : ℕ} [Fact p.Prime]

end Units

section Direction

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[l])

end Direction

section Main

variable (D : D7) {Dx : DivX D} {Tw : TwForms D}

end Main

end GlobalTheory.CompareInert
