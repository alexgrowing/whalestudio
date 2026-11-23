import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData

namespace GlobalTheory.DiscEval

open PowerSeries Finset

variable {p : ℕ} {A K C B : Type*} [CommRing A] [CommRing K] [CommRing C] [CommRing B]
  {i : C →+* B} {κ : K →+* B} {a : A →+* K}

theorem OnDisc.shiftSeries {L : PowerSeries K} (hL : OnDisc p a L) :
    OnDisc p a (PowerSeries.mk fun k => coeff (k + 1) L) := fun M hM => by
  obtain ⟨D, hD⟩ := hL M hM
  refine ⟨D + 1, fun k => ?_⟩
  obtain ⟨b, hb⟩ := hD (k + 1)
  have h1 : D + (k + 1) / M ≤ D + 1 + k / M := by
    rw [Nat.succ_div]
    split_ifs <;> omega
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le h1
  refine ⟨(p : A) ^ e * b, ?_⟩
  rw [coeff_mk, he, pow_add, map_mul, map_pow, map_natCast, ← hb]
  ring

theorem Tends.shiftIndex {s : ℕ → B} {y : B} (h : Tends p i s y) : Tends p i (fun n => s (n + 1)) y :=
  fun r => (h r).imp fun N hN n hn => hN (n + 1) (by omega)

theorem psum_succ_shift (L : PowerSeries K) (x : B) (n : ℕ) :
    psum κ L x (n + 1) = κ (coeff 0 L) + x * psum κ (PowerSeries.mk fun k => coeff (k + 1) L) x n := by
  have e : ∀ k ∈ range n, κ (coeff (k + 1) L) * x ^ (k + 1) =
      x * (κ (coeff k (PowerSeries.mk fun k => coeff (k + 1) L)) * x ^ k) := fun k _ => by
    rw [coeff_mk, pow_succ]
    ring
  rw [psum, psum, sum_range_succ', sum_congr rfl e, ← Finset.mul_sum, pow_zero, mul_one, add_comm]

theorem IsEval.shift [IsHausdorff (Ideal.span {(p : C)}) C] (hi : Function.Injective i) (hp : IsUnit (p : B))
    {L : PowerSeries K} {x : C} {y u : B} (h : IsEval p i κ L (i x) y)
    (hu : IsEval p i κ (PowerSeries.mk fun k => coeff (k + 1) L) (i x) u) :
    y = κ (coeff 0 L) + i x * u := by
  have h1 : Tends p i (fun n => psum κ L (i x) (n + 1)) (κ (coeff 0 L) + i x * u) := by
    have := Tends.add (Tends.const (p := p) (i := i) (κ (coeff 0 L)))
      (Tends.mul_left hp ⟨0, x, by rw [pow_zero, one_mul]⟩ hu)
    simpa only [psum_succ_shift] using this
  exact Tends.unique hi (Tends.shiftIndex h) h1

end GlobalTheory.DiscEval

namespace GlobalTheory.AcrisK

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

theorem ev_shift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : PowerSeries ↥K.1), OnDisc l (oK K) L →
    ∀ (x : AK K), thetaK K x = 0 → ∀ y : GlobalTheory.AcrisK.BK K, Ev L x y →
    ∃ (L' : PowerSeries ↥K.1) (u : GlobalTheory.AcrisK.BK K), OnDisc l (oK K) L' ∧
      (∀ k, PowerSeries.coeff k L' = PowerSeries.coeff (k + 1) L) ∧ Ev L' x u ∧
      y = inK K (PowerSeries.coeff 0 L) + toB K (ofA K x) * u := by
  intro l _ K L hL x hx y hy
  have hL' := OnDisc.shiftSeries hL
  obtain ⟨u, hu, -⟩ := existsUnique_ev hL' hx
  exact ⟨_, u, hL', fun k => PowerSeries.coeff_mk _ _, hu,
    IsEval.shift (toB_injective K) (isUnit_l K) hy hu⟩

end GlobalTheory.AcrisK
