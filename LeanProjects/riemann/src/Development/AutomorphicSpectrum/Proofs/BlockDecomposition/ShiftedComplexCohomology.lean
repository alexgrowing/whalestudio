import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShiftCoh

variable {K : Type} [Field K]

def ev (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m where
  toFun y := y ⟨m, h⟩
  invFun x := fun m' => (show m = m'.1 by have := m'.2; omega) ▸ x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext ⟨m', h'⟩
    obtain rfl : m' = m := by omega
    rfl
  right_inv _ := rfl

theorem ev_apply (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    ev ς k C h y = y ⟨m, h⟩ := rfl

theorem d_apply_succ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) (h' : m + 1 + k = n + 1) :
    (Sh ς k C).d n y ⟨m + 1, h'⟩ = (ς : ℤ) • C.d m (y ⟨m, h⟩) := rfl

theorem d_apply_zero (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {n : ℕ} (y : (Sh ς k C).X n) (h' : 0 + k = n + 1) :
    (Sh ς k C).d n y ⟨0, h'⟩ = 0 := rfl

theorem unit_smul_eq_zero (ς : ℤˣ) {M : Type*} [AddCommGroup M] {x : M} : (ς : ℤ) • x = 0 ↔ x = 0 := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem unit_smul_smul (ς : ℤˣ) {M : Type*} [AddCommGroup M] (x : M) : (ς : ℤ) • (ς : ℤ) • x = x := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem ext_at (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) {y z : (Sh ς k C).X n}
    (e : y ⟨m, h⟩ = z ⟨m, h⟩) : y = z :=
  (ev ς k C h).injective e

theorem mem_Z_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    (Sh ς k C).d n y = 0 ↔ C.d m (y ⟨m, h⟩) = 0 := by
  have h' : m + 1 + k = n + 1 := by omega
  constructor
  · intro e
    have := congrFun e ⟨m + 1, h'⟩
    rw [d_apply_succ ς k C h y h'] at this
    exact (unit_smul_eq_zero ς).1 this
  · intro e
    refine ext_at ς k C h' ?_
    rw [d_apply_succ ς k C h y h', e, smul_zero]
    rfl

theorem mem_B_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    y ∈ (Sh ς k C).B n ↔ y ⟨m, h⟩ ∈ C.B m := by
  cases n with
  | zero =>
    obtain rfl : m = 0 := by omega
    constructor
    · intro e
      have e' : y = 0 := e
      rw [e']
      exact Submodule.zero_mem _
    · intro e
      have e' : y ⟨0, h⟩ = 0 := e
      have : y = 0 := ext_at ς k C h e'
      rw [this]
      exact Submodule.zero_mem _
  | succ n =>
    cases m with
    | zero =>
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_zero ς k C x h]
        exact Submodule.zero_mem _
      · intro e
        have e' : y ⟨0, h⟩ = 0 := e
        have : y = 0 := ext_at ς k C h e'
        rw [this]
        exact Submodule.zero_mem _
    | succ m =>
      have h0 : m + k = n := by omega
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_succ ς k C h0 x h]
        exact ⟨(ς : ℤ) • x ⟨m, h0⟩, by rw [map_zsmul]⟩
      · rintro ⟨z, hz⟩
        refine ⟨(ev ς k C h0).symm ((ς : ℤ) • z), ext_at ς k C h ?_⟩
        rw [d_apply_succ ς k C h0 _ h]
        change (ς : ℤ) • C.d m ((ev ς k C h0) ((ev ς k C h0).symm ((ς : ℤ) • z))) = _
        rw [LinearEquiv.apply_symm_apply, map_zsmul, unit_smul_smul, hz]

def evZ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.Z m ≃ₗ[K] (Sh ς k C).Z n :=
  LinearEquiv.ofSubmodules (ev ς k C h).symm (C.Z m) ((Sh ς k C).Z n) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine (mem_Z_iff ς k C h _).2 ?_
      change C.d m ((ev ς k C h) ((ev ς k C h).symm x)) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hx
    · intro hy
      exact ⟨ev ς k C h y, (mem_Z_iff ς k C h y).1 hy, (ev ς k C h).symm_apply_apply y⟩)

theorem evZ_coe (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.Z m) :
    ev ς k C h (evZ ς k C h x).1 = x.1 :=
  (ev ς k C h).apply_symm_apply x.1

def evH (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.H m ≃ₗ[K] (Sh ς k C).H n :=
  Submodule.Quotient.equiv _ _ (evZ ς k C h) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x.1 ∈ C.B m := hx
      change (evZ ς k C h x).1 ∈ (Sh ς k C).B n
      refine (mem_B_iff ς k C h _).2 ?_
      have := evZ_coe ς k C h x
      rw [ev_apply] at this
      rw [this]
      exact hx'
    · intro hy
      have hy' : y.1 ∈ (Sh ς k C).B n := hy
      refine ⟨(evZ ς k C h).symm y, ?_, (evZ ς k C h).apply_symm_apply y⟩
      change ((evZ ς k C h).symm y).1 ∈ C.B m
      have := evZ_coe ς k C h ((evZ ς k C h).symm y)
      rw [LinearEquiv.apply_symm_apply, ev_apply] at this
      rw [← this]
      exact (mem_B_iff ς k C h _).1 hy')

theorem main : ∀ {K : Type} [Field K] (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) (n : ℕ), (n < k → Subsingleton ((Sh ς k C).H n)) ∧ ∀ (m : ℕ) (h : m + k = n), ∃ e : C.H m ≃ₗ[K] (Sh ς k C).H n, ∀ (y : (Sh ς k C).X n) (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0), e (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy := by
  intro K _ ς k C n
  refine ⟨fun hn => ?_, fun m h => ⟨evH ς k C h, fun y hy hy' => ?_⟩⟩
  · have : IsEmpty {m : ℕ // m + k = n} := ⟨fun x => by have := x.2; omega⟩
    have hX : Subsingleton ((Sh ς k C).X n) :=
      inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, C.X m.1))
    have hZ : Subsingleton ((Sh ς k C).Z n) := ⟨fun a b => Subtype.ext (hX.elim _ _)⟩
    exact Quotient.instSubsingletonQuotient _
  · refine congrArg (Submodule.Quotient.mk (p := ((Sh ς k C).B n).submoduleOf ((Sh ς k C).Z n))) (Subtype.ext ?_)
    exact (ev ς k C h).symm_apply_apply y

end GlobalTheory.CompanionTheory.KunGlue.ShiftCoh
