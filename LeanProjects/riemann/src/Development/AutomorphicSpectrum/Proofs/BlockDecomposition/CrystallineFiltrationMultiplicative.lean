import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

noncomputable section

namespace GlobalTheory.CompanionTheory.FilMul

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem divided_power_xi_zero : A.dxi0 0 = 1 := Subtype.ext (by simp [PAlg.dxi0, dpw])

theorem factorial_mul_dpw (k : ℕ) :
    (k.factorial : WL l A.A) * dpw k A.xi = algebraMap A.W (WL l A.A) A.xi ^ k := by
  rw [dpw, ← mul_assoc, Ring.mul_inverse_cancel _ (A.isUnit_natCast k.factorial_ne_zero), one_mul]

theorem factorial_mul_divided_power_xi (k : ℕ) :
    (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k :=
  Subtype.ext (by
    have h := factorial_mul_dpw A k
    simpa [PAlg.dxi0] using h)

theorem divided_power_xi_mul (i j : ℕ) :
    A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j) := by
  apply Subtype.ext
  show dpw i A.xi * dpw j A.xi = (((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi
  have hi := A.isUnit_natCast i.factorial_ne_zero
  have hj := A.isUnit_natCast j.factorial_ne_zero
  have h : (((i + j).choose i : ℕ) : WL l A.A) * (i.factorial : WL l A.A) * (j.factorial : WL l A.A)
      = ((i + j).factorial : WL l A.A) := by
    rw [Nat.choose_symm_add, ← Nat.cast_mul, ← Nat.cast_mul,
      Nat.add_choose_mul_factorial_mul_factorial i j]
  apply hj.mul_left_cancel
  apply hi.mul_left_cancel
  calc (i.factorial : WL l A.A) * ((j.factorial : WL l A.A) * (dpw i A.xi * dpw j A.xi))
      = ((i.factorial : WL l A.A) * dpw i A.xi) * ((j.factorial : WL l A.A) * dpw j A.xi) := by ring
    _ = ((i + j).factorial : WL l A.A) * dpw (i + j) A.xi := by
        rw [factorial_mul_dpw, factorial_mul_dpw, factorial_mul_dpw, pow_add]
    _ = (i.factorial : WL l A.A) * ((j.factorial : WL l A.A)
          * ((((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi)) := by
        rw [← h]; ring

theorem Fil0_zero : A.Fil0 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨0, le_rfl, (divided_power_xi_zero A).symm⟩)

theorem Fil0_mul_le (r s : ℕ) : A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s) := by
  unfold PAlg.Fil0
  rw [Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
  show A.dxi0 i * A.dxi0 j ∈ Ideal.span _
  rw [divided_power_xi_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i + j, by omega, rfl⟩)

theorem Fil_eq_map (n r : ℕ) : A.Fil n r = (A.Fil0 r).map (A.mkAcr n) := by
  unfold PAlg.Fil PAlg.Fil0
  rw [Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem PFil_eq_map (n : ℕ) : A.PFil n = A.PFil0.map (A.mkAcr n) := by
  rw [PAlg.PFil, PAlg.PFil0, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast,
    Fil_eq_map]

theorem Fil_zero (n : ℕ) : A.Fil n 0 = ⊤ := by
  rw [Fil_eq_map, Fil0_zero, Ideal.map_top]

theorem Fil_mul_le (n r s : ℕ) : A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) := by
  rw [Fil_eq_map, Fil_eq_map, Fil_eq_map, ← Ideal.map_mul]
  exact Ideal.map_mono (Fil0_mul_le A r s)

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.Fil0 0 = ⊤ ∧
    (∀ i j, A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j)) ∧
    (∀ k, (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k) ∧
    (∀ r s, A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s)) ∧
    (∀ n r, A.Fil n r = (A.Fil0 r).map (A.mkAcr n)) ∧
    (∀ n, A.PFil n = A.PFil0.map (A.mkAcr n)) ∧
    (∀ n, A.Fil n 0 = ⊤) ∧ ∀ n r s, A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) :=
  fun A => ⟨Fil0_zero A, divided_power_xi_mul A, factorial_mul_divided_power_xi A, Fil0_mul_le A, Fil_eq_map A,
    PFil_eq_map A, Fil_zero A, Fil_mul_le A⟩

end GlobalTheory.CompanionTheory.FilMul
