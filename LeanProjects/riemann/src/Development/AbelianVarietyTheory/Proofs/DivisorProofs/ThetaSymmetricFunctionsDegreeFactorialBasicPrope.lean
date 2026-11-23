import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (a : R) (j : Fin N) :
    symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j := by
  have h : (Finset.univ.val.map fun b => a * c b) = (Finset.univ.val.map c).map (fun x => a • x) := by
    rw [Multiset.map_map]; rfl
  have hd : ((j : ℕ) + 1) ∣ N.factorial := Nat.dvd_factorial (Nat.succ_pos _) j.isLt
  unfold symTup
  rw [h, ← Multiset.pow_smul_esymm, smul_eq_mul, mul_pow, ← pow_mul, Nat.mul_div_cancel' hd]

theorem symTup_perm {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (fun b => c (σ b)) = symTup c := by
  have h : (Finset.univ.val.map fun b => c (σ b)) = Finset.univ.val.map c := by
    conv_rhs => rw [← Multiset.map_univ_val_equiv σ, Multiset.map_map]
    rfl
  funext j
  unfold symTup
  rw [h]

theorem map_symTup {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  have h : (Finset.univ.val.map fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  unfold symTup
  rw [h, map_pow]
  congr 1
  simp only [Multiset.esymm, map_multiset_sum, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def,
    map_multiset_prod]

theorem exists_symTup_ne_zero {K : Type} [Field K] {N : ℕ} (c : Fin N → K) (h : ∃ a, c a ≠ 0) :
    ∃ j, symTup c j ≠ 0 := by
  obtain ⟨a, ha⟩ := h
  by_contra hne
  push Not at hne
  have hc : Multiset.card (Finset.univ.val.map c) = N := by simp
  have he : ∀ k, 0 < k → k ≤ N → (Finset.univ.val.map c).esymm k = 0 := by
    intro k hk hkN
    have := hne ⟨k - 1, by omega⟩
    unfold symTup at this
    have h2 := eq_zero_of_pow_eq_zero this
    simpa [Nat.sub_add_cancel hk] using h2
  have hp : ((Finset.univ.val.map c).map fun t => Polynomial.X - Polynomial.C t).prod = Polynomial.X ^ N := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc, Finset.sum_range_succ']
    rw [Finset.sum_eq_zero]
    · simp [Multiset.esymm]
    · intro k hk
      rw [he (k + 1) (Nat.succ_pos _) (Finset.mem_range.1 hk)]
      simp
  have hev := congrArg (Polynomial.eval (c a)) hp
  rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero] at hev
  · simp only [Polynomial.eval_pow, Polynomial.eval_X] at hev
    exact pow_ne_zero N ha hev.symm
  · simp only [Multiset.mem_map]
    exact ⟨_, ⟨c a, ⟨a, Finset.mem_univ_val a, rfl⟩, rfl⟩, by simp⟩

theorem symTup_basic :
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (a : R) (j : Fin N),
      symTup (fun b => a * c b) j = a ^ N.factorial * symTup c j) ∧
    (∀ (R : Type) [CommRing R] (N : ℕ) (c : Fin N → R) (σ : Equiv.Perm (Fin N)),
      symTup (fun b => c (σ b)) = symTup c) ∧
    (∀ (R R' : Type) [CommRing R] [CommRing R'] (i : R →+* R') (N : ℕ) (c : Fin N → R) (j : Fin N),
      i (symTup c j) = symTup (fun b => i (c b)) j) ∧
    ∀ (K : Type) [Field K] (N : ℕ) (c : Fin N → K), (∃ a, c a ≠ 0) → ∃ j, symTup c j ≠ 0 :=
  ⟨fun _ _ _ c a j => symTup_mul c a j, fun _ _ _ c σ => symTup_perm c σ,
    fun _ _ _ _ i _ c j => map_symTup i c j, fun _ _ _ c h => exists_symTup_ne_zero c h⟩

end GlobalTheory.UMin
