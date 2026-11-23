import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCrystallineUnitFrobeniusEigen
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusIterateMatrixForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

namespace UpperTheory.V

variable {l : ℕ} [Fact l.Prime]

private def slS (l : ℕ) [Fact l.Prime] : Subring (Bcr l) where
  carrier := {b | (PP l).ιB b ∈ ((PP l).PD (botExt l)).Fil 0}
  mul_mem' := fun {a b} ha hb => by
    have := ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ ha hb
    rw [add_zero, ← map_mul] at this
    exact this
  one_mem' := by
    change (PP l).ιB 1 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_one]; exact ((PP l).PD (botExt l)).one_mem
  add_mem' := fun {a b} ha hb => by
    change (PP l).ιB (a + b) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    change (PP l).ιB 0 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha => by
    change (PP l).ιB (-a) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_neg]; exact Submodule.neg_mem _ ha

private theorem sl_alg (K : FinExt l) (c : ↥(K0 K)) : algebraMap ↥(K0 K) (Bcr l) c ∈ slS l := by
  have h : (PP l).ιB (algebraMap ↥(K0 K) (Bcr l) c) ∈ ((PP l).PD K).Fil 0 := by
    rw [← (PP l).PD_ι K, AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 (PP l).R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact (((PP l).PD K).Fil 0).smul_mem _ ((PP l).PD K).one_mem
  have h2 := (PP l).PD_Fil K (botExt l) 0
  change (PP l).ιB _ ∈ (((PP l).PD (botExt l)).Fil 0 : Set (PP l).R.BdR)
  rw [← h2]
  exact h

end UpperTheory.V

open UpperTheory.V in
theorem UpperTheory.filtration_entries_of_frobenius_matrix :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A F : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 → IsUnit A.det → M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ a : ℤ, (∀ i j, (PP l).ιB (M i j) ∈ ((PP l).PD (botExt l)).Fil a) → ∀ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖((l : Om l) ^ f) ^ (-a) * β‖ ≤ 1 := by
  intro l hl K f hf hσ d M M' A F hMM hA hφ hF a hFil β hβ
  obtain ⟨u, hu, hφu⟩ := UpperTheory.exists_crystalline_unit_frobenius_eigen l (-a)
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hc : ∀ k : ℕ, ((PP l).φB)^[k] = ⇑((PP l).φB ^ k) := fun k => (AlgHom.coe_pow _ _).symm
  have hit : ∀ k : ℕ, ((PP l).φB)^[k] (u : Bcr l) =
      algebraMap ℚ_[l] (Bcr l) (((l : ℚ_[l]) ^ (-a)) ^ k) * (u : Bcr l) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, AlgHom.commutes, hφu, pow_succ, map_mul, mul_assoc]
  have huM : ∀ i j, (u : Bcr l) * M i j ∈ slS l := fun i j => by
    have := ((PP l).PD (botExt l)).Fil_mul _ _ _ _ hu (hFil i j)
    rw [neg_add_cancel, ← map_mul] at this
    exact this
  have key : ∀ (k : ℕ) (E : Matrix (Fin d) (Fin d) ↥(K0 K)),
      M.map (((PP l).φB)^[k]) = M * E.map (algebraMap ↥(K0 K) (Bcr l)) →
      ((u : Bcr l) • M).map (((PP l).φB)^[k]) = ((u : Bcr l) • M) *
        (algebraMap ℚ_[l] ↥(K0 K) (((l : ℚ_[l]) ^ (-a)) ^ k) • E).map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro k E hE
    ext i j
    have h1 := congrFun (congrFun hE i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at h1
    have h2 : ((PP l).φB)^[k] ((u : Bcr l) * M i j) =
        ((PP l).φB)^[k] (u : Bcr l) * ((PP l).φB)^[k] (M i j) := by
      rw [hc, map_mul]
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    rw [h2, hit, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    ring
  have h := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ ((u : Bcr l) • M) (((u⁻¹ : (Bcr l)ˣ) : Bcr l) • M') _
    (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul, hMM'])
    (fun k i j => by
      obtain ⟨E, -, hE⟩ := UpperTheory.frobenius_iterate_matrix_form K M A hA hφ k
      have h1 := congrFun (congrFun (key k E hE) i) j
      rw [Matrix.map_apply, Matrix.mul_apply] at h1
      rw [h1]
      exact Subring.sum_mem (slS l) fun r _ => Subring.mul_mem _ (huM _ _) (sl_alg K _))
    (key f F hF)
  apply h
  have hl0 : ((l : Om l) ^ f) ^ (-a) ≠ 0 :=
    zpow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
  have e : (algebraMap ℚ_[l] ↥(K0 K) (((l : ℚ_[l]) ^ (-a)) ^ f) • F).map (algebraMap ↥(K0 K) (Om l)) =
      Units.mk0 _ hl0 • F.map (algebraMap ↥(K0 K) (Om l)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_zpow₀, map_natCast,
      Units.smul_mk0]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm (f : ℤ)]
  rw [e]
  exact (spectrum.smul_mem_smul_iff (r := Units.mk0 _ hl0)).2 hβ
