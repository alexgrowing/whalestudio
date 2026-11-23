import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevB
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HwUpper

theorem telescope (d : ℕ → ℂ) (f : ℕ → ℕ) (hf : ∀ s, f (s + 1) ≤ f s) (m : ℕ) :
    (∏ s ∈ Finset.range m, (∏ k ∈ Finset.range (s + 1), d k) ^ (f s - f (s + 1))) *
      (∏ k ∈ Finset.range m, d k) ^ f m = ∏ k ∈ Finset.range m, d k ^ f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ (fun k => d k ^ f k), ← ih, mul_assoc, mul_assoc]
    congr 1
    rw [← pow_add, Nat.sub_add_cancel (hf m), Finset.prod_range_succ, mul_pow]

theorem hwScal_transpose {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (B : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.BasicNotions.Examples₂.NZ.hwScal ℂ (le_refl n) ν B.transpose = ∏ i, B i i ^ ν i := by
  classical
  set d : ℕ → ℂ := fun k => if h : k < n then B ⟨k, h⟩ ⟨k, h⟩ else 1 with hd
  set f : ℕ → ℕ := fun k => if h : k < n then ν ⟨k, h⟩ else 0 with hfd
  have hf : ∀ s, f (s + 1) ≤ f s := by
    intro s
    by_cases h : s + 1 < n
    · simp only [hfd, dif_pos h, dif_pos (show s < n by omega)]
      exact hν (show (⟨s, by omega⟩ : Fin n) ≤ ⟨s + 1, h⟩ from Fin.mk_le_mk.mpr (by omega))
    · simp only [hfd, dif_neg h]
      exact Nat.zero_le _
  have hinner : ∀ s : Fin n, (∏ a : Fin (s.val + 1),
      B.transpose (Fin.castLE (by omega) a) (Fin.castLE (by omega) a)) = ∏ k ∈ Finset.range (s.val + 1), d k := by
    intro s
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun a _ => ?_
    have ha : a.val < n := by omega
    simp only [hd, dif_pos ha, Matrix.transpose_apply]
    rfl
  have hexp : ∀ s : Fin n, ν s - Formalism.GradedWeylDivisibility.nuNext ν s = f s.val - f (s.val + 1) := by
    intro s
    simp only [hfd, dif_pos s.2, Formalism.GradedWeylDivisibility.nuNext]
  unfold Formalism.BasicNotions.Examples₂.NZ.hwScal
  simp_rw [hinner, hexp]
  rw [Fin.prod_univ_eq_prod_range (fun s => (∏ k ∈ Finset.range (s + 1), d k) ^ (f s - f (s + 1))) n]
  have hfn : f n = 0 := by simp [hfd]
  have ht := telescope d f hf n
  rw [hfn, pow_zero, mul_one] at ht
  rw [ht, ← Fin.prod_univ_eq_prod_range (fun k => d k ^ f k) n]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [hd, hfd, dif_pos i.2]

theorem exists_hw_upper : ∀ (n : ℕ) (lam : DomWeight n), ∃ v : nablaSq ℂ n lam, v ≠ 0 ∧
    ∀ B : GL (Fin n) ℂ, (B : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id →
      GlobalTheory.Branching.sqRep ℂ n lam B v = (∏ i, ((B : Matrix (Fin n) (Fin n) ℂ) i i) ^ (lam.w i)) • v := by
  intro n lam
  have ha : Antitone lam.natW := fun i j hij => by
    have := lam.anti hij
    simp only [DomWeight.natW]
    omega
  refine ⟨⟨extremal ℂ n lam, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ ha⟩, fun h =>
    Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl lam.natW (congrArg Subtype.val h), fun B hB => ?_⟩
  apply Subtype.ext
  set M : Matrix (Fin n) (Fin n) ℂ := (B : Matrix (Fin n) (Fin n) ℂ) with hM
  have hl : ∀ i j : Fin n, i < j → M.transpose i j = 0 := fun i j hij => by
    rw [Matrix.transpose_apply]; exact hB hij
  have hdet : M.det = ∏ i, M i i := Matrix.det_of_upperTriangular hB
  have hne : ∀ i, M i i ≠ 0 := by
    have h0 : M.det ≠ 0 := by
      have := (Matrix.GeneralLinearGroup.det B).ne_zero
      simpa [hM] using this
    rw [hdet, Finset.prod_ne_zero_iff] at h0
    exact fun i => h0 i (Finset.mem_univ i)
  have hw_eq : ∀ i, (lam.natW i : ℤ) + lam.detShift = lam.w i := by
    intro i
    have hle : lam.detShift ≤ lam.w i := by
      unfold DomWeight.detShift
      have hn : 0 < n := Fin.pos i
      rw [dif_pos hn]
      exact lam.anti (Fin.mk_le_mk.mpr (by omega) : i ≤ ⟨n - 1, by omega⟩)
    simp only [DomWeight.natW]
    omega
  rw [GlobalTheory.Branching.sqRep_coe, Submodule.coe_smul]
  show detPow ℂ n B lam.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) M.transpose (extremal ℂ n lam) = _
  unfold extremal
  rw [Formalism.BasicNotions.Examples₂.NZ.rowAct_hw ℂ le_rfl lam.natW M.transpose hl, hwScal_transpose lam.natW ha M, smul_smul]
  congr 1
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← hM, hdet, ← Finset.prod_zpow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_add₀ (hne i), add_comm, hw_eq]

end GlobalTheory.HwUpper
