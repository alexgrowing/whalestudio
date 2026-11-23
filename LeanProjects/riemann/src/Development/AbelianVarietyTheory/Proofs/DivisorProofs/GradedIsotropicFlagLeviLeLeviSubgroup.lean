import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTSubmatrixMul
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem sum_castLE_of_zero {M : Type*} [AddCommMonoid M] {m s : ℕ} (hm : m ≤ s) (g : Fin s → M)
    (hg : ∀ i : Fin s, m ≤ i.val → g i = 0) : ∑ i : Fin s, g i = ∑ i : Fin m, g (Fin.castLE hm i) := by
  symm
  refine Eq.trans (Finset.sum_map Finset.univ (Fin.castLEEmb hm) g).symm ?_
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hg i (not_lt.1 fun h => hi ?_)
  exact Finset.mem_map.2 ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem mul_submatrix_castLE {R ι' κ : Type*} [CommRing R] {m s : ℕ} (hm : m ≤ s) (C : Matrix ι' (Fin s) R)
    (B : Matrix (Fin s) (Fin s) R) (hB : ∀ i j : Fin s, m ≤ i.val → j.val < m → B i j = 0) (f : κ → ι') :
    (C * B).submatrix f (Fin.castLE hm) =
      C.submatrix f (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  ext a j
  simp only [submatrix_apply, mul_apply]
  exact sum_castLE_of_zero hm _ fun i hi => by rw [hB i _ hi j.2, mul_zero]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem mem_frameStab_of_mem_parFlag {s m : ℕ} (hm : m ≤ s) (C : Matrix (Fin n) (Fin s) E)
    (L : Matrix (Fin s) (Fin n) E) (hL : L * C = 1) (d : Fin s → ℕ)
    (hd : ∀ i j : Fin s, m ≤ i.val → j.val < m → d j < d i) {g : GAd σ J} (hg : g ∈ GlobalTheory.UAut.parFlag σ J C d) :
    g ∈ GlobalTheory.StdPar.frameStab σ J (C.submatrix id (Fin.castLE hm)) ⊤ := by
  obtain ⟨⟨B, hB, e⟩, B', hB', e'⟩ := hg
  have hL' : adMat F L * adMat F C = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMM : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBB : B * B' = 1 := by
    calc B * B' = adMat F L * (adMat F C * B) * B' := by rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
      _ = adMat F L * ((matHom _ σ J g).1 * ((matHom _ σ J g⁻¹).1 * adMat F C)) := by
          simp only [← e, e', Matrix.mul_assoc]
      _ = 1 := by rw [← Matrix.mul_assoc (matHom _ σ J g).1, hMM, Matrix.one_mul, hL']
  have hz : ∀ {A : Matrix (Fin s) (Fin s) (AF F ⊗[F] E)}, A.BlockTriangular d →
      ∀ i j : Fin s, m ≤ i.val → j.val < m → A i j = 0 := fun hA i j hi hj => hA (hd i j hi hj)
  have hU : B.submatrix (Fin.castLE hm) (Fin.castLE hm) * B'.submatrix (Fin.castLE hm) (Fin.castLE hm) = 1 := by
    rw [← mul_submatrix_castLE hm B B' (hz hB') (Fin.castLE hm), hBB, Matrix.submatrix_one _ (Fin.castLE_injective hm)]
  refine ⟨⟨_, _, hU, mul_eq_one_comm.1 hU⟩, Subgroup.mem_top _, ?_⟩
  show (matHom _ σ J g).1 * (adMat F C).submatrix id (Fin.castLE hm) =
    (adMat F C).submatrix id (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm)
  rw [← mul_submatrix_castLE hm _ B (hz hB) id, ← e]
  ext a j
  simp [Matrix.mul_apply]

end GlobalTheory.TieStd

namespace GlobalTheory.TieStd

theorem leviFlag_le_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
    IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) →
    ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ≤
      GlobalTheory.StdPar.levi σ J X Y S := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW S s hs hS d hd g hg
  obtain ⟨hgX, hgY⟩ := Subgroup.mem_inf.1 hg
  have hyx := GlobalTheory.StdPar.yx hσ hJ hW
  have hLX : Formalism.UG.cT (σ : E →+* E) (Y.submatrix id (Fin.castLE hs)) * J * X.submatrix id (Fin.castLE hs) = 1 := by
    rw [cT_submatrix_mul, hyx, Matrix.submatrix_one _ (Fin.castLE_injective hs)]
  have hLY : Formalism.UG.cT (σ : E →+* E) (X.submatrix id (Fin.castLE hs)) * J * Y.submatrix id (Fin.castLE hs) = 1 := by
    rw [cT_submatrix_mul, hW.xy, Matrix.submatrix_one _ (Fin.castLE_injective hs)]
  rw [GlobalTheory.StdPar.levi, Subgroup.mem_iInf]
  intro k
  rw [Subgroup.mem_iInf]
  intro hk
  have hm : k.val + 1 ≤ s := (hS k).2 ⟨k, hk, le_rfl⟩
  have hdk : ∀ i j : Fin s, k.val + 1 ≤ i.val → j.val < k.val + 1 → d j < d i := fun i j hi hj =>
    (depth_lt_iff S s hs d hd i j).2 ⟨k, hk, Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 hj), Fin.lt_iff_val_lt_val.2 hi⟩
  exact Subgroup.mem_inf.2 ⟨mem_frameStab_of_mem_parFlag σ J hm _ _ hLX d hdk hgX,
    mem_frameStab_of_mem_parFlag σ J hm _ _ hLY d hdk hgY⟩

end GlobalTheory.TieStd
