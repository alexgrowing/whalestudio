import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTSubmatrixMul
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem submatrix_mul_right' {R : Type} [CommRing R] {m n o p : ℕ} (P : Matrix (Fin m) (Fin n) R)
    (Q : Matrix (Fin n) (Fin o) R) (e : Fin p → Fin o) : (P * Q).submatrix id e = P * Q.submatrix id e := by
  ext i j; simp [Matrix.mul_apply]

theorem submatrix_eq_mul_one {R : Type} [CommRing R] {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (e : Fin p → Fin n) : A.submatrix id e = A * (1 : Matrix (Fin n) (Fin n) R).submatrix id e := by
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem flag_mat {R : Type} [CommRing R] {n r : ℕ} (A : Matrix (Fin n) (Fin r) R)
    (A' : Matrix (Fin r) (Fin n) R) (hA : A' * A = 1) (M : Matrix (Fin n) (Fin n) R)
    (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r) (hS : ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k)
    (d : Fin s → ℕ) (hd : ∀ i, d i = (S.filter (· < Fin.castLE hs i)).card)
    (hM : ∀ k ∈ S, ∃ Bk : Matrix (Fin (k.val + 1)) (Fin (k.val + 1)) R,
      M * A.submatrix id (Fin.castLE k.2) = A.submatrix id (Fin.castLE k.2) * Bk) :
    ∃ B : Matrix (Fin s) (Fin s) R, B.BlockTriangular d ∧
      M * A.submatrix id (Fin.castLE hs) = A.submatrix id (Fin.castLE hs) * B := by
  have key : ∀ k ∈ S, ∀ j : Fin r, j ≤ k →
      (∀ l : Fin r, k < l → (A' * M * A) l j = 0) ∧ ∀ a, (M * A) a j = (A * (A' * M * A)) a j := by
    intro k hk j hj
    obtain ⟨Bk, hB⟩ := hM k hk
    have hAk : A' * A.submatrix id (Fin.castLE k.2) = (1 : Matrix (Fin r) (Fin r) R).submatrix id (Fin.castLE k.2) := by
      rw [← submatrix_mul_right', hA]
    have hTk : (A' * M * A).submatrix id (Fin.castLE k.2) =
        (1 : Matrix (Fin r) (Fin r) R).submatrix id (Fin.castLE k.2) * Bk := by
      rw [Matrix.mul_assoc, submatrix_mul_right', submatrix_mul_right', hB, ← Matrix.mul_assoc, hAk]
    have hjk : j.val < k.val + 1 := Nat.lt_succ_of_le hj
    have hj' : Fin.castLE k.2 (⟨j.val, hjk⟩ : Fin (k.val + 1)) = j := Fin.ext rfl
    refine ⟨fun l hl => ?_, fun a => ?_⟩
    · have := congrFun (congrFun hTk l) ⟨j.val, hjk⟩
      rw [Matrix.submatrix_apply, hj'] at this
      change (A' * M * A) l j = _ at this
      rw [this, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l' _ => ?_
      have hne : l ≠ Fin.castLE k.2 l' := by
        intro h; have := congrArg Fin.val h; simp at this; have := l'.2; have := Fin.lt_def.1 hl; omega
      simp [Matrix.one_apply, hne]
    · have e1 : M * A.submatrix id (Fin.castLE k.2) = (A * (A' * M * A)).submatrix id (Fin.castLE k.2) := by
        rw [hB, submatrix_mul_right', hTk, ← Matrix.mul_assoc, ← submatrix_eq_mul_one]
      have := congrFun (congrFun e1 a) ⟨j.val, hjk⟩
      rw [← submatrix_mul_right', Matrix.submatrix_apply, Matrix.submatrix_apply, hj'] at this
      exact this
  have hsmall : ∀ j : Fin r, j.val < s → ∀ l : Fin r, s ≤ l.val → (A' * M * A) l j = 0 := by
    intro j hj l hl
    obtain ⟨k, hk, hjk⟩ := (hS j).1 hj
    have hks : k.val < s := (hS k).2 ⟨k, hk, le_rfl⟩
    exact (key k hk j hjk).1 l (Fin.lt_def.2 (by omega))
  refine ⟨(A' * M * A).submatrix (Fin.castLE hs) (Fin.castLE hs), fun i j hij => ?_, ?_⟩
  · obtain ⟨k, hk, h1, h2⟩ := (depth_lt_iff S s hs d hd i j).1 hij
    exact (key k hk _ h1).1 _ h2
  · ext a j
    have hj : (Fin.castLE hs j).val < s := j.2
    obtain ⟨k, hk, hjk⟩ := (hS _).1 hj
    have e := (key k hk _ hjk).2 a
    rw [← submatrix_mul_right']
    change (M * A) a (Fin.castLE hs j) = _
    rw [e, Matrix.mul_apply, Matrix.mul_apply]
    symm
    rw [show (∑ x : Fin s, A.submatrix id (Fin.castLE hs) a x * (A' * M * A).submatrix (Fin.castLE hs) (Fin.castLE hs) x j) =
        ∑ l ∈ Finset.univ.map (Fin.castLEEmb hs), A a l * (A' * M * A) l (Fin.castLE hs j) from by
      rw [Finset.sum_map]; rfl]
    refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_
    have : s ≤ l.val := by
      by_contra h; push_neg at h
      exact hl (Finset.mem_map.2 ⟨⟨l.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    rw [hsmall _ hj l this, mul_zero]

end GlobalTheory.TieStd

namespace GlobalTheory.TieStd

open GlobalTheory.StdPar in

theorem levi_le_leviFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r),
    (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) →
    GlobalTheory.StdPar.levi σ J X Y S ≤
      GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  have side : ∀ Z W : Matrix (Fin n) (Fin r) E, Formalism.UG.cT (σ : E →+* E) W * J * Z = 1 →
      ∀ g : GAd σ J, (∀ k ∈ S, g ∈ frameStab σ J (initCols Z k) ⊤) →
      ∃ B : Matrix (Fin s) (Fin s) (AF F ⊗[F] E), B.BlockTriangular d ∧
        (matHom _ σ J g).1 * adMat F (Z.submatrix id (Fin.castLE hs)) =
          adMat F (Z.submatrix id (Fin.castLE hs)) * B := by
    intro Z W hWZ g hg
    have hA : adMat F (Formalism.UG.cT (σ : E →+* E) W * J) * adMat F Z = 1 := by
      rw [← Matrix.map_mul, hWZ, Matrix.map_one _ (map_zero _) (map_one _)]
    exact flag_mat (adMat F Z) _ hA _ S s hs hS d hd fun k hk => by
      obtain ⟨B, -, e⟩ := hg k hk
      exact ⟨B.1, e⟩
  have mem : ∀ g ∈ levi σ J X Y S, ∀ k ∈ S,
      g ∈ frameStab σ J (initCols X k) ⊤ ∧ g ∈ frameStab σ J (initCols Y k) ⊤ := fun g hg k hk => by
    simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hg
    exact hg k hk
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := yx h hJ hW
  intro g hg
  have hgi := inv_mem hg
  exact Subgroup.mem_inf.2
    ⟨⟨side X Y hyx g fun k hk => (mem g hg k hk).1, side X Y hyx g⁻¹ fun k hk => (mem _ hgi k hk).1⟩,
      ⟨side Y X hW.xy g fun k hk => (mem g hg k hk).2, side Y X hW.xy g⁻¹ fun k hk => (mem _ hgi k hk).2⟩⟩

end GlobalTheory.TieStd
