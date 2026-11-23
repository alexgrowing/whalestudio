import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep
open GlobalTheory.SplitPts (conjE)

namespace UpperTheory.Gal.Spc

section LinAlg

variable {K : Type*} [Field K] {m : ℕ}

private theorem sep_of_mul_closed [IsAlgClosed K] {M N : Matrix (Fin m) (Fin m) K} {a : K} (ha : a ≠ 0)
    (h : N * M = a • (1 : Matrix (Fin m) (Fin m) K)) (hM : M.charpoly.Separable) : N.charpoly.Separable := by
  classical
  have hdet : M.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    by_cases hm : m = 0
    · subst hm
      simp [Matrix.det_isEmpty] at h0
    · exact pow_ne_zero _ ha this.symm
  have hroot : ∀ x ∈ M.charpoly.roots, x ≠ 0 ∧ a / x ∈ N.charpoly.roots := by
    intro x hx
    have hx0 : M.charpoly.eval x = 0 := (Polynomial.mem_roots'.1 hx).2
    rw [Matrix.eval_charpoly] at hx0
    have hne : x ≠ 0 := by
      rintro rfl
      apply hdet
      simpa [Matrix.det_neg] using hx0
    refine ⟨hne, Polynomial.mem_roots'.2 ⟨(Matrix.charpoly_monic N).ne_zero, ?_⟩⟩
    show N.charpoly.eval (a / x) = 0
    rw [Matrix.eval_charpoly]
    have e : Matrix.scalar (Fin m) (a / x) - N = (-x⁻¹) • (N * (Matrix.scalar (Fin m) x - M)) := by
      rw [Matrix.mul_sub, h, Matrix.scalar_apply, Matrix.scalar_apply]
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply] <;> field_simp <;> ring
    rw [e, Matrix.det_smul, Matrix.det_mul, hx0, mul_zero, mul_zero]
  have hnd : M.charpoly.roots.Nodup := Polynomial.nodup_roots hM
  have hcM : M.charpoly.roots.card = m := by
    have := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits M.charpoly)
    rw [this, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcN : N.charpoly.roots.card = m := by
    have := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits N.charpoly)
    rw [this, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hinj : Set.InjOn (fun x : K => a / x) (M.charpoly.roots.toFinset : Set K) := by
    intro x hx y hy hxy
    have hx0 := (hroot x (by simpa using hx)).1
    have hy0 := (hroot y (by simpa using hy)).1
    have hxy' : a * x⁻¹ = a * y⁻¹ := by simpa only [div_eq_mul_inv] using hxy
    exact inv_injective (mul_left_cancel₀ ha hxy')
  have hsub : M.charpoly.roots.toFinset.image (fun x : K => a / x) ⊆ N.charpoly.roots.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Multiset.mem_toFinset.2 (hroot x (Multiset.mem_toFinset.1 hx)).2
  have hle : m ≤ N.charpoly.roots.toFinset.card := by
    have h1 := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj, Multiset.toFinset_card_of_nodup hnd, hcM] at h1
  have hndN : N.charpoly.roots.Nodup := by
    rw [← Multiset.dedup_card_eq_card_iff_nodup]
    refine le_antisymm (Multiset.card_le_card (Multiset.dedup_le _)) ?_
    rw [hcN]
    exact hle
  exact (Polynomial.nodup_roots_iff_of_splits (Matrix.charpoly_monic N).ne_zero (IsAlgClosed.splits _)).1 hndN

private theorem sep_of_mul {M N : Matrix (Fin m) (Fin m) K} {a : K} (ha : a ≠ 0)
    (h : N * M = a • (1 : Matrix (Fin m) (Fin m) K)) (hM : M.charpoly.Separable) : N.charpoly.Separable := by
  have h' : N.map (algebraMap K (AlgebraicClosure K)) * M.map (algebraMap K (AlgebraicClosure K)) =
      algebraMap K (AlgebraicClosure K) a • (1 : Matrix (Fin m) (Fin m) (AlgebraicClosure K)) := by
    rw [← Matrix.map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have h2 := sep_of_mul_closed (K := AlgebraicClosure K) (a := algebraMap K (AlgebraicClosure K) a)
    (by simpa using ha) h' (by rw [Matrix.charpoly_map]; exact hM.map)
  rw [Matrix.charpoly_map] at h2
  exact (Polynomial.separable_map _).1 h2

end LinAlg

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.sepConj :
    UpperTheory.Gal.Spc.SepConj := by
  intro E _ _ _ n g w hw
  have h0 : (g.1.1.val.map (conjFin (conjE E)))ᵀ * g.1.1.val =
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ) • (1 : Matrix (Fin n) (Fin n) _) := g.2
  have h1 := congrArg (RingHom.mapMatrix (pLoc E w)) h0
  rw [map_mul] at h1
  have ha : pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ)) ≠ 0 :=
    ((g.1.2.isUnit.map (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E)).map (pLoc E w)).ne_zero
  have h2 : (((UpperTheory.Gal.CertificateRingHomMap.comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (conjE E) w))ᵀ) * (UpperTheory.Gal.CertificateRingHomMap.comp w g).val =
      pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ)) • (1 : Matrix (Fin n) (Fin n) _) := by
    refine Eq.trans ?_ (h1.trans ?_)
    · congr 1
    · ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have h3 := UpperTheory.Gal.Spc.sep_of_mul ha h2 hw
  rw [Matrix.charpoly_transpose, Matrix.charpoly_map] at h3
  exact (Polynomial.separable_map _).1 h3
