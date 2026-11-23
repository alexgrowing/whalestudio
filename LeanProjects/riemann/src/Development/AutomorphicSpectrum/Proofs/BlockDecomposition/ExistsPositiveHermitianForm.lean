import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.TraceHerm

def toep {K : Type} [CommRing K] {n : ℕ} (M M' : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun j k => Matrix.trace (M ^ (k : ℕ) * M' ^ (j : ℕ))

theorem toep_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ} (f : K →+* L) (M M' : Matrix (Fin n) (Fin n) K) :
    (toep M M').map f = toep (M.map f) (M'.map f) := by
  ext j k
  simp only [toep, Matrix.map_apply, Matrix.of_apply]
  rw [← Matrix.map_pow, ← Matrix.map_pow, ← Matrix.map_mul]
  exact AddMonoidHom.map_trace f.toAddMonoidHom _

theorem pow_mul_eq {n : ℕ} {A T : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ} (h : A * T = T * diagonal z) (k : ℕ) :
    A ^ k * T = T * diagonal (fun i => z i ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h, Matrix.mul_assoc, diagonal_mul_diagonal]
    congr 2
    ext i
    rw [pow_succ']

theorem core {n : ℕ} (A A' T : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) (v : Fin n → ℂ) (hAA : A' * A = 1)
    (hT : A * T = T * diagonal z) (hv : v = T *ᵥ 1) (hz : ∀ i, ‖z i‖ = 1)
    (hB : (GlobalTheory.ClassParam.krylov A v).det ≠ 0) :
    (((GlobalTheory.ClassParam.krylov A v)⁻¹)ᴴ * toep A A' * (GlobalTheory.ClassParam.krylov A v)⁻¹).PosDef ∧
      Aᴴ * (((GlobalTheory.ClassParam.krylov A v)⁻¹)ᴴ * toep A A' * (GlobalTheory.ClassParam.krylov A v)⁻¹) * A =
        ((GlobalTheory.ClassParam.krylov A v)⁻¹)ᴴ * toep A A' * (GlobalTheory.ClassParam.krylov A v)⁻¹ := by
  set B := GlobalTheory.ClassParam.krylov A v with hBdef
  let V : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => z i ^ (k : ℕ)
  let zc : Fin n → ℂ := fun i => starRingEnd ℂ (z i)
  have hzz : ∀ i, z i * zc i = 1 := by
    intro i
    simp only [zc]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz i]
    simp
  have hDD : diagonal z * diagonal zc = 1 := by
    rw [diagonal_mul_diagonal]
    simp [hzz]
  have hBTV : B = T * V := by
    ext i k
    have h1 := pow_mul_eq hT (k : ℕ)
    have h2 : ((A ^ (k : ℕ)) *ᵥ v) = (T * diagonal (fun i => z i ^ (k : ℕ))) *ᵥ 1 := by
      rw [hv, Matrix.mulVec_mulVec, h1]
    simp only [hBdef, GlobalTheory.ClassParam.krylov, Matrix.of_apply]
    rw [h2]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, V, Matrix.diagonal_apply]
  have hdet : T.det * V.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hBTV]; exact hB
  have hTd : IsUnit T.det := (isUnit_iff_ne_zero).2 (left_ne_zero_of_mul hdet)
  have hVd : IsUnit V.det := (isUnit_iff_ne_zero).2 (right_ne_zero_of_mul hdet)
  have hA' : A' * T = T * diagonal zc := by
    calc A' * T = A' * (T * (diagonal z * diagonal zc)) := by rw [hDD, Matrix.mul_one]
      _ = A' * A * T * diagonal zc := by
          rw [Matrix.mul_assoc A' A T, hT]; simp only [Matrix.mul_assoc]
      _ = T * diagonal zc := by rw [hAA, Matrix.one_mul]
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hTd
  have hTT' : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ hTd
  have hG : toep A A' = Vᴴ * V := by
    ext j k
    have h1 : A ^ (k : ℕ) * A' ^ (j : ℕ) * T =
        T * diagonal (fun i => z i ^ (k : ℕ) * zc i ^ (j : ℕ)) := by
      rw [Matrix.mul_assoc, pow_mul_eq hA', ← Matrix.mul_assoc, pow_mul_eq hT, Matrix.mul_assoc,
        diagonal_mul_diagonal]
    have h2 : A ^ (k : ℕ) * A' ^ (j : ℕ) =
        T * (diagonal (fun i => z i ^ (k : ℕ) * zc i ^ (j : ℕ)) * T⁻¹) := by
      rw [← Matrix.mul_assoc, ← h1, Matrix.mul_assoc, hTT, Matrix.mul_one]
    simp only [toep, Matrix.of_apply]
    rw [h2, Matrix.trace_mul_comm, Matrix.mul_assoc, hTT', Matrix.mul_one, Matrix.trace_diagonal]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply, zc]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have hQ : V * B⁻¹ = T⁻¹ := by
    rw [hBTV, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hVd, Matrix.one_mul]
  have hP : (B⁻¹)ᴴ * toep A A' * B⁻¹ = (T⁻¹)ᴴ * T⁻¹ := by
    rw [hG, ← hQ, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hP]
  have hQA : T⁻¹ * A = diagonal z * T⁻¹ := by
    calc T⁻¹ * A = T⁻¹ * A * (T * T⁻¹) := by rw [hTT, Matrix.mul_one]
      _ = T⁻¹ * (A * T) * T⁻¹ := by simp only [Matrix.mul_assoc]
      _ = diagonal z * T⁻¹ := by rw [hT, ← Matrix.mul_assoc, hTT', Matrix.one_mul]
  refine ⟨Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_), ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).2 (by rw [Matrix.det_nonsing_inv]; simpa using hTd)
  · have hDc : (diagonal z)ᴴ * diagonal z = 1 := by
      rw [Matrix.diagonal_conjTranspose, diagonal_mul_diagonal]
      have h1 : (fun i => (star z) i * z i) = fun _ => (1 : ℂ) :=
        funext fun i => by rw [Pi.star_apply, mul_comm]; exact hzz i
      rw [h1]
      exact diagonal_one
    calc Aᴴ * ((T⁻¹)ᴴ * T⁻¹) * A = (T⁻¹ * A)ᴴ * (T⁻¹ * A) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (T⁻¹)ᴴ * ((diagonal z)ᴴ * diagonal z) * T⁻¹ := by
          rw [hQA, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (T⁻¹)ᴴ * T⁻¹ := by rw [hDc, Matrix.mul_one]

theorem exists_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hs : A.charpoly.Separable) (v : Fin n → ℂ) :
    ∃ (T : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ),
      A * T = T * diagonal z ∧ v = T *ᵥ 1 ∧ ∀ i, z i ∈ A.charpoly.roots := by
  have hnd : A.charpoly.roots.Nodup := nodup_roots hs
  have hcard := splits_iff_card_roots.1 (IsAlgClosed.splits A.charpoly)
  have hdeg : A.charpoly.natDegree = n := by
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  set s := A.charpoly.roots.toFinset with hs_def
  have hsc : Fintype.card s = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd, hcard, hdeg]
  let e := Fintype.equivFinOfCardEq hsc
  let z : Fin n → ℂ := fun a => ((e.symm a : s) : ℂ)
  have hprod : A.charpoly = ∏ a, (X - C (z a)) := by
    rw [Equiv.prod_comp e.symm (fun r : s => X - C (r : ℂ)), Finset.prod_coe_sort s (fun r => X - C r),
      Finset.prod_eq_multiset_prod, hs_def, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd,
      prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _) hcard]
  have hch : (diagonal z).charpoly = A.charpoly := by rw [charpoly_diagonal, hprod]
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (M := diagonal z) (N := A)
    (by rw [GlobalTheory.Orb.IsRegSS, hch]; exact hs) hch.symm
  let w : Fin n → ℂ := ((x⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ v
  refine ⟨(x : Matrix (Fin n) (Fin n) ℂ) * diagonal w, z, ?_, ?_, fun i => ?_⟩
  · rw [← Matrix.mul_assoc, hx, Matrix.mul_assoc, Matrix.mul_assoc, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 2
    ext i
    exact mul_comm _ _
  · have h1 : diagonal w *ᵥ (1 : Fin n → ℂ) = w := by
      ext i
      simp [Matrix.mulVec_diagonal]
    rw [← Matrix.mulVec_mulVec, h1]
    simp only [w]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
    simp
  · have : (e.symm i : ℂ) ∈ s := (e.symm i).2
    exact Multiset.mem_toFinset.1 this

theorem exists_posDef_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (N : GL (Fin n) E),
  N.val.charpoly.Separable → (∀ τ : E →+* ℂ, ∀ z ∈ (N.val.charpoly.map τ).roots, ‖z‖ = 1) →
  ∃ H : Matrix (Fin n) (Fin n) E, IsUnit H.det ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
    N ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ ∀ τ : E →+* ℂ, (H.map τ).PosDef := by
  intro E _ _ _ n N hs hr
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hc
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field N.val hs
  set B := GlobalTheory.ClassParam.krylov N.val v with hB
  set N' : Matrix (Fin n) (Fin n) E := ((N⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hN'
  have hN'N : N' * N.val = 1 := by
    rw [hN', ← Units.val_mul, inv_mul_cancel]; rfl
  have hcT : ∀ (τ : E →+* ℂ) (M : Matrix (Fin n) (Fin n) E), (cT c M).map τ = (M.map τ)ᴴ := by
    intro τ M
    ext i j
    simp only [cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    exact IsCMField.complexEmbedding_complexConj E τ (M j i)
  have hinv : ∀ τ : E →+* ℂ, (B⁻¹).map τ = (B.map τ)⁻¹ := by
    intro τ
    have h1 : (B⁻¹).map τ * B.map τ = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ ((isUnit_iff_ne_zero).2 hv)]
      simp
    exact (Matrix.inv_eq_left_inv h1).symm
  let H : Matrix (Fin n) (Fin n) E := cT c B⁻¹ * toep N.val N' * B⁻¹
  have hkey : ∀ τ : E →+* ℂ, (H.map τ).PosDef ∧ (N.val.map τ)ᴴ * H.map τ * N.val.map τ = H.map τ := by
    intro τ
    have hHτ : H.map τ = ((GlobalTheory.ClassParam.krylov (N.val.map τ) (τ ∘ v))⁻¹)ᴴ *
        toep (N.val.map τ) (N'.map τ) * (GlobalTheory.ClassParam.krylov (N.val.map τ) (τ ∘ v))⁻¹ := by
      simp only [H]
      rw [Matrix.map_mul, Matrix.map_mul, hcT, toep_map, hinv, hB, GlobalTheory.ClassParam.krylov_map]
    have hsτ : (N.val.map τ).charpoly.Separable := by
      rw [Matrix.charpoly_map]; exact hs.map
    obtain ⟨T, z, h1, h2, h3⟩ := exists_diag (N.val.map τ) hsτ (τ ∘ v)
    have hz : ∀ i, ‖z i‖ = 1 := fun i => hr τ (z i) (by rw [← Matrix.charpoly_map]; exact h3 i)
    have hdet : (GlobalTheory.ClassParam.krylov (N.val.map τ) (τ ∘ v)).det ≠ 0 := by
      rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero τ).2 hv
    rw [hHτ]
    exact core _ _ T z _ (by rw [← Matrix.map_mul, hN'N]; simp) h1 h2 hz hdet
  have hhermτ : ∀ τ : E →+* ℂ, (cT c H).map τ = H.map τ := fun τ => by
    rw [hcT]; exact (hkey τ).1.isHermitian.eq
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) E => M.map τ₀) :=
    Matrix.map_injective τ₀.injective
  refine ⟨H, ?_, hinj (hhermτ τ₀), ?_, fun τ => (hkey τ).1⟩
  · have h := (hkey τ₀).1.det_pos.ne'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
    exact (isUnit_iff_ne_zero).2 (fun h0 => h (by rw [h0, map_zero]))
  · change cT c N.val * H * N.val = H
    apply hinj
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, hcT]
    exact (hkey τ₀).2

end GlobalTheory.CompanionTheory.TraceHerm
