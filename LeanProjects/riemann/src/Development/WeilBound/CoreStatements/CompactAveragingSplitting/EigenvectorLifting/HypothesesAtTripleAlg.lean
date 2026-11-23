import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef

noncomputable section

namespace PositivityTheory.ThK.PT

open scoped Matrix
open GlobalTheory.WeilM

section Forms

variable {k : Type} [Field k] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}

theorem map_mul_c {a b d : Type} [Fintype b] (A : Matrix a b K) (B : Matrix b d K) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul (f := c.toRingHom)

theorem map_one_c {a : Type} [DecidableEq a] : (1 : Matrix a a K).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)

theorem exists_left_inv (hK : IsField K) {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (C : Matrix a b K)
    (h : ∀ t, C *ᵥ t = 0 → t = 0) : ∃ L : Matrix b a K, L * C = 1 := by
  letI := hK.toField
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot'.2 fun t ht => h t ht)
  refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg, Matrix.toLin'_one]

theorem isLagr_of_free [Invertible (2 : k)] (hK : IsField K) (hc : ∀ x, c (c x) = x) {N m : ℕ} (hN : N = 2 * m)
    {J : Matrix (Fin N) (Fin N) K} (hJ : IsSkewM c J) {Y : Matrix (Fin N) (Fin m) K} (hY : Yᵀ * J * Y.map c = 0)
    (hf : ∀ t, Y *ᵥ t = 0 → t = 0) : IsLagr c J Y := by
  obtain ⟨L, hL⟩ := exists_left_inv hK Y hf
  have cc : ∀ {a b : Type} (A : Matrix a b K), (A.map c).map c = A := fun A => Matrix.ext fun i j => hc _
  have hJ' : (J.map c)ᵀ = -J := Matrix.ext fun i j => hJ.1 i j
  have sk : ∀ {a b : Type} (A : Matrix (Fin N) a K) (B : Matrix (Fin N) b K),
      Bᵀ * J * A.map c = -((Aᵀ * J * B.map c).map c)ᵀ := fun A B => by
    rw [map_mul_c, map_mul_c, cc, Matrix.transpose_mul, Matrix.transpose_mul, hJ', Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin N) (Fin m) K, Yᵀ * J * Z.map c = 1 := ⟨(J⁻¹ * Lᵀ).map c, by
    rw [cc, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ.2, ← Matrix.transpose_mul, hL, Matrix.transpose_one]⟩
  have hZ' : Zᵀ * J * Y.map c = -1 := by rw [sk, hZ, map_one_c, Matrix.transpose_one]
  set S := Zᵀ * J * Z.map c with hS
  have hS' : (S.map c)ᵀ = -S := by rw [hS, neg_eq_iff_eq_neg.2 (sk Z Z)]
  let t : Matrix (Fin m) (Fin m) K := -(⅟(2 : k) • Sᵀ)
  have ht : t.map c = ⅟(2 : k) • S := by
    ext i j
    have : c (S j i) = -S i j := congrFun (congrFun hS' i) j
    simp [t, this]
  have a1 : ∀ A B : Matrix (Fin N) (Fin m) K, (A + B).map c = A.map c + B.map c := fun A B =>
    Matrix.map_add _ (map_add c) _ _
  have e1 : Yᵀ * J * (Z + Y * t).map c = 1 := by
    rw [a1, map_mul_c, Matrix.mul_add, hZ, ← Matrix.mul_assoc, hY, Matrix.zero_mul, add_zero]
  have e2 : (Z + Y * t)ᵀ * J * Y.map c = -1 := by rw [sk, e1, map_one_c, Matrix.transpose_one]
  have e3 : (Z + Y * t)ᵀ * J * (Z + Y * t).map c = 0 := by
    rw [a1, map_mul_c, Matrix.mul_add, ← Matrix.mul_assoc, e2, ht, Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul,
      Matrix.transpose_mul, Matrix.mul_assoc tᵀ, Matrix.mul_assoc tᵀ, hZ, ← hS]
    simp only [t, Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_one, Matrix.neg_mul,
      Matrix.one_mul]
    rw [add_assoc, ← neg_add, ← add_smul, invOf_two_add_invOf_two, one_smul, add_neg_cancel]
  set X := Z + Y * t
  have g : (Matrix.fromCols Y X)ᵀ * J * (Matrix.fromCols Y X).map c = Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.transpose_fromCols, Matrix.fromCols_map, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, hY, e1, e2, e3]
  have g' : ((Matrix.fromBlocks 0 (-1) 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (((Matrix.fromCols Y X)ᵀ).map c * J.map c)) * Matrix.fromCols Y X = 1 := by
    have := congrArg (fun M => M.map c) g
    simp only [map_mul_c, cc] at this
    rw [Matrix.mul_assoc, this, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero c), map_one_c, Matrix.map_neg _ (map_neg c),
      map_one_c, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp
  exact ⟨hY, X, _, e3, (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp; omega))).1 g', g'⟩

def anti (K : Type) [CommRing K] (n : ℕ) : Matrix (Fin n) (Fin n) K := fun i j => if i.val + j.val + 1 = n then 1 else 0

variable (c) in

def HasAnti {n : ℕ} (J : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ P Q : Matrix (Fin n) (Fin n) K, P * Q = 1 ∧ Q * P = 1 ∧ Pᵀ * J * P.map c = anti K n

theorem exists_anti_equiv (a' r : ℕ) : ∃ e : Fin a' ⊕ (Fin r ⊕ Fin r) ≃ Fin (a' + 2 * r),
    (anti K (a' + 2 * r)).submatrix e e = Matrix.fromBlocks (anti K a') 0 0 (Matrix.fromBlocks 0 1 1 0) := by
  let f : Fin a' ⊕ (Fin r ⊕ Fin r) → Fin (a' + 2 * r) :=
    Sum.elim (fun i => ⟨r + i, by omega⟩) (Sum.elim (fun j => ⟨j, by omega⟩) fun j => ⟨a' + 2 * r - 1 - j, by omega⟩)
  have hf : Function.Injective f := by
    rintro (i | i | i) (j | j | j) h <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h <;>
      first | (simp only [Sum.inl.injEq, Sum.inr.injEq]; exact Fin.ext (by omega)) | (exfalso; omega)
  refine ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp; omega⟩), ?_⟩
  ext (i | i | i) (j | j | j) <;>
    simp only [f, anti, Matrix.submatrix_apply, Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply,
      Fin.ext_iff] <;>
    first | exact if_congr (by omega) rfl rfl | exact if_neg (by omega)

theorem isAbove_of_hasAnti {a a' : ℕ} (h : a' ≤ a) (he : Even (a + a')) {J : Matrix (Fin a) (Fin a) K}
    {J' : Matrix (Fin a') (Fin a') K} (h1 : HasAnti c J) (h2 : HasAnti c J') : IsAbove c J J' := by
  obtain ⟨r, rfl⟩ : ∃ r, a = a' + 2 * r := by
    obtain ⟨s, hs⟩ := he
    exact ⟨s - a', by omega⟩
  obtain ⟨P, Q, p1, p2, p3⟩ := h1
  obtain ⟨P', Q', q1, q2, q3⟩ := h2
  obtain ⟨e, he⟩ := exists_anti_equiv (K := K) a' r
  have b1 : (Matrix.fromBlocks Q' 0 0 1 : Matrix (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fin a' ⊕ (Fin r ⊕ Fin r)) K) *
      Matrix.fromBlocks P' 0 0 1 = 1 := by simp [Matrix.fromBlocks_multiply, q2]
  have b2 : (Matrix.fromBlocks P' 0 0 1 : Matrix (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fin a' ⊕ (Fin r ⊕ Fin r)) K) *
      Matrix.fromBlocks Q' 0 0 1 = 1 := by simp [Matrix.fromBlocks_multiply, q1]
  have c1 : P.submatrix id e * Q.submatrix e id = 1 := by rw [Matrix.submatrix_mul_equiv, p1]; rfl
  have c2 : Q.submatrix e id * P.submatrix id e = 1 := by
    rw [show Q.submatrix e id * P.submatrix id e = (Q * P).submatrix e e from rfl, p2, Matrix.submatrix_one_equiv]
  have c3 : (P.submatrix id e)ᵀ * J * (P.submatrix id e).map c = (anti K _).submatrix e e := by rw [← p3]; rfl
  have d : Q'ᵀ * anti K a' * Q'.map c = J' := by
    rw [← q3, Matrix.mul_assoc, Matrix.mul_assoc, ← map_mul_c, q1, map_one_c, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.transpose_mul, q1, Matrix.transpose_one, Matrix.one_mul]
  refine ⟨r, P.submatrix id e * (Matrix.fromBlocks Q' 0 0 1 : Matrix (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fin a' ⊕ (Fin r ⊕ Fin r)) K),
    (Matrix.fromBlocks P' 0 0 1 : Matrix (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fin a' ⊕ (Fin r ⊕ Fin r)) K) * Q.submatrix e id, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.fromBlocks Q' 0 0 1), b1, Matrix.one_mul, c1]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Q.submatrix e id), c2, Matrix.one_mul, b2]
  · rw [map_mul_c, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc J,
      ← Matrix.mul_assoc (P.submatrix id e)ᵀ, ← Matrix.mul_assoc (P.submatrix id e)ᵀ, c3, he, Matrix.fromBlocks_map,
      Matrix.fromBlocks_transpose, Matrix.map_zero _ (map_zero c), Matrix.map_zero _ (map_zero c), map_one_c,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [← Matrix.mul_assoc, d]

end Forms

theorem exists_to_quot {S T : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T] (s : S →ₗ[ℂ] T)
    (A B : Submodule ℂ S) (h : ∀ φ ∈ B, s φ = 0 → φ ∈ A) : ∃ j : T →ₗ[ℂ] S ⧸ A, ∀ φ ∈ B, j (s φ) = A.mkQ φ := by
  have hk : LinearMap.ker (s ∘ₗ B.subtype) ≤ LinearMap.ker (A.mkQ ∘ₗ B.subtype) := fun φ hφ =>
    (Submodule.Quotient.mk_eq_zero A).2 (h φ φ.2 hφ)
  obtain ⟨j, hj⟩ := LinearMap.exists_extend
    (((LinearMap.ker (s ∘ₗ B.subtype)).liftQ _ hk) ∘ₗ (s ∘ₗ B.subtype).quotKerEquivRange.symm.toLinearMap)
  refine ⟨j, fun φ hφ => ?_⟩
  have := LinearMap.congr_fun hj ((s ∘ₗ B.subtype).quotKerEquivRange (Submodule.Quotient.mk ⟨φ, hφ⟩))
  simpa using this

end PositivityTheory.ThK.PT
