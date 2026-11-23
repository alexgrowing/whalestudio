import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PStab

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped Kronecker ComplexOrder

namespace PositivityTheory.KB.BlockInvariants

namespace BlockSumPreservesCone

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
theorem mat_one (N : ℕ) (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

theorem mat_padL (n M : ℕ) (h : HS L n) (w : InfinitePlace L) :
    mat (padL n M h) w = padM (mat h w) := rfl

omit [NumberField L] in
theorem mat_eL (n M : ℕ) (w : InfinitePlace L) :
    mat (eL (L := L) n M) w = padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ) := rfl

def kr {R : Type} [CommRing R] (d : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (d * n)) (Fin (d * n)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) R) ⊗ₖ A)

theorem mat_blkL (d n : ℕ) (h : HS L n) (w : InfinitePlace L) :
    mat (blkL d n h) w = kr d (mat h w) := rfl

theorem padMat_eq {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (padMat ℂ A : Matrix (Fin M) (Fin M) ℂ) = padM A + padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n <;> simp [padMat, padM, hij]

theorem padMat_conjTranspose {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (padMat ℂ A : Matrix (Fin M) (Fin M) ℂ)ᴴ = padMat ℂ Aᴴ := by
  ext i j
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n
  · have hji : (j : ℕ) < n ∧ (i : ℕ) < n := ⟨hij.2, hij.1⟩
    simp [padMat, hij]
  · have hji : ¬((j : ℕ) < n ∧ (i : ℕ) < n) := fun h => hij ⟨h.2, h.1⟩
    by_cases e : i = j
    · subst e
      have hi : ¬(i : ℕ) < n := fun h' => hij ⟨h', h'⟩
      simp [padMat, hi]
    · simp [padMat, hij, hji, e, Ne.symm e]

theorem padMat_mul {n M : ℕ} (h : n ≤ M) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (padMat ℂ (A * B) : Matrix (Fin M) (Fin M) ℂ) = padMat ℂ A * padMat ℂ B :=
  (padHom ℂ h).map_mul A B

theorem padMat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n M : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    (padMat R A : Matrix (Fin M) (Fin M) R).map f = padMat S (A.map f) := by
  ext i j
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n
  · simp [padMat, hij]
  · by_cases e : i = j
    · subst e
      have hi : ¬(i : ℕ) < n := fun h' => hij ⟨h', h'⟩
      simp [padMat, hi]
    · simp [padMat, hij, e]

theorem kr_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : (kr d A).map f = kr d (A.map f) := by
  ext i j
  simp only [kr, reindex_apply, map_apply, submatrix_apply, kroneckerMap_apply, one_apply]
  split_ifs <;> simp

theorem kr_conjTranspose (d : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : (kr d A)ᴴ = kr d Aᴴ := by
  ext i j
  simp only [kr, reindex_apply, conjTranspose_apply, submatrix_apply, kroneckerMap_apply, one_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

theorem kr_mul (d : ℕ) {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : kr d (A * B) = kr d A * kr d B := by
  simp only [kr, reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.mul_one]

omit [NumberField L] in
theorem coe_emb_inv {N : ℕ} (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← Pi.inv_apply, ← map_inv]
  rfl

theorem coe_stab {R : Type} [CommRing R] {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) R) :
    ((stab R n N h g : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) = padMat R (g : Matrix (Fin n) (Fin n) R) :=
  rfl

theorem coe_psi {R : Type} [CommRing R] (d n : ℕ) (g : GL (Fin n) R) :
    ((psi R d n g : GL (Fin (d * n)) R) : Matrix (Fin (d * n)) (Fin (d * n)) R) =
      kr d (g : Matrix (Fin n) (Fin n) R) :=
  rfl

theorem compCLM_comp {V W X : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X] {q : ℕ} (f : X [⋀^Fin q]→L[ℝ] ℝ)
    (A : W →L[ℝ] X) (B : V →L[ℝ] W) :
    (f.compContinuousLinearMap A).compContinuousLinearMap B = f.compContinuousLinearMap (A.comp B) := by
  ext v; rfl

theorem fromBlocks_posDef {n k : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    (fromBlocks H 0 0 (1 : Matrix (Fin k) (Fin k) ℂ)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · unfold IsHermitian
    rw [fromBlocks_conjTranspose]
    simp [hH.isHermitian.eq]
  · have hxe : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := (Sum.elim_comp_inl_inr x).symm
    have hst : star x = Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) := by
      ext (i | i) <;> rfl
    rw [hst, hxe, fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add, Matrix.one_mulVec, Sum.elim_comp_inl,
      Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
    by_cases ha : x ∘ Sum.inl = 0
    · have hb : x ∘ Sum.inr ≠ 0 := by
        intro hb
        apply hx
        rw [hxe, ha, hb]
        ext (i | i) <;> rfl
      rw [ha, Matrix.mulVec_zero, star_zero, dotProduct_zero, zero_add]
      exact dotProduct_star_self_pos_iff.2 hb
    · exact add_pos_of_pos_of_nonneg (hH.dotProduct_mulVec_pos ha) (dotProduct_star_self_nonneg _)

theorem padMat_posDef {n M : ℕ} (h : n ≤ M) {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) :
    (padMat ℂ H : Matrix (Fin M) (Fin M) ℂ).PosDef := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [padMat_add, reindex_apply]
  exact PosDef.submatrix (fromBlocks_posDef hH) (Equiv.injective _)

theorem kr_posDef (d : ℕ) {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) : (kr d H).PosDef := by
  rw [kr, reindex_apply]
  exact PosDef.submatrix (PosDef.one.kronecker hH) (Equiv.injective _)

end BlockSumPreservesCone

open BlockSumPreservesCone

theorem tStab : TStab := by
  intro L _ _ n N h γ
  apply HS_ext
  intro w
  rw [mat_add]
  show mat (actL (emb L N (stab (𝓞 L) n N h γ)) (one L N).1) w =
    padM (mat (actL (emb L n γ) (one L n).1) w) + padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ)
  rw [mat_actL, mat_actL, coe_emb_inv, coe_emb_inv, ← map_inv, coe_stab, padMat_map, mat_one, mat_one,
    padMat_conjTranspose]
  simp only [Matrix.mul_one]
  rw [← padMat_mul h, padMat_eq]

theorem tBlk : TBlk := by
  intro L _ _ d n γ
  apply HS_ext
  intro w
  show mat (actL (emb L (d * n) (psi (𝓞 L) d n γ)) (one L (d * n)).1) w =
    kr d (mat (actL (emb L n γ) (one L n).1) w)
  rw [mat_actL, mat_actL, coe_emb_inv, coe_emb_inv, ← map_inv, coe_psi, kr_map, mat_one, mat_one,
    kr_conjTranspose]
  simp only [Matrix.mul_one]
  rw [kr_mul]

theorem pStab : PStab := by
  intro L _ _ n N q hnN ω hω g h hh
  let g' : Gp L N := fun w => stab ℂ n N hnN (g w)
  have hg' : ∀ w, (((g' w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      padMat ℂ (((g w)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := fun w => by
    show (((stab ℂ n N hnN (g w))⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = _
    rw [← map_inv, coe_stab]
  have hpadM : ∀ Y : Matrix (Fin n) (Fin n) ℂ, (padM Y : Matrix (Fin N) (Fin N) ℂ) =
      padMat ℂ Y - padMat ℂ (0 : Matrix (Fin n) (Fin n) ℂ) := fun Y => by
    rw [padMat_eq Y, add_sub_cancel_right]
  have hJ : padL n N (actL g h) + eL n N = actL g' (padL n N h + eL n N) := HS_ext fun w => by
    rw [mat_add, mat_actL, mat_add, mat_padL, mat_padL, mat_eL, mat_actL, hg', ← padMat_eq (mat h w),
      padMat_conjTranspose, ← padMat_mul hnN, ← padMat_mul hnN, ← padMat_eq]
  have hP : (padL n N).comp (actL g) = (actL g').comp (padL (L := L) n N) := by
    ext1 Y
    apply HS_ext
    intro w
    simp only [ContinuousLinearMap.comp_apply]
    rw [mat_padL, mat_actL, mat_actL, mat_padL, hg', hpadM, hpadM, Matrix.mul_sub, Matrix.sub_mul,
      padMat_conjTranspose, ← padMat_mul hnN, ← padMat_mul hnN, ← padMat_mul hnN, ← padMat_mul hnN,
      Matrix.mul_zero, Matrix.zero_mul]
  have hpos : padL n N h + eL n N ∈ Pos L N := fun w => by
    rw [mat_add, mat_padL, mat_eL, ← padMat_eq]
    exact padMat_posDef hnN (hh w)
  show ((ω (padL n N (actL g h) + eL n N)).compContinuousLinearMap (padL n N)).compContinuousLinearMap
      (actL g) = (ω (padL n N h + eL n N)).compContinuousLinearMap (padL n N)
  rw [hJ, compCLM_comp, hP, ← compCLM_comp, hω g' _ hpos]

theorem blockSum_preserves_cone : PBlk := by
  intro L _ _ d n q ω hω g h hh
  let g' : Gp L (d * n) := fun w => psi ℂ d n (g w)
  have hg' : ∀ w, (((g' w)⁻¹ : GL (Fin (d * n)) ℂ) : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) =
      kr d (((g w)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := fun w => by
    show (((psi ℂ d n (g w))⁻¹ : GL (Fin (d * n)) ℂ) : Matrix (Fin (d * n)) (Fin (d * n)) ℂ) = _
    rw [← map_inv, coe_psi]
  have hJ : blkL d n (actL g h) + 0 = actL g' (blkL d n h + 0) := HS_ext fun w => by
    rw [add_zero, add_zero, mat_actL, mat_blkL, mat_blkL, mat_actL, hg', kr_conjTranspose, kr_mul, kr_mul]
  have hP : (blkL d n).comp (actL g) = (actL g').comp (blkL (L := L) d n) := by
    ext1 Y
    apply HS_ext
    intro w
    simp only [ContinuousLinearMap.comp_apply]
    rw [mat_blkL, mat_actL, mat_actL, mat_blkL, hg', kr_conjTranspose, kr_mul, kr_mul]
  have hpos : blkL d n h + 0 ∈ Pos L (d * n) := fun w => by
    rw [add_zero, mat_blkL]
    exact kr_posDef d (hh w)
  show ((ω (blkL d n (actL g h) + 0)).compContinuousLinearMap (blkL d n)).compContinuousLinearMap
      (actL g) = (ω (blkL d n h + 0)).compContinuousLinearMap (blkL d n)
  rw [hJ, compCLM_comp, hP, ← compCLM_comp, hω g' _ hpos]

end PositivityTheory.KB.BlockInvariants

end
