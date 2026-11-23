import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpUpt

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_mul_self (R : Type) [CommRing R] (j : ZMod 2) : sg R j * sg R j = 1 := by
  rw [sg, ← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem sg_sub (R : Type) [CommRing R] (i j : ZMod 2) : sg R (i - j) = sg R i * sg R j := by
  have key : ∀ a b : ZMod 2, (a - b).val % 2 = (a.val + b.val) % 2 := by decide
  rw [sg, sg, sg, ← pow_add, neg_one_pow_eq_pow_mod_two, key, ← neg_one_pow_eq_pow_mod_two]

private theorem map_sg {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) :
    σ (sg R j) = sg R j := by simp [sg]

private theorem grM_iff {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ σ.mapMatrix M = diagonal (fun a => sg R (α a)) * M * diagonal (fun b => sg R (β b)) := by
  unfold GrM
  rw [← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  change σ (M a b) = sg R (α a - β b) * M a b ↔ _
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, sg_sub]
  constructor <;> intro h <;> rw [h] <;> ring

private theorem diag_sq (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) :
    diagonal (fun a => sg R (α a)) * diagonal (fun a => sg R (α a)) = 1 := by
  rw [diagonal_mul_diagonal]
  simp only [sg_mul_self]
  exact diagonal_one

private theorem map_diag {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α : Fin 3 → ZMod 2) :
    σ.mapMatrix (diagonal (fun a => sg R (α a))) = diagonal (fun a => sg R (α a)) := by
  rw [AlgHom.mapMatrix_apply, Matrix.diagonal_map (map_zero σ)]
  simp only [map_sg]

private theorem exists_sign {R : Type} [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) (x : R) :
    ∃ j : ZMod 2, IsUnit (1 + sg R j * x) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := 1 + x) (b := 1 - x)
      (by convert h2 using 1; ring) with h | h
  · refine ⟨0, ?_⟩
    simpa [sg] using h
  · refine ⟨1, ?_⟩
    rw [show sg R 1 = -1 from by rw [sg, show (1 : ZMod 2).val = 1 from rfl, pow_one]]
    simpa [sub_eq_add_neg] using h

theorem UpperTheory.V.Fr.ep_gflag :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ {H : Type} (r : H → Matrix (Fin 3) (Fin 3) R) (g : GL (Fin 3) R), (∀ s, GrM σ pq pq (r s)) → (∀ s, UpT ((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R))) → (∀ s i, ((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i i ∈ evp σ 0) → (∃ s, ∀ i j, i ≠ j → IsUnit (((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i i - ((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) j j)) → ∃ (u : GL (Fin 3) R) (α : Fin 3 → ZMod 2), UpT (u : Matrix (Fin 3) (Fin 3) R) ∧ GrM σ α pq ((u * g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  intro O _ _ _ _ h2 R _ _ _ σ hσ H r g hr hT hd hs
  have h2R : IsUnit (2 : R) := by
    have := h2.map (algebraMap O R)
    rwa [map_ofNat] at this
  obtain ⟨s0, hs0⟩ := hs
  have hT0 := hT s0
  have hd0 := hd s0
  set G : Matrix (Fin 3) (Fin 3) R := (g : Matrix (Fin 3) (Fin 3) R) with hGdef
  set Gi : Matrix (Fin 3) (Fin 3) R := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) with hGidef
  have hGGi : G * Gi = 1 := g.mul_inv
  have hGiG : Gi * G = 1 := g.inv_mul
  set P : Matrix (Fin 3) (Fin 3) R := diagonal (fun a => sg R (pq a)) with hPdef
  have hPP : P * P = 1 := diag_sq R pq
  have hσP : σ.mapMatrix P = P := map_diag σ pq
  have hSS : ∀ M : Matrix (Fin 3) (Fin 3) R, σ.mapMatrix (σ.mapMatrix M) = M := by
    intro M
    ext i j
    simp [AlgHom.mapMatrix_apply, hσ]
  have hσr : σ.mapMatrix (r s0) = P * r s0 * P := (grM_iff σ pq pq (r s0)).1 (hr s0)
  have hσGiG : σ.mapMatrix Gi * σ.mapMatrix G = 1 := by rw [← map_mul, hGiG, map_one]
  obtain ⟨h, hh⟩ : ∃ h, h = G * P * σ.mapMatrix Gi := ⟨_, rfl⟩
  have hσh : σ.mapMatrix h = σ.mapMatrix G * P * Gi := by
    rw [hh, map_mul, map_mul, hσP, hSS]
  have hhσh : h * σ.mapMatrix h = 1 := by
    rw [hσh, hh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (σ.mapMatrix Gi), hσGiG, Matrix.one_mul, ← Matrix.mul_assoc P P, hPP,
      Matrix.one_mul, hGGi]
  have hUh : UpT h := by
    set T := G * r s0 * Gi with hTdef
    refine ep_upt h (σ.mapMatrix T) T ?_ hT0 ?_ ?_
    · intro i j hij
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, hT0 i j hij, map_zero]
    · intro i j hij
      have hfix : σ (T j j) = T j j := by
        have := hd0 j
        change σ (T j j) = sg R 0 * T j j at this
        rw [this, sg, ZMod.val_zero, pow_zero, one_mul]
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, hfix]
      exact hs0 j i hij.ne
    · rw [hh, hTdef, map_mul, map_mul, hσr]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (σ.mapMatrix Gi) (σ.mapMatrix G), hσGiG, Matrix.one_mul,
        ← Matrix.mul_assoc P P, hPP, Matrix.one_mul, ← Matrix.mul_assoc Gi G, hGiG, Matrix.one_mul]
  have hex : ∀ i, ∃ j : ZMod 2, IsUnit (1 + sg R j * h i i) := fun i => exists_sign h2R (h i i)
  choose α hα using hex
  set D : Matrix (Fin 3) (Fin 3) R := diagonal (fun a => sg R (α a)) with hDdef
  have hDD : D * D = 1 := diag_sq R α
  have hσD : σ.mapMatrix D = D := map_diag σ α
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 1 + h * D := ⟨_, rfl⟩
  have hYU : Y.BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    rw [hY, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij'), hDdef, Matrix.mul_diagonal,
      hUh i j hij', zero_mul, add_zero]
  have hYdet : IsUnit Y.det := by
    rw [Matrix.det_of_upperTriangular hYU, Fin.prod_univ_three]
    have hu : ∀ i, IsUnit (Y i i) := by
      intro i
      rw [hY, Matrix.add_apply, Matrix.one_apply_eq, hDdef, Matrix.mul_diagonal, mul_comm]
      exact hα i
    exact ((hu 0).mul (hu 1)).mul (hu 2)
  have hYu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).2 hYdet
  set Yi : Matrix (Fin 3) (Fin 3) R := ((hYu.unit⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
    with hYidef
  have hYYi : Y * Yi = 1 := hYu.mul_val_inv
  have hYiY : Yi * Y = 1 := hYu.val_inv_mul
  have hUYi : UpT Yi := by
    haveI : Invertible Y := ⟨Yi, hYiY, hYYi⟩
    have := Matrix.blockTriangular_inv_of_blockTriangular hYU
    rw [Matrix.inv_eq_left_inv hYiY] at this
    exact fun i j hij => this hij
  have hσYσYi : σ.mapMatrix Y * σ.mapMatrix Yi = 1 := by rw [← map_mul, hYYi, map_one]
  have hYeq : h * σ.mapMatrix Y = Y * D := by
    rw [hY, map_add, map_one, map_mul, hσD, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
      Matrix.one_mul, ← Matrix.mul_assoc, hhσh, Matrix.one_mul, Matrix.mul_assoc, hDD,
      Matrix.mul_one, add_comm]
  have hGP : h * σ.mapMatrix G = G * P := by
    rw [hh, Matrix.mul_assoc, hσGiG, Matrix.mul_one]
  have hYih : Yi * h = D * σ.mapMatrix Yi := by
    calc Yi * h = Yi * (h * (σ.mapMatrix Y * σ.mapMatrix Yi)) := by rw [hσYσYi, Matrix.mul_one]
      _ = Yi * (Y * D) * σ.mapMatrix Yi := by rw [← hYeq]; simp only [Matrix.mul_assoc]
      _ = D * σ.mapMatrix Yi := by rw [← Matrix.mul_assoc Yi Y, hYiY, Matrix.one_mul]
  refine ⟨hYu.unit⁻¹, α, hUYi, ?_⟩
  rw [grM_iff, Units.val_mul]
  change σ.mapMatrix (Yi * G) = D * (Yi * G) * P
  rw [map_mul, Matrix.mul_assoc D, Matrix.mul_assoc Yi, ← hGP, ← Matrix.mul_assoc Yi, hYih,
    Matrix.mul_assoc D, ← Matrix.mul_assoc D D, hDD, Matrix.one_mul]
