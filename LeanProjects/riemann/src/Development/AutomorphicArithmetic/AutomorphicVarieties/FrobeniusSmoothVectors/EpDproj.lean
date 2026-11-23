import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_add (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i + j) = sg K i * sg K j := by
  simp only [sg, ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

private theorem sg_sub (K : Type) [CommRing K] (i j : ZMod 2) : sg K (i - j) = sg K i * sg K j := by
  have h : i - j = i + j := by revert i j; decide
  rw [h, sg_add]

private theorem sg_sq (K : Type) [CommRing K] (i : ZMod 2) : sg K i * sg K i = 1 := by
  have h : i + i = 0 := by revert i; decide
  rw [← sg_add, h]
  simp [sg]

private theorem sg_ne (K : Type) [CommRing K] (i j : ZMod 2) (e : i ≠ j) : sg K i * sg K j = -1 := by
  have h : i + j = 1 := by revert i j; decide
  rw [← sg_add, h]
  show (-1 : K) ^ (1 : ZMod 2).val = -1
  rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

private theorem lin_sg {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup K] [Module O K]
    (D : R →ₗ[O] K) (i : ZMod 2) (x : R) : D (sg R i * x) = sg ℤ i • D x := by
  have h : i = 0 ∨ i = 1 := by revert i; decide
  rcases h with rfl | rfl
  · simp [sg]
  · show D ((-1 : R) ^ (1 : ZMod 2).val * x) = (-1 : ℤ) ^ (1 : ZMod 2).val • D x
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, pow_one, neg_one_mul, map_neg, neg_one_zsmul]

private theorem gl_inv_apply_eq_zero_of_forall_pw_ne_zero {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (G : GL (Fin 3) K)
    (hG : ∀ a b, pw a b ≠ 0 → (G : Matrix (Fin 3) (Fin 3) K) a b = 0) :
    ∀ a b, pw a b ≠ 0 → ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
  set E : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal (fun a => sg K (pq a)) with hE
  have hEE : E * E = 1 := by
    rw [hE, Matrix.diagonal_mul_diagonal]
    simp only [sg_sq]
    exact Matrix.diagonal_one
  have hconj : ∀ (A : Matrix (Fin 3) (Fin 3) K) a b, (E * A * E) a b = sg K (pw a b) * A a b := by
    intro A a b
    rw [hE, Matrix.mul_diagonal, Matrix.diagonal_mul, pw_eq, sg_sub]
    ring
  have hEG : E * (G : Matrix (Fin 3) (Fin 3) K) * E = G := by
    ext a b
    rw [hconj]
    by_cases h : pw a b = 0
    · rw [h]
      simp [sg]
    · rw [hG a b h, mul_zero]
  have hinv1 : (G : Matrix (Fin 3) (Fin 3) K) * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv2 : ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (G : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : (G : Matrix (Fin 3) (Fin 3) K) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E) = 1 := by
      calc (G : Matrix (Fin 3) (Fin 3) K) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E)
          = (E * (G : Matrix (Fin 3) (Fin 3) K) * E) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E) := by
            rw [hEG]
        _ = E * ((G : Matrix (Fin 3) (Fin 3) K) * ((E * E) * (((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E))) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [hEE, Matrix.one_mul, ← Matrix.mul_assoc (G : Matrix (Fin 3) (Fin 3) K), hinv1, Matrix.one_mul, hEE]
    calc E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E
        = (((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * G) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E) := by
          rw [hinv2, Matrix.one_mul]
      _ = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((G : Matrix (Fin 3) (Fin 3) K) * (E * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * E)) := by
          rw [Matrix.mul_assoc]
      _ = ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h1, Matrix.mul_one]
  intro a b hab
  have e := congrFun (congrFun key a) b
  rw [hconj] at e
  have hp : pw a b = 1 := by
    revert hab
    generalize pw a b = p
    revert p
    decide
  have s1 : sg K 1 = -1 := by
    show (-1 : K) ^ (1 : ZMod 2).val = -1
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]
  rw [hp, s1] at e
  have e' : (2 : K) * ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b = 0 := by
    linear_combination -e
  exact (mul_eq_zero.mp e').resolve_left h2

theorem UpperTheory.V.Fr.ep_dproj :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), B.Gr σ π → ∀ j, ∀ D ∈ Tan O R, ∃ D' ∈ derp O σ j, ∀ s, B.tanCo O D' s = prp (ResidueField O) j (B.tanCo O D s) := by
  intro l _ k _ F O _ _ h2 R _ _ _ σ hσ B π hB j D hD
  have h2k : (2 : ResidueField O) ≠ 0 := by
    have := h2.map (residue O)
    rw [map_ofNat] at this
    exact this.ne_zero
  have zs : ∀ (p : ZMod 2) (v : ResidueField O), sg ℤ p • v = sg (ResidueField O) p * v := by
    intro p v
    rw [zsmul_eq_mul]
    simp [sg]
  let D' : R →ₗ[O] ResidueField O :=
    (2 : ResidueField O)⁻¹ • (D + sg (ResidueField O) j • D.comp σ.toLinearMap)
  have hD' : ∀ x, D' x = (2 : ResidueField O)⁻¹ * (D x + sg (ResidueField O) j * D (σ x)) := by
    intro x
    simp [D', smul_eq_mul, mul_add]
  refine ⟨D', Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · intro f g
    have e1 := hD f g
    have e2 := hD (σ f) (σ g)
    rw [res_map, res_map] at e2
    rw [hD', hD', hD', map_mul σ f g, e1, e2]
    simp only [smul_eq_mul]
    ring
  · intro x
    show D' (σ x) = sg (ResidueField O) j * D' x
    rw [hD', hD', hσ]
    linear_combination (-(2 : ResidueField O)⁻¹ * D (σ x)) * sg_sq (ResidueField O) j
  · intro s
    have hM : ∀ a c, σ ((B.r s).mat a c) = sg R (pw a c) * (B.r s).mat a c := by
      intro a c
      rw [pw_eq]
      exact hB.r s a c
    have hDp : ∀ a c, D' ((B.r s).mat a c) = if pw a c = j then D ((B.r s).mat a c) else 0 := by
      intro a c
      rw [hD', hM, lin_sg, zs]
      split_ifs with hp
      · rw [hp]
        field_simp
        linear_combination D ((B.r s).mat a c) * sg_sq (ResidueField O) j
      · rw [← mul_assoc, sg_ne _ _ _ (Ne.symm hp)]
        ring
    have hbar : ∀ a c, pw a c ≠ 0 →
        (((Box.bar O B).r s).left : Matrix (Fin 3) (Fin 3) (ResidueField O)) a c = 0 := by
      intro a c hac
      show res O R ((B.r s).mat a c) = 0
      have hp : pw a c = 1 := by
        revert hac
        generalize pw a c = p
        revert p
        decide
      have e := congrArg (res O R) (hM a c)
      rw [res_map, hp, map_mul] at e
      have s1R : sg R 1 = -1 := by
        show (-1 : R) ^ (1 : ZMod 2).val = -1
        rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]
      rw [s1R, map_neg, map_one] at e
      have e' : (2 : ResidueField O) * res O R ((B.r s).mat a c) = 0 := by
        linear_combination e
      exact (mul_eq_zero.mp e').resolve_left h2k
    have hN := gl_inv_apply_eq_zero_of_forall_pw_ne_zero h2k ((Box.bar O B).r s).left hbar
    ext a b
    show ((B.r s).mat.map D' * (((Box.bar O B).r s).left⁻¹ : GL (Fin 3) (ResidueField O))) a b =
      if pw a b = j then ((B.r s).mat.map D * (((Box.bar O B).r s).left⁻¹ : GL (Fin 3) (ResidueField O))) a b else 0
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hsame : ∀ c, pw c b = 0 → pw a c = pw a b := by
      intro c hcb
      rw [pw_eq] at hcb
      rw [pw_eq, pw_eq, sub_eq_zero.mp hcb]
    split_ifs with hab
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Matrix.map_apply, Matrix.map_apply, hDp]
      by_cases hcb : pw c b = 0
      · rw [if_pos ((hsame c hcb).trans hab)]
      · rw [hN c b hcb, mul_zero, mul_zero]
    · refine Finset.sum_eq_zero (fun c _ => ?_)
      rw [Matrix.map_apply, hDp]
      by_cases hcb : pw c b = 0
      · rw [if_neg (fun h => hab ((hsame c hcb).symm.trans h)), zero_mul]
      · rw [hN c b hcb, mul_zero]
