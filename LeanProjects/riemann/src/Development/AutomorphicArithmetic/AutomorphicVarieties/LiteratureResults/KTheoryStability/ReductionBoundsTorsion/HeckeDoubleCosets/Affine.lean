import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal

noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section Affine

variable {L : Type} [Field L] [NumberField L]

theorem aff_alg_inj : Function.Injective (algebraMap (𝓞 L) L) :=
  FaithfulSMul.algebraMap_injective (𝓞 L) L

theorem aff_toK_val (N : ℕ) (g : Gm L N) (a b : Fin N) :
    (toK L N g : Matrix (Fin N) (Fin N) L) a b =
      algebraMap (𝓞 L) L ((g : Matrix (Fin N) (Fin N) (𝓞 L)) a b) :=
  rfl

theorem aff_toK_inj (N : ℕ) : Function.Injective (toK L N) := by
  intro a b hab
  refine Matrix.GeneralLinearGroup.ext fun x y => aff_alg_inj ?_
  rw [← aff_toK_val, ← aff_toK_val, hab]

theorem aff_toK_stab (n N : ℕ) (h : n ≤ N) (c : Gm L n) :
    toK L N (stab (𝓞 L) n N h c) = stab L n N h (toK L n c) := by
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  rw [aff_toK_val, stab_apply, stab_apply]
  split_ifs <;> simp [aff_toK_val]

end Affine

theorem aff_stab_low {R : Type} [CommRing R] (n r : ℕ) (g : GL (Fin n) R) (i : Fin r) (b : Fin (n + r)) :
    (stab R n (n + r) (Nat.le_add_right n r) g : Matrix (Fin (n + r)) (Fin (n + r)) R) (Fin.natAdd n i) b =
      (1 : Matrix (Fin (n + r)) (Fin (n + r)) R) (Fin.natAdd n i) b := by
  rw [stab_apply, dif_neg (by simp only [Fin.val_natAdd]; omega), Matrix.one_apply]

theorem aff_stab_lowc {R : Type} [CommRing R] (n r : ℕ) (g : GL (Fin n) R) (i : Fin r) (a : Fin (n + r)) :
    (stab R n (n + r) (Nat.le_add_right n r) g : Matrix (Fin (n + r)) (Fin (n + r)) R) a (Fin.natAdd n i) =
      (1 : Matrix (Fin (n + r)) (Fin (n + r)) R) a (Fin.natAdd n i) := by
  rw [stab_apply, dif_neg (by simp only [Fin.val_natAdd]; omega), Matrix.one_apply]

theorem aff_stab_top {R : Type} [CommRing R] (n r : ℕ) (g : GL (Fin n) R) (a b : Fin n) :
    (stab R n (n + r) (Nat.le_add_right n r) g : Matrix (Fin (n + r)) (Fin (n + r)) R) (Fin.castAdd r a)
      (Fin.castAdd r b) = (g : Matrix (Fin n) (Fin n) R) a b := by
  rw [stab_apply, dif_pos (by simp only [Fin.val_castAdd]; exact ⟨a.2, b.2⟩)]
  rfl

theorem aff_conj {K : Type} [Field K] (n r : ℕ) (i : Fin r) (h : GL (Fin n) K) (y : Fin (n + r) → K)
    (G : GL (Fin (n + r)) K)
    (hG : (G : Matrix (Fin (n + r)) (Fin (n + r)) K) =
      1 + vecMulVec (y - Pi.single (Fin.natAdd n i) 1) (Pi.single (Fin.natAdd n i) 1)) :
    ((G⁻¹ * stab K n (n + r) (Nat.le_add_right n r) h * G : GL (Fin (n + r)) K) :
        Matrix (Fin (n + r)) (Fin (n + r)) K) =
      (stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) +
        vecMulVec (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) - 1) *ᵥ y)
          (Pi.single (Fin.natAdd n i) 1) := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin (n + r)) (Fin (n + r)) K,
      S = (stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Fin (n + r) → K, e = Pi.single (Fin.natAdd n i) 1 := ⟨_, rfl⟩
  rw [← hS, ← he]
  rw [← he] at hG
  have hrow : ∀ b, S (Fin.natAdd n i) b = (1 : Matrix (Fin (n + r)) (Fin (n + r)) K) (Fin.natAdd n i) b := by
    intro b; rw [hS]; exact aff_stab_low n r h i b
  have hcol : ∀ a, S a (Fin.natAdd n i) = (1 : Matrix (Fin (n + r)) (Fin (n + r)) K) a (Fin.natAdd n i) := by
    intro a; rw [hS]; exact aff_stab_lowc n r h i a
  have h1 : e ᵥ* S = e := by
    funext b
    simp [he, vecMul, dotProduct, Pi.single_apply, hrow, Matrix.one_apply]
    split_ifs with h₁ h₂ h₂ <;> first | rfl | (exfalso; exact h₂ h₁.symm) | (exfalso; exact h₁ h₂.symm)
  have h2 : ((S - 1) *ᵥ y) (Fin.natAdd n i) = 0 := by
    simp [mulVec, dotProduct, Matrix.sub_apply, hrow]
  have h3 : e ᵥ* vecMulVec ((S - 1) *ᵥ y) e = 0 := by
    funext b
    simp only [vecMul, dotProduct, vecMulVec_apply, Pi.zero_apply]
    rw [Finset.sum_eq_single (Fin.natAdd n i)]
    · rw [h2]; ring
    · intro c _ hc; rw [he, Pi.single_apply, if_neg hc]; ring
    · simp
  have h4 : S *ᵥ e = e := by
    funext a
    simp [he, mulVec, dotProduct, Pi.single_apply, hcol, Matrix.one_apply]
  have key : (1 + vecMulVec (y - e) e) * (S + vecMulVec ((S - 1) *ᵥ y) e) = S * (1 + vecMulVec (y - e) e) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, h1, h3,
      Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_sub, h4]
    ext a b
    simp only [Matrix.add_apply, vecMulVec_apply, Pi.sub_apply, Pi.zero_apply, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    ring
  rw [Units.val_mul, Units.val_mul, ← hS, hG, Matrix.mul_assoc, ← key, ← Matrix.mul_assoc, ← hG,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

section Gamma

variable {L : Type} [Field L] [NumberField L]

theorem aff_gamma (π : 𝓞 L) (hπ : Prime π) (n r : ℕ) (hn : 1 ≤ n) (c : Gm L (n + r)) (i : Fin r)
    (hi : ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n i) ⟨0, by omega⟩ ∉
      Ideal.span {π}) :
    ∃ (y : Fin (n + r) → L) (G : GK L (n + r)) (γ : Gm L (n + r)),
      (G : Matrix (Fin (n + r)) (Fin (n + r)) L) =
        1 + vecMulVec (y - Pi.single (Fin.natAdd n i) 1) (Pi.single (Fin.natAdd n i) 1) ∧
      toK L (n + r) γ = qel L (n + r) π hπ.ne_zero * toK L (n + r) c * G := by
  have hmax : (Ideal.span {π}).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  obtain ⟨u, j0, hj0, hu⟩ := hmax.exists_inv hi
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hj0
  obtain ⟨o, ho⟩ : ∃ o : Fin (n + r), o = ⟨0, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Fin (n + r), p = Fin.natAdd n i := ⟨_, rfl⟩
  rw [← ho, ← hp] at hu
  rw [← hp]
  set alg := algebraMap (𝓞 L) L with halg
  have hπL : alg π ≠ 0 := (map_ne_zero_iff _ aff_alg_inj).mpr hπ.ne_zero
  set cL : Matrix (Fin (n + r)) (Fin (n + r)) L := (toK L (n + r) c : Matrix (Fin (n + r)) (Fin (n + r)) L) with hcL
  set ciL : Matrix (Fin (n + r)) (Fin (n + r)) L := (toK L (n + r) c⁻¹ : Matrix (Fin (n + r)) (Fin (n + r)) L) with hciL
  set e : Fin (n + r) → L := Pi.single p 1 with he
  set vL : Fin (n + r) → L := ciL *ᵥ Pi.single o 1 with hvL
  set y : Fin (n + r) → L := ((alg π)⁻¹ * alg u) • vL + alg s • e with hy
  have hcci : cL * ciL = 1 := by
    rw [hcL, hciL, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hvp : vL p = alg (((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) p o) := by
    rw [hvL, Matrix.mulVec_single_one]; rfl
  have hyp : y p = (alg π)⁻¹ := by
    have h := congrArg alg hu
    simp only [map_add, map_mul, map_one] at h
    rw [hy, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hvp, he, Pi.single_eq_same, smul_eq_mul, smul_eq_mul]
    field_simp
    try linear_combination h
  have hdet : (1 + vecMulVec (y - e) e).det ≠ 0 := by
    have h1 : vecMulVec (y - e) e = replicateCol Unit (y - e) * replicateRow Unit e := by
      ext a b; simp [vecMulVec_apply, Matrix.mul_apply]
    rw [h1, det_one_add_replicateCol_mul_replicateRow]
    have h2 : e ⬝ᵥ (y - e) = y p - 1 := by
      simp [he, dotProduct, Pi.single_apply]
    rw [h2, hyp]; simp [hπL]
  refine ⟨y, GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩

  set qO : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L) := diagonal fun a => if (a : ℕ) = 0 then π else 1 with hqO
  set eO : Fin (n + r) → 𝓞 L := Pi.single p 1 with heO
  set zO : Fin (n + r) → 𝓞 L := Pi.single o u + (s - 1) • ((qO * (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))) *ᵥ eO) with hzO
  set γM : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L) := qO * (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) + vecMulVec zO eO with hγM
  have hqM : ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) = qO.map alg := by
    rw [hqO, Matrix.diagonal_map (map_zero _)]
    show diagonal _ = _
    congr 1
    funext a
    split_ifs <;> first | rfl | simp
  have hQ : (qO * (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))).map alg =
      ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL := by
    rw [Matrix.map_mul, hqM]; rfl
  have he' : (fun a => alg (eO a)) = e := by
    funext a; rw [heO, he, Pi.single_apply, Pi.single_apply]; split_ifs <;> simp
  have h1 : cL *ᵥ vL = Pi.single o 1 := by rw [hvL, Matrix.mulVec_mulVec, hcci, Matrix.one_mulVec]
  have h2 : cL *ᵥ y = ((alg π)⁻¹ * alg u) • Pi.single o 1 + alg s • (cL *ᵥ e) := by
    rw [hy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1]
  have h3 : ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) *ᵥ Pi.single o (1 : L) =
      Pi.single o (alg π) := by
    rw [hqM, hqO, Matrix.diagonal_map (map_zero _), diagonal_mulVec_single]
    congr 1
    simp [ho]
  have h4 : (((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL) *ᵥ (y - e) =
      fun a => alg (zO a) := by
    rw [Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h3,
      Matrix.mulVec_mulVec]
    funext a
    have h5 : alg (((qO * (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))) *ᵥ eO) a) =
        ((((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL) *ᵥ e) a := by
      rw [RingHom.map_mulVec, hQ]
      congr 1
      try exact he'
    rw [hzO, Pi.add_apply, Pi.smul_apply, map_add, smul_eq_mul, map_mul, h5, map_sub, map_one]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply]
    split_ifs
    · field_simp
      try ring
    · simp
      try ring
  have hγdet : IsUnit γM.det := by
    have h6 : γM.map alg = ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL *
        (1 + vecMulVec (y - e) e) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, h4, hγM, Matrix.map_add _ (map_add alg), hQ]
      congr 1
      ext a b
      simp only [Matrix.map_apply, vecMulVec_apply, map_mul]
      rw [← he']
    have h7 : alg γM.det = alg (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)).det := by
      rw [RingHom.map_det, RingHom.map_det]
      show (γM.map alg).det = (cL).det
      rw [h6, Matrix.det_mul, Matrix.det_mul, hqM, hqO, Matrix.diagonal_map (map_zero _), Matrix.det_diagonal]
      have h8 : (1 + vecMulVec (y - e) e).det = (alg π)⁻¹ := by
        have h1 : vecMulVec (y - e) e = replicateCol Unit (y - e) * replicateRow Unit e := by
          ext a b; simp [vecMulVec_apply, Matrix.mul_apply]
        rw [h1, det_one_add_replicateCol_mul_replicateRow]
        have h2 : e ⬝ᵥ (y - e) = y p - 1 := by
          simp [he, dotProduct, Pi.single_apply]
        rw [h2, hyp]; ring
      rw [h8, Finset.prod_eq_single o]
      · simp [ho]
        field_simp
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext (by rw [h, ho]))
        simp [this]
      · simp
    rw [aff_alg_inj h7]
    exact (Matrix.isUnits_det_units c)
  refine ⟨GeneralLinearGroup.mk'' γM hγdet, rfl, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  rw [aff_toK_val]
  have h6 : γM.map alg = ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL *
      (1 + vecMulVec (y - e) e) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, h4, hγM, Matrix.map_add _ (map_add alg), hQ]
    congr 1
    ext a b
    simp only [Matrix.map_apply, vecMulVec_apply, map_mul]
    rw [← he']
  have h9 := congrArg (fun M => M a b) h6
  simp only [Matrix.map_apply] at h9
  exact h9

end Gamma

theorem aff_blk_top {K : Type} [Field K] (n r : ℕ) (i : Fin r) (h : GL (Fin n) K) (y : Fin (n + r) → K)
    (a b : Fin n) :
    (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) +
        vecMulVec (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) - 1) *ᵥ y)
          (Pi.single (Fin.natAdd n i) 1) : Matrix (Fin (n + r)) (Fin (n + r)) K)) (Fin.castAdd r a) (Fin.castAdd r b) = (h : Matrix (Fin n) (Fin n) K) a b := by
  have hne : Fin.castAdd r b ≠ Fin.natAdd n i := by
    intro hh
    have := congrArg Fin.val hh
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  rw [Matrix.add_apply, vecMulVec_apply, Pi.single_apply, if_neg hne, mul_zero, add_zero, aff_stab_top]

theorem aff_blk_low {K : Type} [Field K] (n r : ℕ) (i : Fin r) (h : GL (Fin n) K) (y : Fin (n + r) → K)
    (a : Fin r) (b : Fin (n + r)) :
    (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) +
        vecMulVec (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) - 1) *ᵥ y)
          (Pi.single (Fin.natAdd n i) 1) : Matrix (Fin (n + r)) (Fin (n + r)) K)) (Fin.natAdd n a) b =
      (1 : Matrix (Fin (n + r)) (Fin (n + r)) K) (Fin.natAdd n a) b := by
  have h0 : (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) - 1) *ᵥ y)
      (Fin.natAdd n a) = 0 := by
    simp [mulVec, dotProduct, Matrix.sub_apply, aff_stab_low]
  rw [Matrix.add_apply, vecMulVec_apply, h0, zero_mul, add_zero, aff_stab_low]

theorem pStabVan : PStabVan := by
  intro _hCh hEv hAff L _ _ hC k hk π hπ n r hn _hr c ⟨i, hi⟩ F hF hdF H hH w hw
  obtain ⟨y, G, γ, hG, hγ⟩ := aff_gamma π hπ n r hn c i hi
  set q := qel L (n + r) π hπ.ne_zero with hq
  have hex : ∀ h : H, ∃ x : Gm L (n + r), toK L (n + r) x =
      G⁻¹ * toK L (n + r) (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (h : Gm L n)) * G := by
    intro h
    obtain ⟨_, ⟨δ, rfl⟩, hx⟩ := hH h h.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hx
    refine ⟨γ⁻¹ * δ * γ, ?_⟩
    have hδ : toK L (n + r) δ =
        q * toK L (n + r) (c * stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (h : Gm L n) * c⁻¹) * q⁻¹ := by
      rw [← hx]; group
    rw [map_mul, map_mul, map_inv, hγ, hδ, map_mul, map_mul, map_inv]
    group
  choose fx hfx using hex
  let f : H →* Gm L (n + r) := MonoidHom.mk' fx (fun a b => aff_toK_inj _ (by
    rw [map_mul, hfx, hfx, hfx, Subgroup.coe_mul, map_mul, map_mul]
    group))
  have hf : ∀ h : H, toK L (n + r) (f h) =
      G⁻¹ * toK L (n + r) (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (h : Gm L n)) * G := hfx
  have hM : ∀ h : H, (toK L (n + r) (f h) : Matrix (Fin (n + r)) (Fin (n + r)) L) =
      (stab L n (n + r) (Nat.le_add_right n r) (toK L n h) : Matrix (Fin (n + r)) (Fin (n + r)) L) +
        vecMulVec (((stab L n (n + r) (Nat.le_add_right n r) (toK L n h) : Matrix (Fin (n + r)) (Fin (n + r)) L) - 1)
          *ᵥ y) (Pi.single (Fin.natAdd n i) 1) := by
    intro h
    rw [hf, aff_toK_stab]
    exact aff_conj n r i (toK L n h) y G hG
  have hblock : ∀ x : H, ∃ B : Matrix (Fin n) (Fin r) (𝓞 L),
      (f x : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (H.subtype x : Matrix (Fin n) (Fin n) (𝓞 L)) B 0 1) := by
    intro x
    refine ⟨fun a b => (f x : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.castAdd r a) (Fin.natAdd n b), ?_⟩
    refine Matrix.ext fun a b => ?_
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
    rcases a with a | a <;> rcases b with b | b
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁]
      apply aff_alg_inj
      rw [← aff_toK_val, hM, aff_blk_top]
      rfl
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      rfl
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      show (f x : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n a) (Fin.castAdd r b) = 0
      apply aff_alg_inj
      rw [map_zero, ← aff_toK_val, hM, aff_blk_low, Matrix.one_apply, if_neg]
      intro hh
      have := congrArg Fin.val hh
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      show (f x : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n a) (Fin.natAdd n b) =
        (1 : Matrix (Fin r) (Fin r) (𝓞 L)) a b
      apply aff_alg_inj
      rw [← aff_toK_val, hM, aff_blk_low, Matrix.one_apply, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg hab, if_neg (fun hh => hab (Fin.ext (by
        have := congrArg Fin.val hh; simp only [Fin.val_natAdd] at this; omega))), map_zero]
  have key : ∀ h : H, q * toK L (n + r) (c * stab (𝓞 L) n (n + r) (Nat.le_add_right n r) ((h : Gm L n) * 1)) =
      toK L (n + r) γ • ((toK L (n + r)).comp f h • G⁻¹) := by
    intro h
    rw [smul_eq_mul, smul_eq_mul, MonoidHom.comp_apply, hf, hγ, mul_one, map_mul]
    group
  have hL : ev H.subtype (fun y => F fun j => q * toK L (n + r)
      (c * stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (y j))) 1 w =
      ev ((toK L (n + r)).comp f) F G⁻¹ w := by
    unfold ev
    refine Finsupp.sum_congr fun x _ => ?_
    congr 1
    rw [← hF γ (fun j => (toK L (n + r)).comp f (Fin.partialProd x j) • G⁻¹)]
    exact congrArg F (funext fun j => key (Fin.partialProd x j))
  have hR : ev H.subtype (fun y => F fun j => toK L (n + r)
      (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (y j))) 1 w =
      ev (toK L (n + r)) F 1 (cmap ((stab (𝓞 L) n (n + r) (Nat.le_add_right n r)).comp H.subtype) (k + 1) w) := by
    rw [ev_cmap]
    unfold ev
    refine Finsupp.sum_congr fun x _ => ?_
    simp only [MonoidHom.comp_apply, smul_eq_mul, mul_one]
  have hE1 := hEv H (GK L (n + r)) (GK L (n + r)) ((toK L (n + r)).comp f) k F (fun g y => hF (f g) y) hdF
  have hE2 := hEv (Gm L (n + r)) (GK L (n + r)) (GK L (n + r)) (toK L (n + r)) k F hF hdF
  have hbd := hAff L hC k hk n r H f H.subtype hblock w hw
  rw [hL, hR, hE1.2 G⁻¹ 1 w hw, ← ev_cmap]
  have h0 := hE2.1 1 _ hbd
  rw [ev_sub] at h0
  linarith

end PositivityTheory.KB.AffineStabilizerVanishing

end
