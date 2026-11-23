import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem z2 (j : ZMod 2) : j = 0 ∨ j = 1 := by revert j; decide

private theorem sg_zero (K : Type) [CommRing K] : sg K 0 = 1 := pow_zero _

private theorem sg_one (K : Type) [CommRing K] : sg K 1 = -1 := pow_one _

private theorem pw_rev (a b : Fin 3) : pw b.rev a.rev = pw a b := by
  revert a b; decide

private theorem zero_of_neg {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {x : K} (h : x = -x) : x = 0 := by
  have : 2 * x = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

private def Dm (K : Type) [CommRing K] : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal fun a => sg K (pq a)

private theorem mem_iff {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K) :
    X ∈ adp K j ↔ Dm K * X = sg K j • (X * Dm K) := by
  have hsq : ∀ y : ZMod 2, sg K y * sg K y = 1 := by
    intro y
    rcases z2 y with rfl | rfl <;> simp [sg_zero, sg_one]
  have hsub : ∀ x y : ZMod 2, sg K (x - y) = sg K x * sg K y := by
    intro x y
    rcases z2 x with rfl | rfl <;> rcases z2 y with rfl | rfl
    · simp [sg_zero]
    · rw [show (0 : ZMod 2) - 1 = 1 from rfl, sg_zero, sg_one, one_mul]
    · rw [show (1 : ZMod 2) - 0 = 1 from rfl, sg_zero, mul_one]
    · rw [show (1 : ZMod 2) - 1 = 0 from rfl, sg_zero, sg_one]
      norm_num
  constructor
  · intro hX
    ext a b
    simp only [Dm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    by_cases hab : pw a b = j
    · rw [← hab, pw_eq, hsub]
      linear_combination (-(sg K (pq a) * X a b)) * hsq (pq b)
    · have h0 : X a b = 0 := hX a b hab
      rw [h0]
      simp
  · intro h
    show ∀ a b, pw a b ≠ j → X a b = 0
    intro a b hab
    have e := congrFun (congrFun h a) b
    simp only [Dm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at e
    have hj : sg K j = -(sg K (pq a) * sg K (pq b)) := by
      rw [pw_eq] at hab
      generalize pq a = x at hab ⊢
      generalize pq b = y at hab ⊢
      rcases z2 x with rfl | rfl <;> rcases z2 y with rfl | rfl <;> rcases z2 j with rfl | rfl <;>
        first | exact absurd (by decide) hab | simp [sg_zero, sg_one]
    rw [hj] at e
    apply zero_of_neg h2
    linear_combination (sg K (pq a)) * e - (X a b + X a b * (sg K (pq b) * sg K (pq b))) * hsq (pq a) -
      X a b * hsq (pq b)

private theorem theta_mem {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (h : X ∈ adp K j) : thetaLie X ∈ adp K j := by
  show ∀ a b, pw a b ≠ j → thetaLie X a b = 0
  intro a b hab
  have hX : X b.rev a.rev = 0 := h b.rev a.rev (by rw [pw_rev]; exact hab)
  have ht : thetaLie X a b = -X b.rev a.rev := by
    simp only [thetaLie, Matrix.neg_apply, Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, one_mul,
      zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    rw [Finset.sum_eq_single b.rev]
    · simp
    · intro c _ hc
      rw [if_neg]
      intro hb
      exact hc (by rw [hb, Fin.rev_rev])
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  rw [ht, hX, neg_zero]

private theorem conj_mem {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (g : GL (Fin 3) K)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) ∈ adp K 0) (j : ZMod 2) (Y : Matrix (Fin 3) (Fin 3) K)
    (h : Y ∈ adp K j) :
    (g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∈ adp K j := by
  rw [mem_iff h2] at hg h ⊢
  rw [sg_zero, one_smul] at hg
  have hgi : Dm K * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Dm K := by
    have e := congrArg (fun M => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hg
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e
    exact e.symm
  calc Dm K * ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        = (Dm K * (g : Matrix (Fin 3) (Fin 3) K)) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          simp only [mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) K) * (Dm K * Y) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hg]
          simp only [mul_assoc]
    _ = (g : Matrix (Fin 3) (Fin 3) K) * (sg K j • (Y * Dm K)) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [h]
    _ = sg K j • ((g : Matrix (Fin 3) (Fin 3) K) * Y *
          (Dm K * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          simp only [mul_assoc]
    _ = sg K j • ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          Dm K) := by
          rw [hgi]
          simp only [mul_assoc]

theorem UpperTheory.V.Fr.ep_ev :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R) (B : Box F 3 R) (π : F.V → Fin 3 → ZMod 2), B.Gr σ π → (B.bar O).Ev π := by
  intro l _ k _ F O _ _ _ _ h2O R _ _ _ σ B π hG
  have h2 : (2 : ResidueField O) ≠ 0 := by
    have hu := h2O.map (IsLocalRing.residue O)
    rw [map_ofNat] at hu
    exact hu.ne_zero
  have key : ∀ x : R, ∀ j : ZMod 2, j ≠ 0 → x ∈ evp σ j → res O R x = 0 := by
    intro x j hj hx
    have hj1 : j = 1 := (z2 j).resolve_left hj
    subst hj1
    have e : σ x = sg R 1 * x := hx
    rw [sg_one, neg_one_mul] at e
    apply zero_of_neg h2
    have hm := res_map σ x
    rw [e, map_neg] at hm
    exact hm.symm
  have hr : ∀ s, ((B.bar O).r s).mat ∈ adp (ResidueField O) 0 := by
    intro s
    show ∀ a b, pw a b ≠ 0 → ((B.bar O).r s).mat a b = 0
    intro a b hab
    rw [pw_eq] at hab
    have := key _ _ hab (hG.r s a b)
    simpa [Box.bar, Box.map, GG.mat, GG.map] using this
  refine ⟨hr, ?_, ?_⟩
  · intro v a b hab
    have := key _ _ (sub_ne_zero.mpr hab) (hG.g v a b)
    simpa [Box.bar, Box.map] using this
  · intro j s X hX
    rw [Submodule.mem_comap]
    simp only [Box.ad, adRep, GG.ad, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk, GG.adFun]
    apply conj_mem h2 _ (hr s) j
    split_ifs
    · exact hX
    · exact theta_mem j X hX
