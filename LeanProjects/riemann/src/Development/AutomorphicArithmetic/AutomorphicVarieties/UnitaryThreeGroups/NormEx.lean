import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MatGstar

open Matrix UpperTheory.V.U3

section SlopeTestRemainingChoices

open IsLocalRing

variable {R : Type} [CommRing R]

private theorem quad_root [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (a b c : R)
    (hb : IsUnit b) (hc : residue R c = 0) : ∃ x, residue R x = 0 ∧ a * x ^ 2 + b * x + c = 0 := by
  have hcm : c ∈ maximalIdeal R := (residue_eq_zero_iff c).1 hc
  have hH : HenselianRing R (maximalIdeal R) := inferInstance
  obtain ⟨w, hw, hw'⟩ := hH.is_henselian
    (Polynomial.X ^ 2 + (Polynomial.C b * Polynomial.X + Polynomial.C (a * c)))
    (Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num))) (-b)
    (by
      have : Polynomial.eval (-b) (Polynomial.X ^ 2 + (Polynomial.C b * Polynomial.X +
          Polynomial.C (a * c))) = a * c := by simp; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hcm)
    (by
      have : Polynomial.eval (-b) (Polynomial.derivative (Polynomial.X ^ 2 +
          (Polynomial.C b * Polynomial.X + Polynomial.C (a * c)))) = -b := by simp; ring
      rw [this]; exact hb.neg.map _)
  have hw0 : w ^ 2 + (b * w + a * c) = 0 := by simpa using hw
  have hwu : IsUnit w := by
    by_contra hn
    have h1 : w ∈ maximalIdeal R := hn
    have h2 : b ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hw' h1
      simpa using this
    exact h2 hb
  obtain ⟨k, hk⟩ := hwu.exists_right_inv
  refine ⟨c * k, by simp [hc], ?_⟩
  linear_combination c * k ^ 2 * hw0 - (c * (w * k + 1) + b * c * k) * hk

private theorem unit_of_res [IsLocalRing R] {x : R} (h : IsUnit (residue R x)) : IsUnit x :=
  (residue_ne_zero_iff_isUnit x).1 h.ne_zero

private theorem stageA (s q p u t v w : R) (hw : w ^ 2 * u = 1) :
    !![1, -q * w ^ 2, 0; 0, w, 0; 0, -t * w ^ 2, 1] * !![s, q, p; q, u, t; p, t, v] *
      (!![1, -q * w ^ 2, 0; 0, w, 0; 0, -t * w ^ 2, 1])ᵀ =
    !![s - q ^ 2 * w ^ 2, 0, p - q * t * w ^ 2; 0, 1, 0; p - q * t * w ^ 2, 0, v - t ^ 2 * w ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private theorem stageB (s p v x k e : R) (hx : v * x ^ 2 + 2 * p * x + s = 0)
    (hk : (p + x * v) * k = 1) (he : 2 * e = 1) :
    !![1, 0, x; 0, 1, 0; -k * (v * k * e), 0, k * (1 - v * k * e * x)] * !![s, 0, p; 0, 1, 0; p, 0, v] *
      (!![1, 0, x; 0, 1, 0; -k * (v * k * e), 0, k * (1 - v * k * e * x)])ᵀ = Jmat R 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev] <;> grind

private theorem symm_norm [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (h2 : IsUnit (2 : R))
    (S : Matrix (Fin 3) (Fin 3) R) (hS : Sᵀ = S) (hr : S.map (residue R) = Jmat _ 3) :
    ∃ h : Matrix (Fin 3) (Fin 3) R, h.map (residue R) = 1 ∧ h * S * hᵀ = Jmat R 3 := by
  have hsy : ∀ i j, S j i = S i j := fun i j => congrFun (congrFun hS i) j
  have hre : ∀ i j, residue R (S i j) = Jmat _ 3 i j := fun i j => congrFun (congrFun hr i) j
  obtain ⟨s, q, p, u, t, v, rfl⟩ : ∃ s q p u t v, S = !![s, q, p; q, u, t; p, t, v] := by
    refine ⟨S 0 0, S 0 1, S 0 2, S 1 1, S 1 2, S 2 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> exact hsy _ _
  have hs : residue R s = 0 := by simpa [Jmat, Fin.rev] using hre 0 0
  have hq : residue R q = 0 := by simpa [Jmat, Fin.rev] using hre 0 1
  have hp : residue R p = 1 := by simpa [Jmat, Fin.rev] using hre 0 2
  have hu : residue R u = 1 := by simpa [Jmat, Fin.rev] using hre 1 1
  have ht : residue R t = 0 := by simpa [Jmat, Fin.rev] using hre 1 2
  have hv : residue R v = 0 := by simpa [Jmat, Fin.rev] using hre 2 2
  have huu : IsUnit u := unit_of_res (by rw [hu]; exact isUnit_one)
  obtain ⟨e, he⟩ := h2.exists_right_inv
  obtain ⟨y, hy0, hy⟩ := quad_root u (2 * u) (u - 1) (h2.mul huu) (by simp [hu])
  have hw : (1 + y) ^ 2 * u = 1 := by linear_combination hy
  have hw1 : residue R (1 + y) = 1 := by simp [hy0]
  generalize 1 + y = w at hw hw1
  have hA := stageA s q p u t v w hw
  obtain ⟨x, hx0, hx⟩ := quad_root (v - t ^ 2 * w ^ 2) (2 * (p - q * t * w ^ 2)) (s - q ^ 2 * w ^ 2)
    (h2.mul (unit_of_res (by simp [hp, hq]))) (by simp [hs, hq])
  obtain ⟨k, hk⟩ := (unit_of_res (x := (p - q * t * w ^ 2) + x * (v - t ^ 2 * w ^ 2))
    (by simp [hp, hq, hx0])).exists_right_inv
  have hk1 : residue R k = 1 := by simpa [hp, hq, hx0] using congrArg (residue R) hk
  have hB := stageB _ _ _ x k e hx hk he
  refine ⟨_ * _, ?_, by rw [← hB, ← hA, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]; rfl⟩
  rw [Matrix.map_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hq, ht, hv, hw1, hx0, hk1]

private theorem anti_norm [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (h2 : IsUnit (2 : R))
    (a b d : R) (ha : IsUnit a) (hb : residue R b = 0) (hd : residue R d = 0) :
    ∃ h : Matrix (Fin 3) (Fin 3) R, h.map (residue R) = 1 ∧ h * (Jmat R 3 * hᵀ * Jmat R 3) = 1 ∧
      (h * !![a, b, 0; d, 0, -b; 0, -d, -a] * (Jmat R 3 * hᵀ * Jmat R 3)) 0 1 = 0 ∧
      (h * !![a, b, 0; d, 0, -b; 0, -d, -a] * (Jmat R 3 * hᵀ * Jmat R 3)) 1 0 = 0 := by
  obtain ⟨e, he⟩ := h2.exists_right_inv
  obtain ⟨y, hy0, hy⟩ := quad_root (-b * e) a d ha hd
  obtain ⟨k, hk⟩ := (unit_of_res (x := a - b * y) (by simpa [hb] using ha.map (residue R))).exists_right_inv
  obtain ⟨x, hx0, hx⟩ : ∃ x, residue R x = 0 ∧ x * (a - b * y) = b :=
    ⟨b * k, by simp [hb], by linear_combination b * hk⟩
  clear hk
  refine ⟨!![1, x, -x ^ 2 * e; 0, 1, -x; 0, 0, 1] * !![1, 0, 0; y, 1, 0; -y ^ 2 * e, -y, 1], ?_, ?_, ?_, ?_⟩
  · rw [Matrix.map_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hx0, hy0]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev] <;> grind
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]; grind
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]; grind

private theorem conj_left {G : Type} [Group G] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G) :
    (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ := by
  simp [conjBy, SemidirectProduct.mul_left, SemidirectProduct.inv_left]

private theorem conj_right {G : Type} [Group G] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G) :
    (conjBy h r g).right = (r g).right := by
  simp [conjBy]

private theorem conj_mat_one {G : Type} [Group G] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G)
    (hg : (r g).right = 1) :
    (conjBy h r g).mat = (h : Matrix _ _ R) * (r g).mat * ((h⁻¹ : GL (Fin m) R) : Matrix _ _ R) := by
  simp only [GG.mat, conj_left, hg, sgnAct_one, Units.val_mul]

private theorem conj_mat_neg {G : Type} [Group G] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G)
    (hg : (r g).right = -1) :
    (conjBy h r g).mat = (h : Matrix _ _ R) * (r g).mat *
      (Jmat R m * (h : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m) := by
  simp only [GG.mat, conj_left, hg, sgnAct_neg_one, Units.val_mul, theta_val, inv_inv]

private theorem conj_conj {G : Type} [Group G] {m : ℕ} (h h' : GL (Fin m) R) (r : G →* GG m R) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  ext1 g
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    _root_.mul_inv_rev, mul_assoc, MulAut.mul_apply]

private theorem sym_of_sq {m : ℕ} (x : GG m R) (hx : x * x = 1) (hr : x.right = -1) :
    (x.mat * Jmat R m)ᵀ = x.mat * Jmat R m := by
  have h1 : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left hx
    simpa [hr] using this
  have h2 : x.left = (theta x.left)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : x.mat = Jmat R m * x.matᵀ * Jmat R m := by
    unfold GG.mat
    rw [← theta_inv_val, ← h2]
  rw [Matrix.transpose_mul, Jmat_transpose]
  conv_rhs => rw [h3, Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]

private theorem anti_shape (M : Matrix (Fin 3) (Fin 3) R) :
    M - Jmat R 3 * Mᵀ * Jmat R 3 = !![M 0 0 - M 2 2, M 0 1 - M 1 2, 0; M 1 0 - M 2 1, 0, -(M 0 1 - M 1 2);
      0, -(M 1 0 - M 2 1), -(M 0 0 - M 2 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

end SlopeTestRemainingChoices

theorem UpperTheory.V.U3.exists_normalised :
    ∀ {G R : Type} [Group G] [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      (η : G →* ℤˣ) (Ψ : G →* (IsLocalRing.ResidueField R)ˣ) (c g₁ : G) (r : G →* GG 3 R), IsUnit (2 : R) → Marks η Ψ c g₁ →
      (GG.map (IsLocalRing.residue R)).comp r = r0 η Ψ →
    ∃ h : GL (Fin 3) R, CongOne (IsLocalRing.maximalIdeal R) h ∧ Normalised c g₁ (conjBy h r) := by
  intro G R _ _ _ _ η Ψ c g₁ r h2 hM hr
  have hr' : ∀ g, GG.map (IsLocalRing.residue R) (r g) = r0 η Ψ g := fun g => DFunLike.congr_fun hr g
  have hright : ∀ g, (r g).right = η g := fun g => congrArg SemidirectProduct.right (hr' g)
  have hmat : ∀ g, (r g).mat.map (IsLocalRing.residue R) = (tor _ (Ψ g) : Matrix (Fin 3) (Fin 3) _) :=
    fun g => congrArg GG.mat (hr' g)
  have hc : (r c).right = -1 := (hright c).trans hM.ηc
  have hg : (r g₁).right = 1 := (hright g₁).trans hM.ηg
  obtain ⟨H₁, hH₁, hH₁'⟩ := symm_norm h2 ((r c).mat * Jmat R 3)
    (sym_of_sq _ (by rw [← map_mul, hM.csq, map_one]) hc)
    (by rw [Matrix.map_mul, hmat, hM.Ψc, Jmat_map]; simp)
  have e1 : H₁ * (r c).mat * (Jmat R 3 * H₁ᵀ * Jmat R 3) = 1 := by
    rw [← Jmat_mul_Jmat (R := R) 3]
    conv_rhs => rw [← hH₁']
    conv_rhs => enter [2]; rw [hH₁']
    simp only [Matrix.mul_assoc]
  obtain ⟨h₁, rfl⟩ : IsUnit H₁ :=
    IsUnit.of_mul_eq_one _ ((Matrix.mul_assoc _ _ _).symm.trans e1)
  have hi : ((h₁⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map (IsLocalRing.residue R) = 1 := by
    have := congrArg (fun X : Matrix (Fin 3) (Fin 3) R => X.map (IsLocalRing.residue R)) h₁.mul_inv
    simp only [Matrix.map_mul, hH₁, Matrix.one_mul] at this
    simpa using this
  have hc1 : (conjBy h₁ r c).right = -1 := (conj_right _ _ _).trans hc
  have hg1 : (conjBy h₁ r g₁).right = 1 := (conj_right _ _ _).trans hg
  have hcm : (conjBy h₁ r c).mat = 1 := (conj_mat_neg _ _ _ hc).trans e1
  have hgm : (conjBy h₁ r g₁).mat.map (IsLocalRing.residue R) =
      (tor _ (Ψ g₁) : Matrix (Fin 3) (Fin 3) _) := by
    rw [conj_mat_one _ _ _ hg, Matrix.map_mul, Matrix.map_mul, hH₁, hi, hmat]; simp
  obtain ⟨hs, hs'⟩ := mat_gstar (conjBy h₁ r) c g₁ hcm hc1 hg1
  have hcc := fun h => conj_conj h h₁ r
  generalize conjBy h₁ r = r₁ at hc1 hg1 hcm hgm hs hs' hcc
  have hent : ∀ i j, IsLocalRing.residue R ((r₁ g₁).mat i j) = _ := fun i j => congrFun (congrFun hgm i) j
  obtain ⟨H₂, hH₂, e2, z1, z2⟩ := anti_norm h2 ((r₁ g₁).mat 0 0 - (r₁ g₁).mat 2 2)
    ((r₁ g₁).mat 0 1 - (r₁ g₁).mat 1 2) ((r₁ g₁).mat 1 0 - (r₁ g₁).mat 2 1)
    (unit_of_res (by
      have := hM.Ψg.mul (Ψ g₁)⁻¹.isUnit
      rw [map_sub, hent, hent]
      convert this using 1
      simp [tor_val, wt1, sub_mul, pow_two]))
    (by rw [map_sub, hent, hent]; simp [tor_val]) (by rw [map_sub, hent, hent]; simp [tor_val])
  obtain ⟨h₂, rfl⟩ : IsUnit H₂ := IsUnit.of_mul_eq_one _ e2
  have hinv : ((h₂⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      Jmat R 3 * (h₂ : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 := Units.inv_eq_of_mul_eq_one_right e2
  have hz : zmat c g₁ (conjBy h₂ r₁) = (h₂ : Matrix (Fin 3) (Fin 3) R) *
      ((r₁ g₁).mat - Jmat R 3 * (r₁ g₁).matᵀ * Jmat R 3) *
      (Jmat R 3 * (h₂ : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3) := by
    rw [zmat, conj_mat_one _ _ _ hg1, conj_mat_one _ _ _ hs', hs, hinv, Matrix.mul_sub, Matrix.sub_mul]
  rw [anti_shape] at hz
  refine ⟨h₂ * h₁, ?_, ?_⟩
  · intro a b
    rw [← IsLocalRing.residue_eq_zero_iff]
    have : ((h₂ * h₁ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map (IsLocalRing.residue R) = 1 := by
      rw [Units.val_mul, Matrix.map_mul, hH₁, hH₂, Matrix.one_mul]
    have h' := congrFun (congrFun this a) b
    rw [Matrix.map_apply] at h'
    rw [Matrix.sub_apply, map_sub, h']
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · rw [hcc]
    exact ⟨by rw [conj_mat_neg _ _ _ hc1, hcm, Matrix.mul_one, e2], hz ▸ z1, hz ▸ z2⟩
