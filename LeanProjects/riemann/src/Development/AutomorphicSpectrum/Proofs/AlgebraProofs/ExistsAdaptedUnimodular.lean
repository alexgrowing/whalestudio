import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.ToricBasis

private theorem transpose_mul_mul_apply_eq_dot_product_mul_vec {m n R : Type*} [Fintype m]
    [CommSemiring R] (P : Matrix m n R) (A : Matrix m m R) (x y : n) :
    (Pᵀ * A * P) x y = Pᵀ x ⬝ᵥ A *ᵥ Pᵀ y := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem exists_isCompl_ker {g : ℕ} (f : (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    ∃ M : Submodule ℤ (Fin g → ℤ), IsCompl M (LinearMap.ker f) := by
  haveI : Module.Free ℤ (LinearMap.range f) := Module.free_of_finite_type_torsion_free'
  obtain ⟨t, ht⟩ :=
    LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  have hft : ∀ y : LinearMap.range f, f (t y) = y := fun y =>
    congrArg Subtype.val (LinearMap.congr_fun ht y)
  refine ⟨LinearMap.range t, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x ⟨y, rfl⟩ hy
    rw [LinearMap.mem_ker] at hy
    have hy0 : y = 0 := Subtype.ext ((hft y).symm.trans hy)
    rw [hy0, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨t (f.rangeRestrict x), LinearMap.mem_range_self _ _, x - t (f.rangeRestrict x), ?_,
      by abel⟩
    rw [LinearMap.mem_ker, map_sub, hft, sub_eq_zero]
    rfl

theorem exists_adapted_basis {g : ℕ} (f : (Fin g → ℤ) →ₗ[ℤ] (Fin g → ℤ)) :
    ∃ (r s : ℕ) (b : Module.Basis (Fin r ⊕ Fin s) ℤ (Fin g → ℤ)),
      (∀ k, f (b (Sum.inr k)) = 0) ∧
      ∀ x : Fin r → ℤ, f (∑ a, x a • b (Sum.inl a)) = 0 → x = 0 := by
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.ToricBasis.exists_isCompl_ker f
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free ℤ (LinearMap.ker f) := Module.free_of_finite_type_torsion_free'
  obtain ⟨bM⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ M)) ℤ M) :=
    ⟨Module.finBasis ℤ M⟩
  obtain ⟨bK⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℤ (LinearMap.ker f))) ℤ
      (LinearMap.ker f)) := ⟨Module.finBasis ℤ (LinearMap.ker f)⟩
  have hb : ∀ i, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM) i =
      ((bM.prod bK i).1 : Fin g → ℤ) + ((bM.prod bK i).2 : Fin g → ℤ) := fun i => by
    rw [Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨_, _, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM), ?_, ?_⟩
  · intro k
    rw [hb, Module.Basis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply, ZeroMemClass.coe_zero,
      zero_add]
    exact LinearMap.mem_ker.mp (bK k).2
  · intro x hx
    have hinl : ∀ a, (bM.prod bK).map (Submodule.prodEquivOfIsCompl M (LinearMap.ker f) hM)
        (Sum.inl a) = (bM a : Fin g → ℤ) := fun a => by
      rw [hb, Module.Basis.prod_apply]
      simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply, ZeroMemClass.coe_zero,
        add_zero]
    simp only [hinl] at hx
    have hmem : (∑ a, x a • (bM a : Fin g → ℤ)) ∈ M :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (bM a).2
    have h0 := Submodule.disjoint_def.mp hM.disjoint _ hmem (LinearMap.mem_ker.mpr hx)
    have h0' : ∑ a, x a • bM a = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa only [Submodule.coe_smul, ZeroMemClass.coe_zero] using h0
    funext a
    exact Fintype.linearIndependent_iff.mp bM.linearIndependent x h0' a

theorem cast_quad {g : ℕ} (A : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    star (fun i => (v i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (v i : ℝ))
      = ((v ⬝ᵥ A *ᵥ v : ℤ) : ℝ) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial,
    Int.cast_sum, Int.cast_mul]

theorem quad_nonneg {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) : 0 ≤ v ⬝ᵥ A *ᵥ v := by
  have h := hA.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
  rw [GlobalTheory.CompanionTheory.ToricBasis.cast_quad] at h
  exact_mod_cast h

theorem mulVec_eq_zero_of_quad {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) (h : v ⬝ᵥ A *ᵥ v = 0) :
    A *ᵥ v = 0 := by
  have h1 : star (fun i => (v i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ
      (fun i => (v i : ℝ)) = 0 := by
    rw [GlobalTheory.CompanionTheory.ToricBasis.cast_quad, h, Int.cast_zero]
  have h2 := (hA.dotProduct_mulVec_zero_iff _).mp h1
  funext i
  have h3 := congrFun h2 i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h3 ⊢
  exact_mod_cast h3

theorem symm_of_posSemidef {g : ℕ} {A : Matrix (Fin g) (Fin g) ℤ}
    (hA : (A.map (fun x : ℤ => (x : ℝ))).PosSemidef) : Aᵀ = A := by
  ext i j
  have h := hA.isHermitian.apply i j
  simp only [Matrix.map_apply, star_trivial] at h
  rw [Matrix.transpose_apply]
  exact_mod_cast h

theorem exists_adapted_unimodular :
    ∀ (g : ℕ) (J : Type) [Fintype J] (B : J → Matrix (Fin g) (Fin g) ℤ), (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → ∃ (r s : ℕ) (e : Fin r ⊕ Fin s ≃ Fin g) (Q : Matrix (Fin g) (Fin g) ℤ), IsUnit Q.det ∧ (∀ j k l, ((Qᵀ * B j * Q).submatrix e e) (Sum.inr k) l = 0 ∧ ((Qᵀ * B j * Q).submatrix e e) l (Sum.inr k) = 0) ∧ ((((Qᵀ * (∑ j, B j) * Q).submatrix e e).toBlocks₁₁).map (fun x : ℤ => (x : ℝ))).PosDef := by
  intro g J _ B hB
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin g) (Fin g) ℤ, S = ∑ j, B j := ⟨_, rfl⟩
  rw [← hSdef]
  have hSpsd : (S.map (fun x : ℤ => (x : ℝ))).PosSemidef := by
    have hmap : S.map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
      ext i i'
      simp only [hSdef, Matrix.map_apply, Matrix.sum_apply, Int.cast_sum]
    rw [hmap]
    exact Matrix.posSemidef_sum Finset.univ fun j _ => hB j
  obtain ⟨r, s, b, hker, hinj⟩ := GlobalTheory.CompanionTheory.ToricBasis.exists_adapted_basis (Matrix.mulVecLin S)
  have hcard : g = r + s := by
    have h := Module.finrank_eq_card_basis b
    rwa [Module.finrank_fin_fun ℤ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  obtain ⟨e⟩ : Nonempty (Fin r ⊕ Fin s ≃ Fin g) := ⟨finSumFinEquiv.trans (finCongr hcard.symm)⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin g) (Fin g) ℤ,
      Q = (Pi.basisFun ℤ (Fin g)).toMatrix (b.reindex e) := ⟨_, rfl⟩
  have hQ : ∀ i m, Q i m = b (e.symm m) i := by
    intro i m
    rw [hQdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply]
  have hunit : IsUnit Q.det := by
    rw [hQdef]
    letI := Module.Basis.invertibleToMatrix (Pi.basisFun ℤ (Fin g)) (b.reindex e)
    exact Matrix.isUnit_det_of_invertible _
  have hcol : ∀ α, Qᵀ (e α) = b α := fun α => funext fun i => by
    rw [Matrix.transpose_apply, hQ, e.symm_apply_apply]
  have hentry : ∀ (X : Matrix (Fin g) (Fin g) ℤ) (α β : Fin r ⊕ Fin s),
      ((Qᵀ * X * Q).submatrix e e) α β = b α ⬝ᵥ X *ᵥ b β := by
    intro X α β
    rw [Matrix.submatrix_apply, transpose_mul_mul_apply_eq_dot_product_mul_vec, hcol, hcol]
  have hBk : ∀ j k, B j *ᵥ b (Sum.inr k) = 0 := by
    intro j k
    have hSk : S *ᵥ b (Sum.inr k) = 0 := by
      have h := hker k
      rwa [Matrix.mulVecLin_apply] at h
    have hsum : ∑ i, b (Sum.inr k) ⬝ᵥ B i *ᵥ b (Sum.inr k) = 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, ← hSdef, hSk, dotProduct_zero]
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      GlobalTheory.CompanionTheory.ToricBasis.quad_nonneg (hB i) _)).mp hsum j
        (Finset.mem_univ _)
    exact GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad (hB j) _ hj
  refine ⟨r, s, e, Q, hunit, ?_, ?_⟩
  · intro j k l
    refine ⟨?_, ?_⟩
    · rw [hentry, Matrix.dotProduct_mulVec,
        ← GlobalTheory.CompanionTheory.ToricBasis.symm_of_posSemidef (hB j), Matrix.vecMul_transpose, hBk,
        zero_dotProduct]
    · rw [hentry, hBk, dotProduct_zero]
  · obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin g) (Fin r) ℤ, ∀ i a, C i a = b (Sum.inl a) i :=
      ⟨Matrix.of fun i a => b (Sum.inl a) i, fun _ _ => rfl⟩
    have hCt : ∀ a, Cᵀ a = b (Sum.inl a) := fun a => funext fun i => by
      rw [Matrix.transpose_apply, hC]
    have hMC : ((Qᵀ * S * Q).submatrix e e).toBlocks₁₁ = Cᵀ * S * C := by
      ext a a'
      rw [transpose_mul_mul_apply_eq_dot_product_mul_vec, hCt, hCt, ← hentry]
      rfl
    rw [hMC]
    have hN : (Cᵀ * S * C).map (fun x : ℤ => (x : ℝ)) =
        (C.map (fun x : ℤ => (x : ℝ)))ᴴ * S.map (fun x : ℤ => (x : ℝ)) *
          C.map (fun x : ℤ => (x : ℝ)) := by
      ext a a'
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.transpose_apply, star_trivial, Int.cast_sum, Int.cast_mul]
    have hNpsd : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).PosSemidef := by
      rw [hN]
      exact hSpsd.conjTranspose_mul_mul_same _
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hNpsd.isHermitian ?_
    intro x hx
    refine lt_of_le_of_ne (hNpsd.dotProduct_mulVec_nonneg x) fun h0 => ?_
    have hNx := (hNpsd.dotProduct_mulVec_zero_iff x).mp h0.symm
    have hdetN : ((Cᵀ * S * C).map (fun x : ℤ => (x : ℝ))).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hNx⟩
    have hdetZ : (Cᵀ * S * C).det = 0 := by
      have h1 : (((Cᵀ * S * C).det : ℤ) : ℝ) = 0 := by
        rw [← hdetN]
        have h2 := RingHom.map_det (Int.castRingHom ℝ) (Cᵀ * S * C)
        rw [RingHom.mapMatrix_apply] at h2
        exact h2
      exact_mod_cast h1
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetZ
    have hquad : (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v) = 0 := by
      have h3 : v ⬝ᵥ (Cᵀ * S * C) *ᵥ v = (C *ᵥ v) ⬝ᵥ S *ᵥ (C *ᵥ v) := by
        rw [← Matrix.mulVec_mulVec v (Cᵀ * S) C, ← Matrix.mulVec_mulVec (C *ᵥ v) Cᵀ S,
          Matrix.dotProduct_mulVec v Cᵀ, Matrix.vecMul_transpose C v]
      rw [← h3, hv0, dotProduct_zero]
    have hSw := GlobalTheory.CompanionTheory.ToricBasis.mulVec_eq_zero_of_quad hSpsd
      (C *ᵥ v) hquad
    have hCv : C *ᵥ v = ∑ a, v a • b (Sum.inl a) := by
      ext i
      rw [Finset.sum_apply]
      simp only [Matrix.mulVec, dotProduct, hC, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    exact hv (hinj v (by rw [Matrix.mulVecLin_apply, ← hCv]; exact hSw))

end GlobalTheory.CompanionTheory.ToricBasis
