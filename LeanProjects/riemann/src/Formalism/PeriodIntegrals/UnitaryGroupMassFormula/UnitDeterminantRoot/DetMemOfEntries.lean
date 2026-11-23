import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NsmulRelIdxMem

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

lemma det_mem_of_entries {m : Type} [Fintype m] [DecidableEq m] {S : IntermediateField ℚ ℂ}
    (U : Matrix m m ℂ) (h : ∀ i j, U i j ∈ S) : U.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

lemma theta_mem (b : ℤ) (d : ℕ) : UnitDetRootDefs.cmTheta b d ∈ KF b d :=
    IntermediateField.mem_adjoin_simple_self ℚ (UnitDetRootDefs.cmTheta b d)

lemma single_mem_stdLat {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [DecidableEq m] (j : m) :
    Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m := by
  rw [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]
  intro i _
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same]
    exact (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁_mem_lattice
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

lemma entries_mem {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {Λa : AddSubgroup (m → ℂ)}
    (hH : Hyp a b c d ha hd lam hlam m Λa) {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)} (hA : admitted a b d ha hd lam hlam m Λa δ)
    (i j : m) : LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) i j ∈ KF b d := by
  have he : Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m :=
    single_mem_stdLat j
  obtain ⟨n1, hn1, -, h1⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hH.2.2.2.2 he
  have h2 : (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (n1 • Pi.single j (lam * a)) ∈
      UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa :=
    AddSubgroup.mem_map_of_mem _ h1.1
  obtain ⟨n2, hn2, -, h3⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hA.2.1 h2
  have h4 := (AddSubgroup.mem_inf.mp h3).1
  rw [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi] at h4
  have h5 := h4 i (Set.mem_univ _)
  rw [Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice] at h5
  obtain ⟨p, q, hpq⟩ := h5
  have hs : Pi.single j (lam * (a : ℂ)) = (lam * (a : ℂ)) • Pi.single j (1 : ℂ) := by
    ext k
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hs, map_nsmul, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    nsmul_eq_mul, nsmul_eq_mul] at hpq
  change (p : ℂ) * (lam * a) + q * (lam * UnitDetRootDefs.cmTheta b d) = _ at hpq
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hN : (n2 : ℂ) * n1 * a ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hn2.ne') (by exact_mod_cast hn1.ne')) ha0
  have hM : LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) i j =
      ((p : ℂ) * a + q * UnitDetRootDefs.cmTheta b d) / ((n2 : ℂ) * n1 * a) := by
    rw [LinearMap.toMatrix'_apply, eq_div_iff hN]
    apply mul_left_cancel₀ hlam
    simp only [LinearEquiv.coe_coe] at hpq ⊢
    linear_combination -hpq
  rw [hM]
  exact div_mem (add_mem (mul_mem (intCast_mem _ _) (natCast_mem _ _))
    (mul_mem (intCast_mem _ _) (theta_mem b d)))
    (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) (natCast_mem _ _))

private lemma stdH_apply_lemma (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (z w : m → ℂ) :
    UnitDetRootDefs.stdH L m z w = ((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ * ∑ i, z i * conj (w i) := by
  simp only [UnitDetRootDefs.stdH, UnitDetRootDefs.matH, LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro j _ hji
    rw [if_neg (Ne.symm hji)]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma unitary_det {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)}
    (hiso : UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
      (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) :
    LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) * conj (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))) = 1 := by
  have hA0 : ((UnitDetRootDefs.area (UnitDetRootDefs.cmL a b d ha hd lam hlam) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, UnitDetRootDefs.area, abs_ne_zero]
    change (conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d)).im ≠ 0
    have e : conj (lam * (a : ℂ)) * (lam * UnitDetRootDefs.cmTheta b d) =
        ((Complex.normSq lam * a : ℝ) : ℂ) * UnitDetRootDefs.cmTheta b d := by
      rw [map_mul, Complex.conj_natCast]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    rw [e, Complex.im_ofReal_mul]
    have hθ : (UnitDetRootDefs.cmTheta b d).im = Real.sqrt d / 2 := by
      simp [UnitDetRootDefs.cmTheta]
    rw [hθ]
    have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
    have h2 : (0 : ℝ) < a := by exact_mod_cast ha
    have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    exact (mul_pos (mul_pos h1 h2) (by positivity)).ne'
  have hU : (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).transpose *
      (LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))).map (starRingEnd ℂ) = 1 := by
    ext k l
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix'_apply]
    have h := hiso (Pi.single k 1) (Pi.single l 1)
    rw [stdH_apply_lemma, stdH_apply_lemma] at h
    rw [mul_left_cancel₀ (inv_ne_zero hA0) h]
    rw [Finset.sum_eq_single k (fun i _ hik => by rw [Pi.single_eq_of_ne hik, zero_mul])
      (fun hk => absurd (Finset.mem_univ k) hk), Pi.single_eq_same, one_mul, Pi.single_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hd' := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd'
  rw [← LinearMap.det_toMatrix', RingHom.map_det, RingHom.mapMatrix_apply]
  exact hd'

theorem detInK : DetInK := by
  intro a b c d ha hd lam hlam m _ _ Λa hH δ hA
  refine ⟨?_, unitary_det hA.1⟩
  rw [← LinearMap.det_toMatrix']
  exact det_mem_of_entries _ (entries_mem hH hA)

end PI.UnitaryGroupMassFormula.UnitDetRoot
