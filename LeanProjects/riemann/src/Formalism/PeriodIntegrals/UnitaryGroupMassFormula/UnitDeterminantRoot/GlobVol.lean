import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.IdealPowPrincipal

noncomputable section
open scoped NumberField ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

section Vol

variable (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m]

lemma vol_smul_le {Λ Λ' : AddSubgroup (m → ℂ)} (c : ℂ) (h : ∀ x ∈ Λ, c • x ∈ Λ') :
    Submodule.span (𝓞 F) {c ^ Fintype.card m} * vol F Λ ≤ vol F Λ' := by
  unfold vol volSet
  rw [Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, _, ⟨v, hv, rfl⟩, rfl⟩
  obtain rfl := Set.mem_singleton_iff.mp hx
  apply Submodule.subset_span
  refine ⟨fun j => c • v j, fun j => h _ (hv j), ?_⟩
  rw [show (Matrix.of fun j => c • v j) = c • Matrix.of v from by ext i j; rfl, Matrix.det_smul]

lemma det_rows_map (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w : m → m → ℂ) :
    (Matrix.of fun j => δ (w j)).det = LinearMap.det δ * (Matrix.of w).det := by
  have h : Matrix.of (fun j => δ (w j)) = Matrix.of w * Matrix.transpose (LinearMap.toMatrix' δ) := by
    ext j i
    rw [Matrix.of_apply, ← LinearMap.toMatrix'_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [h, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix', mul_comm]

lemma vol_img (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)) :
    vol F (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ)
      = Submodule.span (𝓞 F) {LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))} * vol F Λ := by
  unfold UnitDetRootDefs.imgLat vol volSet
  rw [Submodule.span_mul_span]
  congr 1
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    choose w hw hwv using fun j => AddSubgroup.mem_map.mp (hv j)
    refine Set.mem_mul.mpr ⟨_, Set.mem_singleton _, _, ⟨w, hw, rfl⟩, ?_⟩
    have hv' : v = fun j => (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w j) := funext fun j => (hwv j).symm
    rw [hv', det_rows_map]
  · intro hz
    obtain ⟨_, h1, _, ⟨w, hw, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
    obtain rfl := Set.mem_singleton_iff.mp h1
    refine ⟨fun j => (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w j), fun j => AddSubgroup.mem_map.mpr ⟨w j, hw j, rfl⟩, ?_⟩
    rw [det_rows_map]

end Vol

def thetaO {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) : 𝓞 (KF b d) :=
  ⟨⟨UnitDetRootDefs.cmTheta b d, theta_mem b d⟩, by
    rw [mem_integralClosure_iff]
    refine ⟨Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X + Polynomial.C ((a : ℤ) * c), ?_, ?_⟩
    · monicity!
    · apply (KF b d).val.injective
      have h : ((KF b d).val.toRingHom) ((Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X +
          Polynomial.C ((a : ℤ) * c)).eval₂ (algebraMap ℤ (KF b d)) ⟨UnitDetRootDefs.cmTheta b d, theta_mem b d⟩)
          = (Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X +
          Polynomial.C ((a : ℤ) * c)).eval₂ (Int.castRingHom ℂ) (UnitDetRootDefs.cmTheta b d) := by
        rw [Polynomial.hom_eval₂, RingHom.ext_int ((KF b d).val.toRingHom.comp (algebraMap ℤ (KF b d)))
          (Int.castRingHom ℂ)]
        rfl
      change ((KF b d).val.toRingHom) _ = (KF b d).val 0
      rw [h, map_zero]
      rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X]
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
      linear_combination theta_sq hok⟩

lemma algebraMap_thetaO {a : ℕ} {b c : ℤ} {d : ℕ} (hok : UnitDetRootDefs.CmOK a b c d) :
    algebraMap (𝓞 (KF b d)) ℂ (thetaO hok) = UnitDetRootDefs.cmTheta b d := by
  rfl

lemma vol_std_le {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    (hok : UnitDetRootDefs.CmOK a b c d) {m : Type} [Fintype m] [DecidableEq m] :
    vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≤ Submodule.span (𝓞 (KF b d)) {lam ^ Fintype.card m} := by
  unfold vol volSet UnitDetRootDefs.stdLat
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  have h1 : ∀ j i, v j i ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice :=
    fun j i => (show ∀ i ∈ (Set.univ : Set m), v j i ∈ _ from hv j) i (Set.mem_univ i)
  clear hv
  have hent : ∀ j i, ∃ o : 𝓞 (KF b d), v j i = lam * algebraMap (𝓞 (KF b d)) ℂ o := by
    intro j i
    have h2 := h1 j i
    simp only [PeriodPair.lattice, UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair,
      UnitDetRootDefs.cmPair] at h2
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp h2
    refine ⟨p * (a : 𝓞 (KF b d)) + q * thetaO hok, ?_⟩
    rw [← hpq]
    simp only [map_add, map_mul, algebraMap_thetaO, map_intCast, map_natCast, zsmul_eq_mul]
    ring
  choose o ho using hent
  have hM : Matrix.of v = lam • (algebraMap (𝓞 (KF b d)) ℂ).mapMatrix (Matrix.of o) := by
    ext j i
    simp [ho j i]
  rw [hM, Matrix.det_smul, ← RingHom.map_det]
  refine Submodule.mem_span_singleton.mpr ⟨(Matrix.of o).det, ?_⟩
  rw [Algebra.smul_def, mul_comm]

lemma vol_std_ne_bot {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] :
    vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ ⊥ := by
  unfold vol volSet UnitDetRootDefs.stdLat
  rw [Submodule.ne_bot_iff]
  refine ⟨(Matrix.of fun (j i : m) => if i = j then lam * (a : ℂ) else 0).det,
    Submodule.subset_span ⟨_, fun j => ?_, rfl⟩, ?_⟩
  · refine fun i _ => ?_
    show (if i = j then lam * (a : ℂ) else 0) ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice
    have hω : lam * (a : ℂ) ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice := by
      simp only [PeriodPair.lattice, UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair,
        UnitDetRootDefs.cmPair]
      exact Submodule.subset_span (Set.mem_insert _ _)
    by_cases h : i = j
    · rw [if_pos h]
      exact hω
    · rw [if_neg h]
      exact zero_mem _
  · have hD : (Matrix.of fun (j i : m) => if i = j then lam * (a : ℂ) else 0) =
        Matrix.diagonal (fun _ => lam * (a : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, eq_comm]
    rw [hD, Matrix.det_diagonal, Finset.prod_const]
    exact pow_ne_zero _ (mul_ne_zero hlam (by exact_mod_cast ha.ne'))

end PI.UnitaryGroupMassFormula.UnitDetRoot
