import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

section BlockTri

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (Q : ι → Prop) [DecidablePred Q]

private def LowZero (M : Matrix ι ι R) : Prop := ∀ j, ¬ Q j → ∀ i, Q i → M j i = 0

private theorem lowZero_mul {A B : Matrix ι ι R} (hA : LowZero Q A) (hB : LowZero Q B) :
    LowZero Q (A * B) := by
  intro j hj i hi
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : Q k
  · rw [hA j hj k hk, zero_mul]
  · rw [hB k hk i hi, mul_zero]

private theorem toSq_mul {A B : Matrix ι ι R} (hB : LowZero Q B) :
    (A * B).toSquareBlockProp Q = A.toSquareBlockProp Q * B.toSquareBlockProp Q := by
  ext ⟨i, hi⟩ ⟨l, hl⟩
  change (A * B) i l = ∑ k : {x // Q x}, A i k * B k l
  rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype Q]
  have h0 : ∑ k : {x // ¬ Q x}, A i k * B k l = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hB k k.2 l hl, mul_zero]
  rw [h0, add_zero]

private theorem charpoly_toSq_dvd {M : Matrix ι ι R} (hM : LowZero Q M) :
    (M.toSquareBlockProp Q).charpoly ∣ M.charpoly := by
  have hz : ∀ i, ¬ Q i → ∀ j, Q j → M.charmatrix i j = 0 := by
    intro i hi j hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Matrix.charmatrix_apply_ne M i j hij, hM i hi j hj]
    simp
  have hsq : (M.charmatrix).toSquareBlockProp Q = (M.toSquareBlockProp Q).charmatrix := by
    ext1 ⟨i, hi⟩ ⟨j, hj⟩
    by_cases hij : i = j
    · subst hij
      change M.charmatrix i i = (M.toSquareBlockProp Q).charmatrix ⟨i, hi⟩ ⟨i, hi⟩
      rw [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_eq]
      rfl
    · have hne : (⟨i, hi⟩ : {x // Q x}) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
      change M.charmatrix i j = (M.toSquareBlockProp Q).charmatrix ⟨i, hi⟩ ⟨j, hj⟩
      rw [Matrix.charmatrix_apply_ne M i j hij, Matrix.charmatrix_apply_ne _ _ _ hne]
      rfl
  have h := Matrix.twoBlockTriangular_det (M.charmatrix) Q hz
  rw [hsq] at h
  exact ⟨_, h⟩

end BlockTri

theorem UpperTheory.exists_lower_entry_ne_zero_of_norm_charpoly_irreducible :
    ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
          (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (δ : GL (Fin n) E) (p : F[X]), Irreducible p →
          p.map (algebraMap F E) = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly →
          ∀ r : ℕ, 0 < r → r < n → ∃ i j : Fin n, (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (δ : Matrix (Fin n) (Fin n) E) j i ≠ 0 := by
  intro F E _ _ _ _ _ σ hgen n δ p hp hpc r hr0 hrn
  by_contra hcon
  push_neg at hcon
  let Q : Fin n → Prop := fun i => (i : ℕ) < r
  have hL : LowZero Q (δ : Matrix (Fin n) (Fin n) E) :=
    fun j hj i hi => hcon i j hi (not_lt.mp hj)
  have hdet : ((δ : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q).det ≠ 0 := by
    intro h0
    have h := Matrix.twoBlockTriangular_det (δ : Matrix (Fin n) (Fin n) E) Q hL
    rw [h0, zero_mul] at h
    have hu : IsUnit (δ : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp δ.isUnit
    exact hu.ne_zero h
  let δ₁ : GL {i // Q i} E := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hδ₁ : (δ₁ : Matrix {i // Q i} {i // Q i} E) =
      (δ : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q := rfl
  have key : ∀ m : ℕ,
      LowZero Q ((twNorm (sigmaGL σ) m δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∧
      ((twNorm (sigmaGL σ) m δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).toSquareBlockProp Q =
        ((twNorm (sigmaGL σ) m δ₁ : GL {i // Q i} E) : Matrix {i // Q i} {i // Q i} E) := by
    intro m
    induction m with
    | zero =>
      constructor
      · intro j hj i hi
        have hij : j ≠ i := fun h => hj (h ▸ hi)
        simp [hij]
      · ext ⟨i, hi⟩ ⟨l, hl⟩
        simp [Matrix.toSquareBlockProp, Matrix.one_apply]
    | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hpow : ((((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) δ : GL (Fin n) E) :
          Matrix (Fin n) (Fin n) E) = (δ : Matrix (Fin n) (Fin n) E).map (σ ^ m) := by
        rw [← sigmaGL_pow, sigmaGL_val]
      have hpow₁ : ((((sigmaGL σ : Monoid.End (GL {i // Q i} E)) ^ m) δ₁ : GL {i // Q i} E) :
          Matrix {i // Q i} {i // Q i} E) =
            (δ₁ : Matrix {i // Q i} {i // Q i} E).map (σ ^ m) := by
        rw [← sigmaGL_pow, sigmaGL_val]
      have hLm : LowZero Q ((δ : Matrix (Fin n) (Fin n) E).map (σ ^ m)) := by
        intro j hj i hi
        simp [hL j hj i hi]
      rw [twNorm_succ, twNorm_succ, Units.val_mul, Units.val_mul, hpow, hpow₁]
      refine ⟨lowZero_mul Q ih1 hLm, ?_⟩
      rw [toSq_mul Q hLm, ih2, hδ₁]
      rfl
  have hdvd : ((normGL σ δ₁ : GL {i // Q i} E) : Matrix {i // Q i} {i // Q i} E).charpoly ∣
      ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly := by
    have h := charpoly_toSq_dvd Q (key (Module.finrank F E)).1
    rw [(key (Module.finrank F E)).2] at h
    exact h
  obtain ⟨P₁, hP₁⟩ := charpoly_normGL_lifts σ hgen δ₁
  have hdvd' : P₁ ∣ p := by
    rw [← Polynomial.map_dvd_map' (algebraMap F E), hP₁, hpc]
    exact hdvd
  have hdegP : P₁.natDegree = Fintype.card {i // Q i} := by
    rw [← Polynomial.natDegree_map (algebraMap F E) (p := P₁), hP₁, Matrix.charpoly_natDegree_eq_dim]
  have hdegp : p.natDegree = n := by
    rw [← Polynomial.natDegree_map (algebraMap F E) (p := p), hpc, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  have hpos : 0 < Fintype.card {i // Q i} :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨0, by omega⟩, hr0⟩⟩
  have hlt : Fintype.card {i // Q i} < n := by
    have h := Fintype.card_subtype_lt (p := Q) (x := (⟨r, hrn⟩ : Fin n)) (by simp [Q])
    simpa using h
  rcases hp.dvd_iff.mp hdvd' with hu | ha
  · have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · have h1 := Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated ha)
    omega
