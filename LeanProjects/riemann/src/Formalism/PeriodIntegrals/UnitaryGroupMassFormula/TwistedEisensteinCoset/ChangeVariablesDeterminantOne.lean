import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.WeightedSumToGaussSum

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE Function Matrix

variable {E K : Type} [Field E] [NumberField E] [Field K]

theorem qt_id {P : HeightOneSpectrum (𝓞 E)} {ι : Type} [Fintype ι] [DecidableEq ι] :
    QT P (fun t : ι → E => t) (1 : K) :=
  fun a b => ⟨a, b, fun _ h => ⟨h, (one_mul _).symm⟩⟩

section Lin

variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem qt_transvec (t : TransvectionStruct ι E) :
    QT P (fun v => t.toMatrix *ᵥ v) ((qOf P : K) ^ vq P t.toMatrix.det) := by
  have hmv : ∀ v : ι → E, t.toMatrix *ᵥ v = em t.i t.j 1 t.c 0 v := by
    intro v
    funext k
    by_cases h : k = t.i
    · subst h
      simp [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
        Matrix.single_mulVec, em] <;> ring
    · simp [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
        Matrix.single_mulVec, em, h]
  exact qt_congr (qt_em hN hp hq hK t.i t.j one_ne_zero t.c 0 (Or.inl t.hij.symm)) hmv (by rw [t.det])

theorem qt_diag (D : ι → E) (hD : ∀ i, D i ≠ 0) :
    QT P (fun v => diagonal D *ᵥ v) ((qOf P : K) ^ vq P (diagonal D).det) := by
  classical
  have key : ∀ s : Finset ι, QT P (fun v : ι → E => fun k => if k ∈ s then D k * v k else v k)
      ((qOf P : K) ^ (∑ k ∈ s, vq P (D k))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact qt_congr qt_id (fun v => by funext k; simp) (by simp)
    | insert a s ha ih =>
      refine qt_congr (qt_comp (qt_em hN hp hq hK a a (hD a) 0 0 (Or.inr rfl)) ih) (fun v => ?_) ?_
      · funext k
        by_cases hk : k = a
        · subst hk
          simp [em, ha]
        · simp [em, hk, Function.update_apply]
      · rw [Finset.sum_insert ha, zpow_add₀ hK, mul_comm]
  refine qt_congr (key Finset.univ) (fun v => by funext k; simp [Matrix.mulVec_diagonal]) ?_
  rw [Matrix.det_diagonal, vq_prod (s := Finset.univ) (f := D) (hf := fun i _ => hD i)]
  all_goals assumption

theorem qt_matrix (M : Matrix ι ι E) (hM : M.det ≠ 0) :
    QT P (fun v => M *ᵥ v) ((qOf P : K) ^ vq P M.det) := by
  classical
  obtain ⟨L, L', D, hMLD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hlist : ∀ l : List (TransvectionStruct ι E),
      QT P (fun v => (l.map TransvectionStruct.toMatrix).prod *ᵥ v) (1 : K) := by
    intro l
    induction l with
    | nil => exact qt_congr qt_id (fun v => by simp) rfl
    | cons t l ih =>
      refine qt_congr (qt_comp (qt_transvec hN hp hq hK t) ih) (fun v => by simp [Matrix.mulVec_mulVec]) ?_
      rw [t.det, vq_one, zpow_zero, one_mul]
      all_goals assumption
  have hl1 : ∀ l : List (TransvectionStruct ι E), ((l.map TransvectionStruct.toMatrix).prod).det = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih => simp [Matrix.det_mul, t.det, ih]
  have hdetM : M.det = (diagonal D).det := by
    rw [hMLD, Matrix.det_mul, Matrix.det_mul, hl1, hl1, one_mul, mul_one]
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    apply hM
    rw [hdetM, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  refine qt_congr (qt_comp (hlist L) (qt_comp (qt_diag hN hp hq hK D hD) (hlist L')))
    (fun v => by rw [hMLD]; simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]) ?_
  rw [hdetM, one_mul, mul_one]

theorem qt_transl (τ : ι → E) : QT P (fun v : ι → E => v + τ) (1 : K) := by
  classical
  have key : ∀ s : Finset ι, QT P (fun v : ι → E => fun k => if k ∈ s then v k + τ k else v k) (1 : K) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact qt_congr qt_id (fun v => by funext k; simp) rfl
    | insert a s ha ih =>
      refine qt_congr (qt_comp (qt_em hN hp hq hK a a one_ne_zero 0 (τ a) (Or.inr rfl)) ih) (fun v => ?_) ?_
      · funext k
        by_cases hk : k = a
        · subst hk
          simp [em, ha]
        · simp [em, hk, Function.update_apply]
      · rw [vq_one, zpow_zero, one_mul]
        all_goals assumption
  exact qt_congr (key Finset.univ) (fun v => by funext k; simp) rfl

theorem qt_aff (L : (ι → E) ≃ₗ[E] (ι → E)) (τ : ι → E) :
    QT P (fun t => L t + τ) ((qOf P : K) ^ vq P (LinearMap.det (L : (ι → E) →ₗ[E] (ι → E)))) := by
  have hL : ∀ t, L t = LinearMap.toMatrix' (L : (ι → E) →ₗ[E] (ι → E)) *ᵥ t :=
    fun t => (LinearMap.toMatrix'_mulVec _ t).symm
  have hdet : (LinearMap.toMatrix' (L : (ι → E) →ₗ[E] (ι → E))).det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (LinearEquiv.isUnit_det' L).ne_zero
  refine qt_congr (qt_comp (qt_transl hN hp hq hK τ) (qt_matrix hN hp hq hK _ hdet))
    (fun t => by simp only [hL]) ?_
  rw [LinearMap.det_toMatrix', mul_one]

end Lin

def ChangeVariablesDeterminantOne : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ((qOf P : ℕ) : K) ≠ 0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L : (ι → E) ≃ₗ[E] (ι → E)) (τ : ι → E),
      LinearMap.det (L : (ι → E) →ₗ[E] (ι → E)) = 1 →
      ∀ a b : ℕ, ∃ a' b' : ℕ, ∀ H : (ι → E) → K, Good P a b H →
        Good P a' b' (fun t => H (L t + τ)) ∧ RS P a' b' (fun t => H (L t + τ)) = RS P a b H

theorem cov_of (hN : NTAll) : CoVP := by
  intro E K _ _ _ P hp hq hK ι _ _ L τ
  exact ⟨(qOf P : K) ^ vq P (LinearMap.det (L : (ι → E) →ₗ[E] (ι → E))), zpow_ne_zero _ hK,
    qt_aff hN hp hq hK L τ⟩

theorem change_variables_determinant_one (hN : NTAll) : ChangeVariablesDeterminantOne := by
  intro E K _ _ _ P hp hq hK ι _ _ L τ h1 a b
  obtain ⟨a', b', h⟩ := qt_aff hN hp hq hK L τ a b
  refine ⟨a', b', fun H hH => ?_⟩
  obtain ⟨g, e⟩ := h H hH
  refine ⟨g, ?_⟩
  rw [e, h1, vq_one, zpow_zero, one_mul]
  all_goals assumption

end PI.TwistedEisensteinNonvanishing.W
