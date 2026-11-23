import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace UnipotentMeasureProperties

variable {R : Type} [CommRing R] {k : ℕ}

def Fx (P Q : Fin k → Prop) (γ : GL (Fin k) R) : Prop :=
  ∀ i c : Fin k, (P i ∨ Q c) → γ.val i c = (1 : Matrix (Fin k) (Fin k) R) i c

theorem fx_mul {P Q : Fin k → Prop} {γ γ' : GL (Fin k) R} (h : Fx P Q γ) (h' : Fx P Q γ') :
    Fx P Q (γ * γ') := by
  intro i c hic
  rw [Units.val_mul, Matrix.mul_apply]
  rcases hic with hi | hc
  · have e : ∀ l, γ.val i l = (1 : Matrix (Fin k) (Fin k) R) i l := fun l => h i l (Or.inl hi)
    simp_rw [e]
    rw [← Matrix.mul_apply, Matrix.one_mul]
    exact h' i c (Or.inl hi)
  · have e : ∀ l, γ'.val l c = (1 : Matrix (Fin k) (Fin k) R) l c := fun l => h' l c (Or.inr hc)
    simp_rw [e]
    rw [← Matrix.mul_apply, Matrix.mul_one]
    exact h i c (Or.inr hc)

theorem fx_inv {P Q : Fin k → Prop} {γ : GL (Fin k) R} (h : Fx P Q γ) : Fx P Q γ⁻¹ := by
  intro i c hic
  rcases hic with hi | hc
  · have e : ∀ l, γ.val i l = (1 : Matrix (Fin k) (Fin k) R) i l := fun l => h i l (Or.inl hi)
    have key : (γ.val * γ⁻¹.val) i c = (1 : Matrix (Fin k) (Fin k) R) i c := by rw [Units.mul_inv]
    rw [Matrix.mul_apply] at key
    simp_rw [e] at key
    rwa [← Matrix.mul_apply, Matrix.one_mul] at key
  · have e : ∀ l, γ.val l c = (1 : Matrix (Fin k) (Fin k) R) l c := fun l => h l c (Or.inr hc)
    have key : (γ⁻¹.val * γ.val) i c = (1 : Matrix (Fin k) (Fin k) R) i c := by rw [Units.inv_mul]
    rw [Matrix.mul_apply] at key
    simp_rw [e] at key
    rwa [← Matrix.mul_apply, Matrix.mul_one] at key

theorem row_mul_inv {A B : GL (Fin k) R} {r : Fin k} (h : ∀ c, A.val r c = B.val r c) (c : Fin k) :
    (A * B⁻¹).val r c = (1 : Matrix (Fin k) (Fin k) R) r c := by
  rw [Units.val_mul, Matrix.mul_apply]
  simp_rw [h]
  rw [← Matrix.mul_apply, Units.mul_inv]

theorem row_of_one {A B : GL (Fin k) R} {r : Fin k} (h : ∀ c, A.val r c = (1 : Matrix (Fin k) (Fin k) R) r c)
    (c : Fin k) : (A * B).val r c = B.val r c := by
  rw [Units.val_mul, Matrix.mul_apply]
  simp_rw [h]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem blk_iff {j : ℕ} {γ : GL (Fin k) R} : GlobalTheory j γ ↔ Fx (fun i => j ≤ (i : ℕ)) (fun c => j ≤ (c : ℕ)) γ := Iff.rfl

section Fld

variable {E : Type} [Field E] {k : ℕ}

theorem blk_of_mir {j : ℕ} (hj : 1 ≤ j) {γ : GL (Fin k) E} (h : IsMir (j - 1) γ) : GlobalTheory j γ := by
  intro i c hic
  apply h
  rcases hic with hi | hc
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem mir_of {j : ℕ} (hj : 1 ≤ j) {γ : GL (Fin k) E} (hB : GlobalTheory j γ)
    (hr : ∀ i c : Fin k, (i : ℕ) + 1 = j → γ.val i c = (1 : Matrix (Fin k) (Fin k) E) i c) : IsMir (j - 1) γ := by
  intro i c hic
  by_cases hi : (i : ℕ) + 1 = j
  · exact hr i c hi
  · apply hB
    rcases hic with h1 | h2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end Fld

section Gam

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem exists_gam {j : ℕ} (hjk : j ≤ k) (ξ : RowT E k j) :
    ∃ γ : GL (Fin k) E, GlobalTheory j γ ∧ ∀ i c : Fin k, (i : ℕ) + 1 = j → γ.val i c = ξ.1 c := by
  obtain ⟨i₀, h0⟩ : ∃ i, ξ.1 i ≠ 0 := by
    by_contra h
    push Not at h
    exact ξ.2.1 (funext h)
  have hi0 : (i₀ : ℕ) < j := by
    by_contra h
    exact h0 (ξ.2.2 i₀ (by omega))
  set i₁ : Fin k := ⟨j - 1, by omega⟩ with hi₁
  set σ := Equiv.swap i₀ i₁ with hσ
  set u : Fin k → E := Pi.single i₀ 1 with hu
  set v : Fin k → E := ξ.1 - Pi.single i₀ 1 with hv
  set N : Matrix (Fin k) (Fin k) E := 1 + replicateCol Unit u * replicateRow Unit v with hN
  have hNe : ∀ i c, N i c = (1 : Matrix (Fin k) (Fin k) E) i c + u i * v c := by
    intro i c
    simp [N, Matrix.mul_apply, replicateCol, replicateRow]
  have hdet : N.det = ξ.1 i₀ := by
    rw [hN, det_one_add_replicateCol_mul_replicateRow]
    simp [u, v, dotProduct, Pi.single_apply]
  set M := N.submatrix σ id with hM
  have hMu : IsUnit M.det := by
    rw [hM, det_permute, hdet]
    exact IsUnit.mul (by simp) (isUnit_iff_ne_zero.mpr h0)
  have hMe : ∀ i c, M i c = (1 : Matrix (Fin k) (Fin k) E) (σ i) c + u (σ i) * v c := fun i c => hNe _ _
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).mpr hMu).unit, ?_, ?_⟩
  · intro i c hic
    change M i c = _
    rw [hMe]
    rcases hic with hi | hc'
    · have a1 : i ≠ i₀ := fun e => by rw [e] at hi; omega
      have a2 : i ≠ i₁ := fun e => by have : (i₁ : ℕ) = j - 1 := rfl; rw [e] at hi; omega
      have hs : σ i = i := by rw [hσ]; exact Equiv.swap_apply_of_ne_of_ne a1 a2
      rw [hs, hu, Pi.single_apply, if_neg a1, zero_mul, add_zero]
    · have b1 : c ≠ i₀ := fun e => by rw [e] at hc'; omega
      have b2 : c ≠ i₁ := fun e => by have : (i₁ : ℕ) = j - 1 := rfl; rw [e] at hc'; omega
      have hs : σ i = c ↔ i = c := by
        rw [← Equiv.eq_symm_apply, hσ, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne b1 b2]
      have hv0 : v c = 0 := by rw [hv, Pi.sub_apply, Pi.single_apply, if_neg b1, ξ.2.2 c hc', sub_zero]
      rw [hv0, mul_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
      simp only [hs]
  · intro i c hi
    change M i c = _
    have : i = i₁ := Fin.ext (by simp [i₁]; omega)
    have hs : σ i₁ = i₀ := by rw [hσ, Equiv.swap_apply_right]
    rw [hMe, this, hs, hu, hv, Pi.single_eq_same, one_mul, Pi.sub_apply, Matrix.one_apply, Pi.single_apply]
    by_cases h : c = i₀
    · subst h; simp
    · simp [h, Ne.symm h]

theorem gam_spec {j : ℕ} (hjk : j ≤ k) (ξ : RowT E k j) :
    GlobalTheory j (gam ξ) ∧ ∀ i c : Fin k, (i : ℕ) + 1 = j → (gam ξ).val i c = ξ.1 c := by
  unfold gam
  exact Classical.epsilon_spec (exists_gam hjk ξ)

end Gam

section Rest

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem row_gam_mul {j : ℕ} (hjk : j ≤ k) {p : GL (Fin k) E} (hp : IsMir (j - 1) p) (ξ : RowT E k j)
    (i c : Fin k) (hi : (i : ℕ) + 1 = j) : (p * gam ξ).val i c = ξ.1 c := by
  rw [row_of_one (fun l => hp i l (Or.inl (by omega))) c]
  exact (gam_spec hjk ξ).2 i c hi

theorem lubinTateSeries_eq_of_coeff_one_eq {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {p p' : GL (Fin k) E} {ξ ξ' : RowT E k j}
    (hp : IsMir (j - 1) p) (hp' : IsMir (j - 1) p') (h : p * gam ξ = p' * gam ξ') : ξ = ξ' ∧ p = p' := by
  have hξ : ξ = ξ' := by
    apply Subtype.ext
    funext c
    have i₁ : Fin k := ⟨j - 1, by omega⟩
    rw [← row_gam_mul hjk hp ξ ⟨j - 1, by omega⟩ c (by simp; omega),
      ← row_gam_mul hjk hp' ξ' ⟨j - 1, by omega⟩ c (by simp; omega), h]
  subst hξ
  exact ⟨rfl, mul_right_cancel h⟩

theorem exists_coset {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (γ : GL (Fin k) E) (hγ : GlobalTheory j γ) :
    ∃ p : RowT E k j × GL (Fin k) E, IsMir (j - 1) p.2 ∧ γ = p.2 * gam p.1 := by
  set i₁ : Fin k := ⟨j - 1, by omega⟩ with hi₁
  have ne : (fun c => γ.val i₁ c) ≠ 0 := by
    intro h
    have key : (γ.val * γ⁻¹.val) i₁ i₁ = (1 : Matrix (Fin k) (Fin k) E) i₁ i₁ := by rw [Units.mul_inv]
    rw [Matrix.mul_apply] at key
    simp [fun c => congr_fun h c] at key
  have supp : ∀ c : Fin k, j ≤ (c : ℕ) → γ.val i₁ c = 0 := by
    intro c hc
    rw [hγ i₁ c (Or.inr hc), Matrix.one_apply, if_neg]
    intro e
    have : (i₁ : ℕ) = (c : ℕ) := congr_arg Fin.val e
    simp [i₁] at this
    omega
  let ξ : RowT E k j := ⟨fun c => γ.val i₁ c, ne, supp⟩
  refine ⟨(ξ, γ * (gam ξ)⁻¹), ?_, by simp⟩
  apply mir_of hj
  · exact (blk_iff.mpr (fx_mul (blk_iff.mp hγ) (fx_inv (blk_iff.mp (gam_spec hjk ξ).1))))
  · intro i c hi
    have : i = i₁ := Fin.ext (by simp [i₁]; omega)
    subst this
    exact row_mul_inv (fun c => ((gam_spec hjk ξ).2 i₁ c hi).symm) c

def rowE (γ : GL (Fin k) E) (ξ : RowT E k k) : RowT E k k :=
  ⟨ξ.1 ᵥ* γ.val, fun h => ξ.2.1 (by
      have : ξ.1 ᵥ* γ.val ᵥ* γ⁻¹.val = 0 := by rw [h, Matrix.zero_vecMul]
      rwa [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one] at this), fun i hi => absurd i.isLt (by omega)⟩

def rowEq (γ : GL (Fin k) E) : RowT E k k ≃ RowT E k k where
  toFun := rowE γ
  invFun := rowE γ⁻¹
  left_inv ξ := Subtype.ext (by simp [rowE, Matrix.vecMul_vecMul])
  right_inv ξ := Subtype.ext (by simp [rowE, Matrix.vecMul_vecMul])

theorem row_mul (hk : 1 ≤ k) (γ : GL (Fin k) E) (ξ : RowT E k k) :
    ∃ p, IsMir (k - 1) p ∧ gam ξ * γ = p * gam (rowEq γ ξ) := by
  refine ⟨gam ξ * γ * (gam (rowEq γ ξ))⁻¹, ?_, by simp⟩
  apply mir_of hk
  · intro i c hic
    exfalso
    rcases hic with h | h <;> omega
  · intro i c hi
    apply row_mul_inv
    intro c
    rw [(gam_spec le_rfl (rowEq γ ξ)).2 i c hi, Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [(gam_spec le_rfl ξ).2 i l hi]

theorem last_row (hk : 1 ≤ k) (ξ : RowT E k k) (g : GA E k) :
    lastRow (ratGL E k (gam ξ) * g) = (fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val := by
  funext c
  simp only [lastRow]
  rw [Finset.sum_eq_single (⟨k - 1, by omega⟩ : Fin k)]
  · rw [if_pos (by simp; omega), Units.val_mul, Matrix.mul_apply]
    simp only [Matrix.vecMul, dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← (gam_spec le_rfl ξ).2 ⟨k - 1, by omega⟩ l (by simp; omega)]
    rfl
  · intro b _ hb
    rw [if_neg]
    intro e
    exact hb (Fin.ext (by simp; omega))
  · simp

theorem countable_rowT (j : ℕ) : Countable (RowT E k j) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  unfold RowT
  infer_instance

end Rest

end UnipotentMeasureProperties

theorem mem_unipotent_fixer_of : N0 := by
  intro E _ _ _ k j hj hjk
  have hk : 1 ≤ k := le_trans hj hjk
  refine ⟨fun ξ => UnipotentMeasureProperties.gam_spec hjk ξ, ?_, fun γ γ' h h' => UnipotentMeasureProperties.fx_mul h h', fun γ h => UnipotentMeasureProperties.fx_inv h,
    fun γ γ' h h' => UnipotentMeasureProperties.fx_mul h h', fun γ h => ⟨UnipotentMeasureProperties.fx_inv h, UnipotentMeasureProperties.blk_of_mir hj h⟩, UnipotentMeasureProperties.countable_rowT j, ?_,
    fun γ => ⟨UnipotentMeasureProperties.rowEq γ, UnipotentMeasureProperties.row_mul hk γ⟩, fun ξ g => UnipotentMeasureProperties.last_row hk ξ g⟩
  · intro γ hγ
    obtain ⟨p, hp, hpe⟩ := UnipotentMeasureProperties.exists_coset hj hjk γ hγ
    refine ⟨p, ⟨hp, hpe⟩, ?_⟩
    rintro q ⟨hq, hqe⟩
    obtain ⟨h1, h2⟩ := UnipotentMeasureProperties.lubinTateSeries_eq_of_coeff_one_eq hj hjk hq hp (hqe.symm.trans hpe)
    exact Prod.ext h1 h2
  · intro γ i c hic
    exfalso
    rcases hic with h | h <;> omega

end PositivityTheory.AdelicQuotientData

end
