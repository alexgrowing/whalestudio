import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.CardRangeRedJ

noncomputable section

open Matrix Formalism.DoubleCosetMeasures.P.GLRed

namespace PI.ParahoricIdxZ.W

section C

variable {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ∈ O)

def param {a t : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a)
    (p : (redJ O ϖ hϖ J' hJ).range × Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ×
      GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) :
    Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) :=
  theta ((p.1 : GL (Fin a) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : Matrix _ _ _) p.2.1 0
    ((p.2.2 : GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : Matrix _ _ _)

theorem param_injective {a t : ℕ} (J' : Subgroup (GL (Fin a) F)) (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) :
    Function.Injective (param (t := t) O hϖ J' hJ) := by
  rintro ⟨x, B, D⟩ ⟨x', B', D'⟩ h
  obtain ⟨h1, h2, -, h4⟩ := theta_injective h
  have hx : x = x' := Subtype.ext (Units.ext h1)
  have hD : D = D' := Units.ext h4
  subst hx hD h2
  rfl

theorem image_eq (hϖ0 : ϖ ≠ 0) (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (hJint : J' ≤ Formalism.DoubleCosetMeasures.GLint O a)
    (J : Subgroup (GL (Fin (a + t)) F)) (hJ : ∀ A, A ∈ J ↔ blockCond O ϖ J' A) :
    (fun g : GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) =>
      (g : Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) ''
      (((J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).map (red O (a + t) ϖ hϖ) : Subgroup _) : Set _) =
      Set.range (param O hϖ J' hJint) := by
  ext M
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_map] at hg
    obtain ⟨h, hH, rfl⟩ := hg
    rw [Subgroup.mem_subgroupOf, hJ] at hH
    simp only [blockCond] at hH
    obtain ⟨⟨k, hk, hkv⟩, hB, hC, ⟨D, hD, hDv⟩⟩ := hH
    refine ⟨⟨⟨redJ O ϖ hϖ J' hJint ⟨k, hk⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩,
      fun i j => Ideal.Quotient.mk _ ⟨_, hB i j⟩, red O t ϖ hϖ ⟨D, hD⟩⟩, ?_⟩
    symm
    apply red_eq_theta
    rintro (x | x) (y | y)
    · exact (mk_congr O ϖ hϖ _ ((hJint hk).1 x y)
        (by rw [hkv]; simp [Matrix.toBlocks₁₁, reindex_apply'])).trans rfl
    · exact (mk_congr O ϖ hϖ _ (hB x y) (by simp [Matrix.toBlocks₁₂, reindex_apply'])).trans rfl
    · obtain ⟨o, ho, he⟩ := hC x y
      exact (mk_eq_zero O ϖ hϖ _ o ho
        (by rw [← he]; simp [Matrix.toBlocks₂₁, reindex_apply'])).trans rfl
    · exact (mk_congr O ϖ hϖ _ (hD.1 x y)
        (by rw [hDv]; simp [Matrix.toBlocks₂₂, reindex_apply'])).trans rfl
  · rintro ⟨⟨⟨xb, hxb⟩, Bb, Db⟩, rfl⟩
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hxb
    obtain ⟨D, rfl⟩ := red_surj O t ϖ hϖ hloc Db
    choose Bl hBl using fun i j =>
      Ideal.Quotient.mk_surjective (I := Ideal.span {(⟨ϖ, hϖ⟩ : O)}) (Bb i j)
    have hk := hJint k.2
    set BF : Matrix (Fin a) (Fin t) F := fun i j => (Bl i j : F) with hBF
    have hBFi : ∀ i j, BF i j ∈ O := fun i j => (Bl i j).2
    set kM : Matrix (Fin a) (Fin a) F := ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) with hkM
    set kI : Matrix (Fin a) (Fin a) F := (((k : GL (Fin a) F)⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
      with hkI
    set DM : Matrix (Fin t) (Fin t) F := (((D : GL (Fin t) F)) : Matrix (Fin t) (Fin t) F) with hDM
    set DI : Matrix (Fin t) (Fin t) F := (((D : GL (Fin t) F)⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F)
      with hDI
    have hkk : kM * kI = 1 := Units.mul_inv _
    have hkk' : kI * kM = 1 := Units.inv_mul _
    have hDD : DM * DI = 1 := Units.mul_inv _
    have hDD' : DI * DM = 1 := Units.inv_mul _
    have h1 : theta kM BF 0 DM * theta kI (-(kI * BF * DI)) 0 DI = 1 := by
      rw [theta_mul]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
        ← Matrix.mul_assoc, hkk, hDD, Matrix.one_mul, neg_add_cancel, neg_zero, zero_add, theta_one]
    have h2 : theta kI (-(kI * BF * DI)) 0 DI * theta kM BF 0 DM = 1 := by
      rw [theta_mul]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul,
        Matrix.mul_assoc, hkk', hDD', Matrix.mul_one, add_neg_cancel, neg_zero, zero_add, theta_one]
    obtain ⟨hF, hFv, hFi⟩ : ∃ g : GL (Fin (a + t)) F, (g : Matrix (Fin (a + t)) (Fin (a + t)) F) = theta kM BF 0 DM ∧
        ((g⁻¹ : GL (Fin (a + t)) F) : Matrix (Fin (a + t)) (Fin (a + t)) F) = theta kI (-(kI * BF * DI)) 0 DI :=
      ⟨⟨_, _, h1, h2⟩, rfl, rfl⟩
    have hmem : hF ∈ Formalism.DoubleCosetMeasures.GLint O (a + t) := by
      refine ⟨?_, ?_⟩
      · rw [hFv]
        exact theta_int O hk.1 hBFi (fun _ _ => O.zero_mem) D.2.1
      · rw [hFi]
        refine theta_int O hk.2 (fun i j => ?_) (fun _ _ => O.zero_mem) D.2.2
        rw [Matrix.neg_apply]
        exact O.neg_mem (intProd O (intProd O hk.2 hBFi) D.2.2 i j)
    have hbc : blockCond O ϖ J' hF := by
      simp only [blockCond]
      rw [hFv, reindex_theta]
      refine ⟨⟨k, k.2, ?_⟩, fun i j => ?_, fun i j => ⟨0, O.zero_mem, ?_⟩, ⟨D, D.2, ?_⟩⟩
      · simp [hkM]
      · simpa using hBFi i j
      · simp
      · simp [hDM]
    refine ⟨red O (a + t) ϖ hϖ ⟨hF, hmem⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_map]
      exact ⟨⟨hF, hmem⟩, by rw [Subgroup.mem_subgroupOf, hJ]; exact hbc, rfl⟩
    · apply red_eq_theta
      rintro (x | x) (y | y)
      · refine (mk_entry O ϖ hϖ ⟨hF, hmem⟩ hFv _ _ ?_).trans ?_
        · exact hk.1 x y
        · rfl
      · refine (mk_entry O ϖ hϖ ⟨hF, hmem⟩ hFv _ _ ?_).trans ?_
        · exact hBFi x y
        · exact hBl x y
      · refine (mk_entry O ϖ hϖ ⟨hF, hmem⟩ hFv _ _ ?_).trans ?_
        · exact O.zero_mem
        · exact map_zero _
      · refine (mk_entry O ϖ hϖ ⟨hF, hmem⟩ hFv _ _ ?_).trans ?_
        · exact D.2.1 x y
        · rfl

end C

end PI.ParahoricIdxZ.W
