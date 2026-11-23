import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IndTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InducedAutomorphicForms.IndSymp

open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Sd.S2 Matrix

section

variable {k : Type} [Field k]

private def Pm (a b : k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 4) k :=
  Matrix.of (Sum.elim ![![0, a, 0, a], ![b, 0, -b, 0]] ![![0, -1, 0, 1], ![1, 0, 1, 0]])

private def Qm (a b : k) : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) k :=
  Matrix.of ![Sum.elim ![0, (2 * b)⁻¹] ![0, 2⁻¹], Sum.elim ![(2 * a)⁻¹, 0] ![-2⁻¹, 0],
    Sum.elim ![0, -(2 * b)⁻¹] ![0, 2⁻¹], Sum.elim ![(2 * a)⁻¹, 0] ![2⁻¹, 0]]

private def J4 (k : Type) [Field k] : M4 k := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private lemma QP {a b : k} (h2 : (2 : k) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) : Qm a b * Pm a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;> field_simp <;> ring

private lemma PQ {a b : k} (h2 : (2 : k) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) : Pm a b * Qm a b = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private lemma Qmix {a b : kˣ} (h2 : (2 : k) ≠ 0) (A B : Matrix (Fin 2) (Fin 2) k) :
    Qm (a : k) b * Matrix.fromBlocks A 0 0 B * Pm (a : k) b = mix (b / a) A B := by
  have ha := a.ne_zero
  have hb := b.ne_zero
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm, mix] <;> field_simp <;> ring

private lemma Qoff {a b : k} (h2 : (2 : k) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    Qm a b * Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) k) (Matrix.diagonal ![a ^ 2, b ^ 2]) (1 : Matrix (Fin 2) (Fin 2) k)
      (0 : Matrix (Fin 2) (Fin 2) k) * Pm a b = Matrix.diagonal ![b, -a, -b, a] := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm] <;> field_simp <;> ring

private lemma gram (a b : k) :
    (Pm a b)ᵀ * Matrix.fromBlocks (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k) (0 : Matrix (Fin 2) (Fin 2) k) (0 : Matrix (Fin 2) (Fin 2) k)
      ((a * b) • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) k)) * Pm a b = (-2 * (a * b)) • J4 k := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [Pm, J4] <;> ring

private lemma adj_eq (Y : M4 k) : adj Y = -J4 k * Yᵀ * J4 k := by
  ext i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [J4, adj_apply, sgn, Fin.rev]

private lemma JJ : -J4 k * J4 k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J4, Matrix.mul_apply, Fin.sum_univ_four]

private lemma gsp {a b ν : k} (h2 : (2 : k) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (X B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) (hB : (Pm a b)ᵀ * B * Pm a b = (-2 * (a * b)) • J4 k)
    (hX : Xᵀ * B * X = ν • B) : IsGSp ν (Qm a b * X * Pm a b) := by
  have hc : (-2 * (a * b)) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2) (mul_ne_zero ha hb)
  have hPY : Pm a b * (Qm a b * X * Pm a b) = X * Pm a b := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, PQ h2 ha hb, Matrix.one_mul]
  generalize Qm a b * X * Pm a b = Y at hPY
  have h1 : (-2 * (a * b)) • (Yᵀ * J4 k * Y) = (-2 * (a * b)) • (ν • J4 k) := by
    calc _ = Yᵀ * ((Pm a b)ᵀ * B * Pm a b) * Y := by rw [hB, Matrix.mul_smul, Matrix.smul_mul]
      _ = (Pm a b * Y)ᵀ * B * (Pm a b * Y) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (Pm a b)ᵀ * (Xᵀ * B * X) * Pm a b := by
        rw [hPY]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hX, Matrix.mul_smul, Matrix.smul_mul, hB, smul_comm]
  have h3 : Yᵀ * J4 k * Y = ν • J4 k := smul_right_injective _ hc h1
  unfold IsGSp
  rw [adj_eq]
  calc _ = -J4 k * (Yᵀ * J4 k * Y) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h3, Matrix.mul_smul, JJ]

end

theorem UpperTheory.symmetric_square_mixed_exists :
    UpperTheory.V.Sd.S2.MixEx := by
  intro k Γ₀ Γ _ _ _ j t α β ρ μ h2 hj hi ht hsq hdet hαβ
  have ha := α.ne_zero
  have hb := β.ne_zero
  let e : Γ₀ ≃* j.range := MonoidHom.ofInjective hj
  have he : ∀ h, ((e h : j.range) : Γ) = j h := fun h => rfl
  let r : j.range →* GL (Fin 2) k := ρ.comp e.symm.toMonoidHom
  have hr : ∀ h, r (e h) = ρ h := fun h => by simp [r]
  obtain ⟨I, hI1, hI2⟩ := UpperTheory.V.AlgebraTools.indTwo j.range t hi ht r
  have hS := UpperTheory.V.AlgebraTools.indSymp j.range t hi ht r μ I (by
    intro h
    obtain ⟨h, rfl⟩ := e.surjective h
    rw [hr, he, ← hdet, Matrix.GeneralLinearGroup.val_det_apply]) hI1 hI2
  let M : Γ →* M4 k :=
    { toFun := fun g => Qm (α : k) β * (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) * Pm (α : k) β
      map_one' := by rw [map_one, Units.val_one, Matrix.mul_one, QP h2 ha hb]
      map_mul' := by
        intro x y
        rw [map_mul, Units.val_mul]
        calc _ = Qm (α : k) β * (I x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) * (Pm (α : k) β * Qm (α : k) β) *
              (I y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) * Pm (α : k) β := by
                rw [PQ h2 ha hb]; simp only [Matrix.mul_assoc, Matrix.one_mul]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hM : ∀ g, ((M.toHomUnits g : GL (Fin 4) k) : M4 k) =
      Qm (α : k) β * (I g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) * Pm (α : k) β := fun g => rfl
  refine ⟨M.toHomUnits, ⟨h2, hj, hi, ht, hsq, ?_, ?_⟩, ?_⟩
  · intro h h' hh
    have := hI1 (e h) (e h') hh
    rw [he, hr, hr] at this
    rw [hM, this, Qmix h2]
  · obtain ⟨u, hu⟩ := Subgroup.mul_self_mem_of_index_two hi t
    have := hI2 (e u) hu
    rw [hr, hsq u hu] at this
    rw [hM, this, Qoff h2 ha hb]
  · intro g
    rw [hM]
    refine gsp h2 ha hb _ _ ?_ (hS g)
    rw [← hαβ, Units.val_mul]
    exact gram _ _
