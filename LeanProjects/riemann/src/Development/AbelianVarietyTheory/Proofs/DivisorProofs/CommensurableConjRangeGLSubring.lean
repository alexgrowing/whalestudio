import Mathlib
open Matrix

namespace GlobalTheory

section GLCong

variable {B : Type} [CommRing B] (R : Subring B) {n : ℕ}

theorem glcong_mem_range (A : GL (Fin n) B) (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) B) i j ∈ R)
    (hA' : ∀ i j, ((A⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) :
    A ∈ (GeneralLinearGroup.map (n := Fin n) R.subtype).range := by
  let M : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hA i j⟩
  let N : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hA' i j⟩
  have hM : R.subtype.mapMatrix M = (A : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
  have hN : R.subtype.mapMatrix N = ((A⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
  have hinj : Function.Injective (R.subtype.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) := by
    intro X Y h; ext i j; exact congrFun (congrFun h i) j
  have h1 : M * N = 1 := hinj (by rw [map_mul, map_one, hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : N * M = 1 := hinj (by rw [map_mul, map_one, hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨M, N, h1, h2⟩, ?_⟩
  ext i j
  rfl

theorem glcong_entries (c : R) (h : GL (Fin n) R)
    (hh : GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {c * c})) h = 1)
    (P Q : Matrix (Fin n) (Fin n) B) (hP : ∀ i j, (c : B) * P i j ∈ R) (hQ : ∀ i j, (c : B) * Q i j ∈ R)
    (hPQ : P * Q = 1) :
    ∀ i j, (P * R.subtype.mapMatrix (h : Matrix (Fin n) (Fin n) R) * Q) i j ∈ R := by
  have hX : ∀ i j, ∃ x : R, x * (c * c) = (h : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j := by
    intro i j
    rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Fin n) (R ⧸ Ideal.span {c * c}) => (u : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {c * c})) i j) hh
    simp only [GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  choose X hXe using hX
  let P' : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hP i j⟩
  let Q' : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hQ i j⟩
  let X' : Matrix (Fin n) (Fin n) R := fun i j => X i j
  have hP' : R.subtype.mapMatrix P' = (c : B) • P := by ext i j; rfl
  have hQ' : R.subtype.mapMatrix Q' = (c : B) • Q := by ext i j; rfl
  have hh' : (h : Matrix (Fin n) (Fin n) R) = 1 + (c * c) • X' := by
    refine Matrix.ext fun i j => ?_
    show _ = (1 : Matrix (Fin n) (Fin n) R) i j + (c * c) * X i j
    rw [mul_comm, hXe i j]; ring
  have key : P * R.subtype.mapMatrix (h : Matrix (Fin n) (Fin n) R) * Q
      = R.subtype.mapMatrix (1 + P' * X' * Q') := by
    have hs : R.subtype.mapMatrix ((c * c) • X') = ((c : B) * (c : B)) • R.subtype.mapMatrix X' := by
      ext i j
      change ((c * c * X i j : R) : B) = (c : B) * c * (X i j : B)
      push_cast; ring
    rw [map_add, map_one, map_mul, map_mul, hP', hQ', hh', map_add, map_one, hs]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  intro i j
  rw [key]
  exact ((1 + P' * X' * Q' : Matrix (Fin n) (Fin n) R) i j).2

theorem glcong_relIndex_ne_zero (c : R) (hfin : Finite (R ⧸ Ideal.span {c * c})) (g : GL (Fin n) B)
    (hg : ∀ i j, (c : B) * (g : Matrix (Fin n) (Fin n) B) i j ∈ R)
    (hg' : ∀ i j, (c : B) * ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) :
    (((GeneralLinearGroup.map (n := Fin n) R.subtype).range).map (MulAut.conj g).toMonoidHom).relIndex
      (GeneralLinearGroup.map (n := Fin n) R.subtype).range ≠ 0 := by
  set φ := GeneralLinearGroup.map (n := Fin n) R.subtype
  set ψ := GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {c * c}))
  have hΓ : ψ.ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    ext i j
    exact congrArg (fun u : GL (Fin n) B => (u : Matrix (Fin n) (Fin n) B) i j) hab
  have h1 : (ψ.ker.map φ).relIndex φ.range ≠ 0 := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj,
      Subgroup.relIndex_top_right]
    exact hΓ
  have hval : ∀ h : GL (Fin n) R, ((φ h : GL (Fin n) B) : Matrix (Fin n) (Fin n) B)
      = R.subtype.mapMatrix (h : Matrix (Fin n) (Fin n) R) := fun h => rfl
  have hgg : ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) * (g : Matrix (Fin n) (Fin n) B) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : ψ.ker.map φ ≤ φ.range.map (MulAut.conj g).toMonoidHom := by
    rintro x ⟨h, hh, rfl⟩
    replace hh : ψ h = 1 := hh
    have hh' : ψ h⁻¹ = 1 := by rw [map_inv, hh, inv_one]
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * φ h * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    apply glcong_mem_range
    · intro i j
      have := glcong_entries R c h hh _ _ hg' hg hgg i j
      rwa [Units.val_mul, Units.val_mul, hval]
    · intro i j
      have := glcong_entries R c h⁻¹ hh' _ _ hg' hg hgg i j
      rwa [show (g⁻¹ * φ h * g)⁻¹ = g⁻¹ * φ h⁻¹ * g by rw [map_inv]; group, Units.val_mul, Units.val_mul, hval]
  exact fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_left h2 h0)

end GLCong

theorem commensurable_conj_range_GL_subring {B : Type} [CommRing B] (R : Subring B) (n : ℕ) (c : R)
    (hfin : Finite (R ⧸ Ideal.span {c * c})) (g : GL (Fin n) B)
    (hg : ∀ i j, (c : B) * (g : Matrix (Fin n) (Fin n) B) i j ∈ R)
    (hg' : ∀ i j, (c : B) * ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) :
    Subgroup.Commensurable ((GeneralLinearGroup.map R.subtype).range.map (MulAut.conj g).toMonoidHom)
      (GeneralLinearGroup.map R.subtype).range := by
  set K := (GeneralLinearGroup.map (n := Fin n) R.subtype).range
  refine ⟨glcong_relIndex_ne_zero R c hfin g hg hg', ?_⟩
  have e := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (K.map (MulAut.conj g⁻¹).toMonoidHom) K (MulEquiv.injective _)
  have hK : (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id K]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hK] at e
  rw [e]
  exact glcong_relIndex_ne_zero R c hfin g⁻¹ hg' (by simpa using hg)

end GlobalTheory
