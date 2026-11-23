import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem UpperTheory.isUnit_det_joinM {A : Type} [CommRing A] {r s N : ℕ} (h : r + s = N)
    (M₁ : Matrix (Fin N) (Fin r) A) (M₂ L : Matrix (Fin N) (Fin s) A) (σ : Fin r → Fin N)
    (h1 : (M₁.submatrix σ id).det = 1) (h2 : M₂ᵀ * L = 1) (h3 : M₂ᵀ * M₁ = 0) :
    IsUnit (joinM h M₁ L).det := by
  classical
  have hb : Function.Bijective (Sum.elim (lo h) (hi h) : Fin r ⊕ Fin s → Fin N) := by
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨fun i => ?_, by simp [h]⟩
    rcases lo_or_hi h i with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨.inl k, hk⟩
    · exact ⟨.inr k, hk⟩
  let e : Fin r ⊕ Fin s ≃ Fin N := Equiv.ofBijective _ hb
  have hJ : (joinM h M₁ L).submatrix e e = (Matrix.fromCols M₁ L).submatrix e id := by
    ext a b
    rcases b with b | b
    · have : ((lo h b : Fin N) : ℕ) < r := b.2
      simp only [Matrix.submatrix_apply, e, Equiv.ofBijective_apply, Sum.elim_inl, id, Matrix.fromCols_apply_inl,
        RootFrame.joinM, Matrix.of_apply, dif_pos this]
      rfl
    · have hb2 := b.2
      have : ¬ ((hi h b : Fin N) : ℕ) < r := by simp only [hi]; omega
      simp only [Matrix.submatrix_apply, e, Equiv.ofBijective_apply, Sum.elim_inr, id, Matrix.fromCols_apply_inr,
        RootFrame.joinM, Matrix.of_apply, dif_neg this]
      congr 1
      exact Fin.ext (by simp only [hi]; omega)
  let P : Matrix (Fin r) (Fin N) A := (1 : Matrix (Fin N) (Fin N) A).submatrix σ id
  have hP : P * M₁ = M₁.submatrix σ id := by
    ext a b
    simp [P, Matrix.mul_apply, Matrix.one_apply]
  have hm : (Matrix.fromRows P M₂ᵀ).submatrix id e * (joinM h M₁ L).submatrix e e =
      Matrix.fromBlocks (M₁.submatrix σ id) (P * L) 0 1 := by
    rw [hJ, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.fromRows_mul_fromCols, hP, h2, h3]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, h1, Matrix.det_one, _root_.one_mul, Matrix.det_submatrix_equiv_self] at hd
  exact IsUnit.of_mul_eq_one_right _ hd

private theorem UpperTheory.joinM_map' {A B : Type} {r s N : ℕ} (h : r + s = N) (f : A → B)
    (M₁ : Matrix (Fin N) (Fin r) A) (L : Matrix (Fin N) (Fin s) A) :
    (joinM h M₁ L).map f = joinM h (M₁.map f) (L.map f) := by
  ext a b
  simp only [RootFrame.joinM, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> rfl

theorem UpperTheory.joined_matrix_det_valuation_one :
    ∀ (K : Type) [Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean w → ∀ (r s N : ℕ) (h : r + s = N) (M₁ : Matrix (Fin N) (Fin r) K) (M₂ L : Matrix (Fin N) (Fin s) K) (σ : Fin r → Fin N), (∀ k i, w (M₁ k i) ≤ 1) → (∀ k i, w (M₂ k i) ≤ 1) → (∀ k i, w (L k i) ≤ 1) → (M₁.submatrix σ id).det = 1 → M₂ᵀ * L = 1 → (∀ i j, w ((M₁ᵀ * M₂) i j) < 1) → w (joinM h M₁ L).det = 1 := by
  intro K _ w hw r s N h M₁ M₂ L σ b1 b2 b3 h1 h2 h3
  let O : Subring K :=
    { carrier := {x | w x ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul] at *
        exact mul_le_one₀ ha (w.nonneg _) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => (hw a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha }
  let I : Ideal O :=
    { carrier := {x | w (x : K) < 1}
      add_mem' := fun {a b} ha hb => (hw a b).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have hc : w (c : K) ≤ 1 := c.2
        have hx' : w (x : K) < 1 := hx
        show w ((c : K) * x) < 1
        rw [map_mul]
        exact (mul_le_of_le_one_left (w.nonneg _) hc).trans_lt hx' }
  have hI : I ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one]
    show ¬ w (1 : K) < 1
    simp
  let A₁ : Matrix (Fin N) (Fin r) O := Matrix.of fun k i => ⟨M₁ k i, b1 k i⟩
  let A₂ : Matrix (Fin N) (Fin s) O := Matrix.of fun k i => ⟨M₂ k i, b2 k i⟩
  let B : Matrix (Fin N) (Fin s) O := Matrix.of fun k i => ⟨L k i, b3 k i⟩
  have e1 : A₁.map O.subtype = M₁ := rfl
  have e2 : A₂.map O.subtype = M₂ := rfl
  have e3 : B.map O.subtype = L := rfl
  have g1 : (A₁.submatrix σ id).det = 1 := by
    apply O.subtype_injective
    rw [RingHom.map_det, map_one, ← h1]
    rfl
  have g2 : A₂ᵀ * B = 1 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    rw [← e2, ← e3, ← Matrix.transpose_map, ← Matrix.map_mul, Matrix.map_apply] at this
    show O.subtype _ = O.subtype _
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have g3 : ∀ i j, (A₂ᵀ * A₁) i j ∈ I := by
    intro i j
    have := h3 j i
    rw [← e2, ← e1, ← Matrix.transpose_map, ← Matrix.map_mul, Matrix.map_apply] at this
    have e : A₂ᵀ * A₁ = (A₁ᵀ * A₂)ᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [e]
    exact this
  let q := Ideal.Quotient.mk I
  have hu := UpperTheory.isUnit_det_joinM h (A₁.map q) (A₂.map q) (B.map q) σ
    (by rw [← map_one q, ← g1, RingHom.map_det]; rfl)
    (by rw [← Matrix.transpose_map, ← Matrix.map_mul, g2, Matrix.map_one _ (map_zero q) (map_one q)])
    (by
      rw [← Matrix.transpose_map, ← Matrix.map_mul]
      ext i j
      exact Ideal.Quotient.eq_zero_iff_mem.2 (g3 i j))
  rw [← UpperTheory.joinM_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hu
  have hn : (joinM h A₁ B).det ∉ I := by
    intro hmem
    haveI := Ideal.Quotient.nontrivial_iff.2 hI
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem] at hu
    exact not_isUnit_zero hu
  have hd : (joinM h M₁ L).det = O.subtype (joinM h A₁ B).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, UpperTheory.joinM_map', e1, e3]
  rw [hd]
  exact le_antisymm (joinM h A₁ B).det.2 (not_lt.1 hn)
