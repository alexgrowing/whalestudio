import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

namespace UpperTheory.JoinedMatrixIntegral

private theorem joinM_lo {K : Type} {r s N : ℕ} (h : r + s = N) (M : Matrix (Fin N) (Fin r) K)
    (L : Matrix (Fin N) (Fin s) K) (k : Fin N) (i : Fin r) : joinM h M L k (lo h i) = M k i := by
  exact dif_pos (c := ((lo h i : Fin N) : ℕ) < r) i.2

private theorem joinM_hi {K : Type} {r s N : ℕ} (h : r + s = N) (M : Matrix (Fin N) (Fin r) K)
    (L : Matrix (Fin N) (Fin s) K) (k : Fin N) (j : Fin s) : joinM h M L k (hi h j) = L k j := by
  have hj := j.2
  have h1 : ¬ ((hi h j : Fin N) : ℕ) < r := by simp only [hi]; omega
  refine (dif_neg h1).trans ?_
  congr 1
  apply Fin.ext
  simp only [hi]; omega

private theorem joinM_map {K K' : Type} (f : K → K') {r s N : ℕ} (h : r + s = N) (M : Matrix (Fin N) (Fin r) K)
    (L : Matrix (Fin N) (Fin s) K) : (joinM h M L).map f = joinM h (M.map f) (L.map f) := by
  ext k i
  rcases lo_or_hi h i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · simp [joinM_lo]
  · simp [joinM_hi]

private theorem sum_split {A : Type} [AddCommMonoid A] {r s N : ℕ} (h : r + s = N) (f : Fin N → A) :
    ∑ n, f n = ∑ i, f (lo h i) + ∑ j, f (hi h j) := by
  have hb : Function.Bijective (Sum.elim (lo h) (hi h)) := by
    constructor
    · rintro (a | a) (b | b) hab <;> have ha := a.2 <;> have hb := b.2 <;>
        simp only [Sum.elim_inl, Sum.elim_inr, lo, hi, Fin.mk.injEq] at hab
      · congr 1; exact Fin.ext hab
      · omega
      · omega
      · congr 1; exact Fin.ext (by omega)
    · intro i
      rcases lo_or_hi h i with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨.inl a, rfl⟩
      · exact ⟨.inr a, rfl⟩
  rw [← Fintype.sum_bijective _ hb (fun x => f (Sum.elim (lo h) (hi h) x)) f (fun _ => rfl), Fintype.sum_sum_type]
  rfl

private theorem core {k : Type} [CommRing k] {r s N : ℕ} (h : r + s = N) (M₁ : Matrix (Fin N) (Fin r) k)
    (M₂ L L' : Matrix (Fin N) (Fin s) k) (σ₁ : Fin r → Fin N) (t : Matrix (Fin r) (Fin r) k)
    (t' : Matrix (Fin s) (Fin s) k) (C : Matrix (Fin N) (Fin N) k)
    (hd : (M₁.submatrix σ₁ id).det = 1) (hL : M₂ᵀ * L = 1) (hL' : (M₂ * t')ᵀ * L' = 1) (ho : M₁ᵀ * M₂ = 0)
    (ht : t.BlockTriangular id) (ht' : t'.BlockTriangular id)
    (hC : joinM h M₁ L * C = joinM h (M₁ * t) L') :
    C.BlockTriangular id ∧ (∀ i, C (lo h i) (lo h i) = t i i) ∧ ∀ j, C (hi h j) (hi h j) * t' j j = 1 := by
  have ho' : M₂ᵀ * M₁ = 0 := by
    have := congrArg Matrix.transpose ho
    simpa [Matrix.transpose_mul] using this
  have e1 : M₁ * C.submatrix (lo h) (lo h) + L * C.submatrix (hi h) (lo h) = M₁ * t := by
    ext a i
    have := congrFun (congrFun hC a) (lo h i)
    rw [joinM_lo, Matrix.mul_apply, sum_split h] at this
    simpa [joinM_lo, joinM_hi, Matrix.mul_apply] using this
  have e2 : M₁ * C.submatrix (lo h) (hi h) + L * C.submatrix (hi h) (hi h) = L' := by
    ext a i
    have := congrFun (congrFun hC a) (hi h i)
    rw [joinM_hi, Matrix.mul_apply, sum_split h] at this
    simpa [joinM_lo, joinM_hi, Matrix.mul_apply] using this
  have c21 : C.submatrix (hi h) (lo h) = 0 := by
    have := congrArg (fun X => M₂ᵀ * X) e1
    simpa [Matrix.mul_add, ← Matrix.mul_assoc, ho', hL] using this
  have c11 : C.submatrix (lo h) (lo h) = t := by
    rw [c21, Matrix.mul_zero, add_zero] at e1
    have e3 : M₁.submatrix σ₁ id * C.submatrix (lo h) (lo h) = M₁.submatrix σ₁ id * t := by
      ext a i
      exact congrFun (congrFun e1 (σ₁ a)) i
    have := congrArg (fun X => (M₁.submatrix σ₁ id).adjugate * X) e3
    simpa only [← Matrix.mul_assoc, Matrix.adjugate_mul, hd, one_smul, Matrix.one_mul] using this
  have c22 : (C.submatrix (hi h) (hi h))ᵀ * t' = 1 := by
    have := congrArg (fun X => M₂ᵀ * X) e2
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, ho', hL, Matrix.zero_mul, zero_add, Matrix.one_mul] at this
    rw [this]
    have := congrArg Matrix.transpose hL'
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have hinv : (C.submatrix (hi h) (hi h))ᵀ.BlockTriangular id := by
    letI : Invertible t' := invertibleOfLeftInverse _ _ c22
    rw [← Matrix.inv_eq_left_inv c22]
    exact Matrix.blockTriangular_inv_of_blockTriangular ht'
  refine ⟨?_, fun i => congrFun (congrFun c11 i) i, fun j => ?_⟩
  · intro a b hab
    simp only [id] at hab
    rcases lo_or_hi h a with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases lo_or_hi h b with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact (congrFun (congrFun c11 a) b).trans (ht hab)
    · have ha := a.2
      have hb := b.2
      simp only [lo, hi, Fin.mk_lt_mk] at hab
      omega
    · exact congrFun (congrFun c21 a) b
    · have ha := a.2
      have hb := b.2
      simp only [hi, Fin.mk_lt_mk] at hab
      exact hinv (i := b) (j := a) (show (a : ℕ) < b by omega)
  · have := congrFun (congrFun c22 j) j
    rw [Matrix.mul_apply, Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with hb | hb
      · rw [hinv (i := j) (j := b) hb, zero_mul]
      · rw [ht' (i := b) (j := j) hb, mul_zero]
    · simp

private theorem setup {K : Type} [Field K] (w : AbsoluteValue K ℝ) (hw : IsNonarchimedean w) :
    ∃ (O : Subring K) (I : Ideal O), (∀ x, x ∈ O ↔ w x ≤ 1) ∧ ∀ x : O, x ∈ I ↔ w x < 1 := by
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
    { carrier := {x | w x < 1}
      add_mem' := fun {a b} ha hb => (hw a b).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        have hc : w c ≤ 1 := c.2
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, map_mul] at *
        exact (mul_le_of_le_one_left (w.nonneg _) hc).trans_lt ha }
  exact ⟨O, I, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

private theorem liftM {K : Type} [Field K] (O : Subring K) {m n : Type} (X : Matrix m n K) (hX : ∀ i j, X i j ∈ O) :
    ∃ Y : Matrix m n O, Y.map O.subtype = X :=
  ⟨Matrix.of fun i j => ⟨X i j, hX i j⟩, rfl⟩

private theorem tint {K : Type} [Field K] (O : Subring K) {r N : ℕ} (M : Matrix (Fin N) (Fin r) O) (σ : Fin r → Fin N)
    (t : Matrix (Fin r) (Fin r) K) (hd : ((M.map O.subtype).submatrix σ id).det = 1)
    (ht : ∀ k i, (M.map O.subtype * t) k i ∈ O) : ∃ Y : Matrix (Fin r) (Fin r) O, Y.map O.subtype = t := by
  obtain ⟨Y, hY⟩ := liftM O _ ht
  refine ⟨(M.submatrix σ id).adjugate * Y.submatrix σ id, ?_⟩
  have e1 : (Y.submatrix σ id).map O.subtype = (M.map O.subtype).submatrix σ id * t := by
    ext a i
    exact congrFun (congrFun hY (σ a)) i
  have e2 : (M.submatrix σ id).adjugate.map O.subtype = ((M.map O.subtype).submatrix σ id).adjugate :=
    RingHom.map_adjugate O.subtype (M.submatrix σ id)
  rw [Matrix.map_mul, e1, e2, ← Matrix.mul_assoc, Matrix.adjugate_mul, hd, one_smul, Matrix.one_mul]

end UpperTheory.JoinedMatrixIntegral

open UpperTheory.JoinedMatrixIntegral in
theorem UpperTheory.joined_matrices_valuation_compare :
    ∀ (K : Type) [Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean w → ∀ (r s N : ℕ) (h : r + s = N) (M₁ M₁' : Matrix (Fin N) (Fin r) K) (M₂ L M₂' L' : Matrix (Fin N) (Fin s) K) (σ₁ : Fin r → Fin N) (σ₂ : Fin s → Fin N) (t : Matrix (Fin r) (Fin r) K) (t' : Matrix (Fin s) (Fin s) K), (∀ k i, w (M₁ k i) ≤ 1) → (∀ k i, w (M₂ k i) ≤ 1) → (∀ k i, w (L k i) ≤ 1) → (∀ k i, w (M₁' k i) ≤ 1) → (∀ k i, w (M₂' k i) ≤ 1) → (∀ k i, w (L' k i) ≤ 1) → (M₁.submatrix σ₁ id).det = 1 → (M₂.submatrix σ₂ id).det = 1 → M₂ᵀ * L = 1 → M₂'ᵀ * L' = 1 → (∀ i j, w ((M₁ᵀ * M₂) i j) < 1) → w (joinM h M₁ L).det = 1 → w (joinM h M₁' L').det = 1 → t.BlockTriangular id → t'.BlockTriangular id → (∀ j, w (t' j j) = 1) → (∀ k i, w (M₁' k i - (M₁ * t) k i) < 1) → (∀ k i, w (M₂' k i - (M₂ * t') k i) < 1) → ∃ B : Matrix (Fin N) (Fin N) K, B.BlockTriangular id ∧ (∀ i k, w ((joinM h M₁ L * B) i k) ≤ 1) ∧ w (joinM h M₁ L * B).det = 1 ∧ (∀ i k, w (joinM h M₁' L' i k - (joinM h M₁ L * B) i k) < 1) ∧ (∀ i, w (B (lo h i) (lo h i) - t i i) < 1) ∧ ∀ j, w (B (hi h j) (hi h j) * t' j j - 1) < 1 := by
  intro K _ w hw r s N h M₁ M₁' M₂ L M₂' L' σ₁ σ₂ t t' h1 h2 h3 h4 h5 h6 d1 d2 hL hL' ho hG hG' ht ht' _ c1 c2
  obtain ⟨O, I, hO, hI⟩ := setup w hw
  have hint : ∀ a b : K, a ∈ O → w (a - b) < 1 → b ∈ O := fun a b ha hab => by
    have := O.sub_mem ha ((hO _).2 hab.le)
    simpa using this
  obtain ⟨M₁, rfl⟩ := liftM O M₁ fun i j => (hO _).2 (h1 i j)
  obtain ⟨M₂, rfl⟩ := liftM O M₂ fun i j => (hO _).2 (h2 i j)
  obtain ⟨t, rfl⟩ := tint O M₁ σ₁ t d1 fun k i => hint _ _ ((hO _).2 (h4 k i)) (c1 k i)
  obtain ⟨t', rfl⟩ := tint O M₂ σ₂ t' d2 fun k i => hint _ _ ((hO _).2 (h5 k i)) (c2 k i)
  obtain ⟨L, rfl⟩ := liftM O L fun i j => (hO _).2 (h3 i j)
  obtain ⟨M₁', rfl⟩ := liftM O M₁' fun i j => (hO _).2 (h4 i j)
  obtain ⟨M₂', rfl⟩ := liftM O M₂' fun i j => (hO _).2 (h5 i j)
  obtain ⟨L', rfl⟩ := liftM O L' fun i j => (hO _).2 (h6 i j)
  set ρ := Ideal.Quotient.mk I with hρdef
  have hρ : ∀ a b : O, ρ a = ρ b ↔ w ((a : K) - b) < 1 := fun a b => by
    rw [hρdef, Ideal.Quotient.eq, hI]; rfl
  have hinj : ∀ {m n : Type} (X Y : Matrix m n O), X.map O.subtype = Y.map O.subtype → X = Y :=
    fun X Y hXY => Matrix.map_injective O.subtype_injective hXY
  have hdet : ∀ {n : ℕ} (X : Matrix (Fin n) (Fin n) O), (X.map O.subtype).det = (X.det : K) :=
    fun X => (RingHom.map_det O.subtype X).symm
  rw [← joinM_map, hdet] at hG hG'
  rw [← joinM_map, ← joinM_map]
  have hu : IsUnit (joinM h M₁ L).det := by
    have hne : ((joinM h M₁ L).det : K) ≠ 0 := by
      intro h0; rw [h0] at hG; simp at hG
    refine IsUnit.of_mul_eq_one ⟨((joinM h M₁ L).det : K)⁻¹, (hO _).2 (by rw [map_inv₀, hG]; simp)⟩ ?_
    exact Subtype.ext (mul_inv_cancel₀ hne)
  obtain ⟨C, hC⟩ : ∃ C, joinM h M₁ L * C = joinM h M₁' L' :=
    ⟨(joinM h M₁ L)⁻¹ * joinM h M₁' L', Matrix.mul_nonsing_inv_cancel_left _ _ hu⟩
  have r1 : M₁'.map ρ = M₁.map ρ * t.map ρ := by
    rw [← Matrix.map_mul]
    ext k i
    refine (hρ _ _).2 ?_
    have := c1 k i
    rwa [← Matrix.map_mul] at this
  have r2 : M₂'.map ρ = M₂.map ρ * t'.map ρ := by
    rw [← Matrix.map_mul]
    ext k i
    refine (hρ _ _).2 ?_
    have := c2 k i
    rwa [← Matrix.map_mul] at this
  have hone : ∀ (X Y : Matrix (Fin N) (Fin s) O), (X.map O.subtype)ᵀ * Y.map O.subtype = 1 →
      (X.map ρ)ᵀ * Y.map ρ = 1 := fun X Y hXY => by
    have : Xᵀ * Y = 1 := hinj _ _ (by
      rw [Matrix.map_mul, Matrix.transpose_map, hXY, Matrix.map_one _ (map_zero _) (map_one _)])
    rw [← Matrix.transpose_map, ← Matrix.map_mul, this, Matrix.map_one _ (map_zero _) (map_one _)]
  have htri : ∀ {n : ℕ} (X : Matrix (Fin n) (Fin n) O), (X.map O.subtype).BlockTriangular id →
      (X.map ρ).BlockTriangular id := fun X hX i j hij => by
    have : X i j = 0 := Subtype.ext (hX hij)
    simp [this]
  obtain ⟨k1, k2, k3⟩ := core h (M₁.map ρ) (M₂.map ρ) (L.map ρ) (L'.map ρ) σ₁ (t.map ρ) (t'.map ρ) (C.map ρ)
    (by
      have : (M₁.submatrix σ₁ id).det = 1 := Subtype.ext ((hdet (M₁.submatrix σ₁ id)).symm.trans d1)
      exact (RingHom.map_det ρ (M₁.submatrix σ₁ id)).symm.trans (by rw [this, map_one]))
    (hone _ _ hL) (by rw [← r2]; exact hone _ _ hL')
    (by
      rw [← Matrix.transpose_map, ← Matrix.map_mul]
      ext i j
      have := ho i j
      rw [← Matrix.transpose_map, ← Matrix.map_mul] at this
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((hI _).2 this))
    (htri _ ht) (htri _ ht') (by rw [← r1, ← joinM_map, ← joinM_map, ← Matrix.map_mul, hC])
  let B : Matrix (Fin N) (Fin N) O := Matrix.of fun i j => if j < i then 0 else C i j
  have hB : B.map ρ = C.map ρ := by
    ext i j
    by_cases hij : j < i
    · rw [k1 (i := i) (j := j) hij]; simp [B, hij]
    · simp [B, hij]
  have hBd : ∀ i, B i i = C i i := fun i => by simp [B]
  have hGB : (joinM h M₁' L').map ρ = (joinM h M₁ L * B).map ρ := by
    rw [Matrix.map_mul, hB, ← Matrix.map_mul, hC]
  refine ⟨B.map O.subtype, fun i j hij => ?_, fun i k => ?_, ?_, fun i k => ?_, fun i => ?_, fun j => ?_⟩
  · have : j < i := hij
    simp [B, this]
  · rw [← Matrix.map_mul]
    exact (hO _).1 ((joinM h M₁ L * B) i k).2
  · rw [← Matrix.map_mul, hdet]
    have e : ρ (joinM h M₁' L').det = ρ (joinM h M₁ L * B).det := by
      rw [RingHom.map_det, RingHom.map_det]
      exact congrArg Matrix.det hGB
    have e' := (hρ _ _).1 e
    refine le_antisymm ((hO _).1 (joinM h M₁ L * B).det.2) (not_lt.1 fun hlt => ?_)
    have := (hw _ _).trans_lt (max_lt e' hlt)
    rw [sub_add_cancel, hG'] at this
    exact lt_irrefl _ this
  · rw [← Matrix.map_mul]
    exact (hρ _ _).1 (congrFun (congrFun hGB i) k)
  · refine (hρ (B (lo h i) (lo h i)) (t i i)).1 ?_
    rw [hBd]
    exact k2 i
  · refine (hρ (B (hi h j) (hi h j) * t' j j) 1).1 ?_
    rw [hBd, map_mul, map_one]
    exact k3 j
