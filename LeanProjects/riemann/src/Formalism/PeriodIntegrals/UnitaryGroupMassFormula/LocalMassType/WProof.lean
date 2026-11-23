import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SplitDecomp

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section LocF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with hd
  · exact hd.choose_spec.1
  · exact one_ne_zero

theorem alp_ne_zero (r : ℕ) (a : Fin (r + 1)) : alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

theorem locF_injective {n r : ℕ} {X X' : TupV (E := E) v n (r + 1)} (h : locF v X = locF v X') :
    X = X' := by
  funext a
  have ha := congrFun h a
  simp only [locF] at ha
  have hinv : sc (E := E) v (alp v r a)⁻¹ * sc (E := E) v (alp v r a) = 1 := by
    rw [← sc_mul, inv_mul_cancel₀ (alp_ne_zero v r a), sc_one]
  calc X a = (sc (E := E) v (alp v r a)⁻¹ * sc (E := E) v (alp v r a)) • X a := by rw [hinv, one_smul]
    _ = (sc (E := E) v (alp v r a)⁻¹ * sc (E := E) v (alp v r a)) • X' a := by rw [mul_smul, ha, ← mul_smul]
    _ = X' a := by rw [hinv, one_smul]

end LocF

section Coords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def IntV {n : ℕ} (x : Fin n → Fv F v ⊗[F] E) : Prop := ∀ i, x i ∈ OEv (E := E) v

def mkS (e : Fv F v ⊗[F] E) (a b : Fv F v) : Fv F v ⊗[F] E :=
  sc (E := E) v a * e + sc (E := E) v b * (1 - e)

variable {v}
variable {e : Fv F v ⊗[F] E} {π₁ π₂ : Fv F v ⊗[F] E →+* Fv F v}

theorem fst_proj_split_element (hπe1 : π₁ e = 1) (hsc : ∀ c : Fv F v, π₁ (sc (E := E) v c) = c ∧ π₂ (sc (E := E) v c) = c)
    (a b : Fv F v) : π₁ (mkS v e a b) = a := by
  simp [mkS, map_add, map_mul, map_sub, (hsc _).1, hπe1]

theorem snd_proj_split_element (hπe2 : π₂ e = 0) (hsc : ∀ c : Fv F v, π₁ (sc (E := E) v c) = c ∧ π₂ (sc (E := E) v c) = c)
    (a b : Fv F v) : π₂ (mkS v e a b) = b := by
  simp [mkS, map_add, map_mul, map_sub, (hsc _).2, hπe2]

end Coords

section SD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure SD (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) where
  e : Fv F v ⊗[F] E
  π₁ : Fv F v ⊗[F] E →+* Fv F v
  π₂ : Fv F v ⊗[F] E →+* Fv F v
  h1 : ∀ x, x * e = sc (E := E) v (π₁ x) * e
  h2 : ∀ x, x * (1 - e) = sc (E := E) v (π₂ x) * (1 - e)
  he1 : π₁ e = 1
  he2 : π₂ e = 0
  hsc : ∀ c : Fv F v, π₁ (sc (E := E) v c) = c ∧ π₂ (sc (E := E) v c) = c
  hσ1 : ∀ x, π₁ (sigR (Fv F v) σ x) = π₂ x
  hσ2 : ∀ x, π₂ (sigR (Fv F v) σ x) = π₁ x
  hO : ∀ x, x ∈ OEv (E := E) v ↔ π₁ x ∈ v.adicCompletionIntegers F ∧ π₂ x ∈ v.adicCompletionIntegers F

variable {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v)

theorem SD.ext {x y : Fv F v ⊗[F] E} (hx : D.π₁ x = D.π₁ y) (hy : D.π₂ x = D.π₂ y) : x = y :=
  split_ext v D.h1 D.h2 hx hy

theorem SD.extV {n : ℕ} {x y : Fin n → Fv F v ⊗[F] E} (hx : ∀ i, D.π₁ (x i) = D.π₁ (y i))
    (hy : ∀ i, D.π₂ (x i) = D.π₂ (y i)) : x = y := by
  funext i; exact D.ext (hx i) (hy i)

def SD.kS {n : ℕ} (k₁ k₂ : Matrix (Fin n) (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
  Matrix.of fun i j => mkS v D.e (k₁ i j) (k₂ i j)

theorem SD.fst_proj_split_matrix_entry {n : ℕ} (k₁ k₂ : Matrix (Fin n) (Fin n) (Fv F v)) (i j : Fin n) :
    D.π₁ (D.kS k₁ k₂ i j) = k₁ i j := fst_proj_split_element D.he1 D.hsc _ _

theorem SD.snd_proj_split_matrix_entry {n : ℕ} (k₁ k₂ : Matrix (Fin n) (Fin n) (Fv F v)) (i j : Fin n) :
    D.π₂ (D.kS k₁ k₂ i j) = k₂ i j := snd_proj_split_element D.he2 D.hsc _ _

theorem SD.fst_proj_split_matrix_mulVec {n : ℕ} (k₁ k₂ : Matrix (Fin n) (Fin n) (Fv F v)) (x : Fin n → Fv F v ⊗[F] E)
    (i : Fin n) : D.π₁ ((D.kS k₁ k₂ *ᵥ x) i) = (k₁ *ᵥ fun j => D.π₁ (x j)) i := by
  simp only [mulVec, dotProduct, map_sum, map_mul, SD.fst_proj_split_matrix_entry]

theorem SD.snd_proj_split_matrix_mulVec {n : ℕ} (k₁ k₂ : Matrix (Fin n) (Fin n) (Fv F v)) (x : Fin n → Fv F v ⊗[F] E)
    (i : Fin n) : D.π₂ ((D.kS k₁ k₂ *ᵥ x) i) = (k₂ *ᵥ fun j => D.π₂ (x j)) i := by
  simp only [mulVec, dotProduct, map_sum, map_mul, SD.snd_proj_split_matrix_entry]

theorem SD.kS_mul {n : ℕ} (k₁ k₂ l₁ l₂ : Matrix (Fin n) (Fin n) (Fv F v)) :
    D.kS k₁ k₂ * D.kS l₁ l₂ = D.kS (k₁ * l₁) (k₂ * l₂) := by
  ext i j
  apply D.ext
  · simp only [Matrix.mul_apply, map_sum, map_mul, SD.fst_proj_split_matrix_entry]
  · simp only [Matrix.mul_apply, map_sum, map_mul, SD.snd_proj_split_matrix_entry]

theorem SD.kS_one {n : ℕ} : D.kS (1 : Matrix (Fin n) (Fin n) (Fv F v)) 1 = 1 := by
  ext i j
  apply D.ext
  · rw [SD.fst_proj_split_matrix_entry, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  · rw [SD.snd_proj_split_matrix_entry, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

def stdH (σ : E →ₐ[F] E) {n : ℕ} (x y : Fin n → Fv F v ⊗[F] E) : Fv F v ⊗[F] E :=
  ∑ i, sigR (Fv F v) σ (x i) * y i

theorem SD.fst_proj_standard_hermitian_form {n : ℕ} (x y : Fin n → Fv F v ⊗[F] E) :
    D.π₁ (stdH σ x y) = (fun i => D.π₂ (x i)) ⬝ᵥ (fun i => D.π₁ (y i)) := by
  simp only [stdH, map_sum, map_mul, D.hσ1, dotProduct]

theorem SD.snd_proj_standard_hermitian_form {n : ℕ} (x y : Fin n → Fv F v ⊗[F] E) :
    D.π₂ (stdH σ x y) = (fun i => D.π₁ (x i)) ⬝ᵥ (fun i => D.π₂ (y i)) := by
  simp only [stdH, map_sum, map_mul, D.hσ2, dotProduct]

theorem dot_mulVec_mulVec {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) K)
    (u w : Fin n → K) : (M *ᵥ u) ⬝ᵥ (N *ᵥ w) = u ⬝ᵥ ((Mᵀ * N) *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, mulVec_mulVec]

theorem SD.stdH_kS {n : ℕ} (k₁ k₂ : Matrix (Fin n) (Fin n) (Fv F v)) (h21 : k₂ᵀ * k₁ = 1)
    (h12 : k₁ᵀ * k₂ = 1) (x y : Fin n → Fv F v ⊗[F] E) :
    stdH σ (D.kS k₁ k₂ *ᵥ x) (D.kS k₁ k₂ *ᵥ y) = stdH σ x y := by
  apply D.ext
  · rw [SD.fst_proj_standard_hermitian_form, SD.fst_proj_standard_hermitian_form]
    have e1 : (fun i => D.π₂ ((D.kS k₁ k₂ *ᵥ x) i)) = k₂ *ᵥ (fun j => D.π₂ (x j)) := by
      funext i; exact D.snd_proj_split_matrix_mulVec k₁ k₂ x i
    have e2 : (fun i => D.π₁ ((D.kS k₁ k₂ *ᵥ y) i)) = k₁ *ᵥ (fun j => D.π₁ (y j)) := by
      funext i; exact D.fst_proj_split_matrix_mulVec k₁ k₂ y i
    rw [e1, e2, dot_mulVec_mulVec, h21, one_mulVec]
  · rw [SD.snd_proj_standard_hermitian_form, SD.snd_proj_standard_hermitian_form]
    have e1 : (fun i => D.π₁ ((D.kS k₁ k₂ *ᵥ x) i)) = k₁ *ᵥ (fun j => D.π₁ (x j)) := by
      funext i; exact D.fst_proj_split_matrix_mulVec k₁ k₂ x i
    have e2 : (fun i => D.π₂ ((D.kS k₁ k₂ *ᵥ y) i)) = k₂ *ᵥ (fun j => D.π₂ (y j)) := by
      funext i; exact D.snd_proj_split_matrix_mulVec k₁ k₂ y i
    rw [e1, e2, dot_mulVec_mulVec, h12, one_mulVec]

theorem SD.intV_kS {n : ℕ} (k₁ k₂ : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F))
    {x : Fin n → Fv F v ⊗[F] E} (hx : IntV v x) :
    IntV v (D.kS (k₁.map (v.adicCompletionIntegers F).subtype) (k₂.map (v.adicCompletionIntegers F).subtype) *ᵥ x) := by
  intro i
  rw [D.hO]
  constructor
  · rw [SD.fst_proj_split_matrix_mulVec]
    simp only [mulVec, dotProduct, Matrix.map_apply]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (k₁ i j).2 ((D.hO _).1 (hx j)).1
  · rw [SD.snd_proj_split_matrix_mulVec]
    simp only [mulVec, dotProduct, Matrix.map_apply]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (k₂ i j).2 ((D.hO _).1 (hx j)).2

end SD

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem SD.sat₁ {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) {n m : ℕ}
    (Zc : Fin m → Fin n → Fv F v ⊗[F] E) (hprim : ∀ c : Fin m → Fv F v ⊗[F] E,
      IntV v (∑ a, c a • Zc a) → ∀ a, c a ∈ OEv (E := E) v) (t : Fin m → Fv F v)
    (ht : ∀ i, ((Matrix.of fun i a => D.π₁ (Zc a i)) *ᵥ t) i ∈ v.adicCompletionIntegers F) :
    ∀ j, t j ∈ v.adicCompletionIntegers F := by
  intro j
  have hc := hprim (fun a => sc (E := E) v (t a) * D.e) (by
    intro i
    rw [D.hO]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, (D.hsc _).1,
      (D.hsc _).2, D.he1, D.he2, mul_one, mul_zero, zero_mul, Finset.sum_const_zero]
    refine ⟨?_, Subring.zero_mem _⟩
    have := ht i
    simp only [mulVec, dotProduct, Matrix.of_apply] at this
    simpa [mul_comm] using this) j
  have := ((D.hO _).1 hc).1
  simpa [map_mul, (D.hsc _).1, D.he1] using this

theorem SD.sat₂ {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (D : SD σ v) {n m : ℕ}
    (Zc : Fin m → Fin n → Fv F v ⊗[F] E) (hprim : ∀ c : Fin m → Fv F v ⊗[F] E,
      IntV v (∑ a, c a • Zc a) → ∀ a, c a ∈ OEv (E := E) v) (t : Fin m → Fv F v)
    (ht : ∀ i, ((Matrix.of fun i a => D.π₂ (Zc a i)) *ᵥ t) i ∈ v.adicCompletionIntegers F) :
    ∀ j, t j ∈ v.adicCompletionIntegers F := by
  intro j
  have hc := hprim (fun a => sc (E := E) v (t a) * (1 - D.e)) (by
    intro i
    rw [D.hO]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_sub, map_one,
      (D.hsc _).1, (D.hsc _).2, D.he1, D.he2, sub_self, sub_zero, mul_one, mul_zero, zero_mul,
      Finset.sum_const_zero]
    refine ⟨Subring.zero_mem _, ?_⟩
    have := ht i
    simp only [mulVec, dotProduct, Matrix.of_apply] at this
    simpa [mul_comm] using this) j
  have := ((D.hO _).1 hc).2
  simpa [map_mul, map_sub, (D.hsc _).2, D.he2] using this

end Main

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem stepW_core {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}
    {r : ℕ} {P : Frame E n r} {Λ : Set (Fin n → E)} (D : SD σ v) (Q : GL (Fin n) (Fv F v ⊗[F] E))
    (hQΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔
      ∃ x : Fin n → Fv F v ⊗[F] E, (∀ i, x i ∈ OEv (E := E) v) ∧
        y = (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
    (hQh : ∀ x y : Fin n → Fv F v ⊗[F] E,
      hR (Fv F v) σ J ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x)
        ((Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) = ∑ i, sigR (Fv F v) σ (x i) * y i)
    (hSat : SatSplit) (hC : WCore)
    (hPr : IsPrim v Λ (locF v (ratTup (F := F) (Fv F v) (F0 P)))) (h : HA (Fv F v) σ J)
    (hPrh : IsPrim v Λ (locF v (h • ratTup (F := F) (Fv F v) (F0 P)))) :
    ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v,
      k • ratTup (F := F) (Fv F v) (F0 P) = h • ratTup (F := F) (Fv F v) (F0 P) := by
  classical
  set Qm : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (Q : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQm
  set Qi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    ((Q⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) with hQi
  have hQQi : Qm * Qi = 1 := Q.mul_inv
  have hQiQ : Qi * Qm = 1 := Q.inv_mul
  have memΛ : ∀ y, y ∈ latLoc (E := E) v Λ ↔ IntV v (Qi *ᵥ y) := by
    intro y
    rw [hQΛ]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [mulVec_mulVec, hQiQ, one_mulVec]
    · intro hy
      exact ⟨Qi *ᵥ y, hy, by rw [mulVec_mulVec, hQQi, one_mulVec]⟩
  set X0r := ratTup (F := F) (Fv F v) (F0 P) with hX0r
  set Y0 := locF v X0r with hY0
  have hYdef : locF v (h • X0r) = h • Y0 := locF_smul σ J v h X0r
  rw [hYdef] at hPrh

  have hunit : ∀ x y, hR (Fv F v) σ J ((HA.mat (Fv F v) σ J h : Matrix (Fin n) (Fin n) _) *ᵥ x)
      ((HA.mat (Fv F v) σ J h : Matrix (Fin n) (Fin n) _) *ᵥ y) = hR (Fv F v) σ J x y := by
    intro x y
    have hmem := (show HR (Fv F v) σ J from h).2
    show Formalism.UG.hform _ _ _ _ = Formalism.UG.hform _ _ _ _
    rw [hform_mulVec]
    congr 1

  have primT : ∀ W : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, IsPrim v Λ W →
      ∀ c : Fin (r + 1) → Fv F v ⊗[F] E, IntV v (∑ a, c a • (Qi *ᵥ W a)) → ∀ a, c a ∈ OEv (E := E) v := by
    intro W hW c hc
    apply hW.2 c
    rw [memΛ]
    have : Qi *ᵥ (∑ a, c a • W a) = ∑ a, c a • (Qi *ᵥ W a) := by
      show Matrix.mulVecLin Qi (∑ a, c a • W a) = _
      rw [map_sum]
      simp only [map_smul, Matrix.mulVecLin_apply]
    rwa [this]
  set Z0 : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ Y0 a with hZ0def
  set Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun a => Qi *ᵥ (h • Y0) a with hZdef
  have hZ0 : ∀ a, IntV v (Z0 a) := fun a => (memΛ _).1 (hPr.1 a)
  have hZ : ∀ a, IntV v (Z a) := fun a => (memΛ _).1 (hPrh.1 a)
  have pZ0 := primT Y0 hPr
  have pZ := primT (h • Y0) hPrh

  let A0 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₁ (Z0 a i), ((D.hO _).1 (hZ0 a i)).1⟩
  let B0 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₂ (Z0 a i), ((D.hO _).1 (hZ0 a i)).2⟩
  let A1 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₁ (Z a i), ((D.hO _).1 (hZ a i)).1⟩
  let B1 : Matrix (Fin n) (Fin (r + 1)) (v.adicCompletionIntegers F) :=
    Matrix.of fun i a => ⟨D.π₂ (Z a i), ((D.hO _).1 (hZ a i)).2⟩
  have hA0 := hSat v n (r + 1) A0 (fun t ht => D.sat₁ Z0 pZ0 t ht)
  have hB0 := hSat v n (r + 1) B0 (fun t ht => D.sat₂ Z0 pZ0 t ht)
  have hA1 := hSat v n (r + 1) A1 (fun t ht => D.sat₁ Z pZ t ht)
  have hB1 := hSat v n (r + 1) B1 (fun t ht => D.sat₂ Z pZ t ht)

  have hstd : ∀ a b, stdH σ (Z a) (Z b) = stdH σ (Z0 a) (Z0 b) := by
    intro a b
    have e1 : stdH σ (Z a) (Z b) = hR (Fv F v) σ J ((h • Y0) a) ((h • Y0) b) := by
      rw [stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]
    have e2 : stdH σ (Z0 a) (Z0 b) = hR (Fv F v) σ J (Y0 a) (Y0 b) := by
      rw [stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec, one_mulVec]
    rw [e1, e2]
    exact hunit (Y0 a) (Y0 b)
  have hgram : A0ᵀ * B0 = A1ᵀ * B1 := by
    refine Matrix.ext fun a b => Subtype.ext ?_
    have := congrArg D.π₂ (hstd a b)
    rw [D.snd_proj_standard_hermitian_form, D.snd_proj_standard_hermitian_form] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    push_cast
    simp only [dotProduct] at this
    exact this.symm
  obtain ⟨k1, hk1u, hk1A, hk1B⟩ := hC (v.adicCompletionIntegers F) n (r + 1) A0 A1 B0 B1 hA0 hA1 hB0 hB1 hgram
  have hdet : IsUnit k1.det := (Matrix.isUnit_iff_isUnit_det k1).1 hk1u
  have hki : k1 * k1⁻¹ = 1 := Matrix.mul_nonsing_inv k1 hdet
  have hik : k1⁻¹ * k1 = 1 := Matrix.nonsing_inv_mul k1 hdet
  set f := (v.adicCompletionIntegers F).subtype with hf
  have mo : ∀ {M N : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)}, M * N = 1 →
      M.map f * N.map f = 1 := by
    intro M N hMN
    rw [← Matrix.map_mul, hMN, Matrix.map_one f (map_zero f) (map_one f)]
  have e1 : (k1⁻¹)ᵀᵀ * k1 = 1 := by rw [transpose_transpose, hik]
  have e2 : k1ᵀ * (k1⁻¹)ᵀ = 1 := by rw [← transpose_mul, hik, transpose_one]
  have e3 : (k1⁻¹)ᵀ * k1ᵀ = 1 := by rw [← transpose_mul, hki, transpose_one]
  have tm : ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F), (M.map f)ᵀ = Mᵀ.map f :=
    fun M => (Matrix.transpose_map).symm
  set kstd := D.kS (k1.map f) ((k1⁻¹)ᵀ.map f) with hkstd
  set kstd' := D.kS (k1⁻¹.map f) (k1ᵀ.map f) with hkstd'
  have hkk : kstd * kstd' = 1 := by
    rw [hkstd, hkstd', SD.kS_mul, mo hki, mo e3, SD.kS_one]
  have hk'k : kstd' * kstd = 1 := mul_eq_one_comm.mp hkk

  have hkU : ∀ x y, stdH σ (kstd *ᵥ x) (kstd *ᵥ y) = stdH σ x y := by
    intro x y
    refine D.stdH_kS _ _ ?_ ?_ x y
    · rw [tm, mo e1]
    · rw [tm, mo e2]

  have hkI : ∀ x, IntV v (kstd *ᵥ x) ↔ IntV v x := by
    intro x
    constructor
    · intro hx
      have := D.intV_kS (k1⁻¹) k1ᵀ hx
      rwa [← hkstd', mulVec_mulVec, hk'k, one_mulVec] at this
    · intro hx
      exact D.intV_kS k1 (k1⁻¹)ᵀ hx

  have hkZ : ∀ a, kstd *ᵥ Z0 a = Z a := by
    intro a
    apply D.extV
    · intro i
      rw [hkstd, SD.fst_proj_split_matrix_mulVec]
      have := congrArg (fun M => f (M i a)) hk1A
      simp only [Matrix.mul_apply, map_sum, map_mul] at this
      simp only [mulVec, dotProduct, Matrix.map_apply]
      exact this
    · intro i
      have hB : (k1⁻¹)ᵀ * B0 = B1 := by
        rw [← hk1B, ← Matrix.mul_assoc, e3, Matrix.one_mul]
      rw [hkstd, SD.snd_proj_split_matrix_mulVec]
      have := congrArg (fun M => f (M i a)) hB
      simp only [Matrix.mul_apply, map_sum, map_mul] at this
      simp only [mulVec, dotProduct, Matrix.map_apply]
      exact this

  set kM := Qm * kstd * Qi with hkM
  set kMi := Qm * kstd' * Qi with hkMi
  have hkMM : kM * kMi = 1 := by
    rw [hkM, hkMi]
    calc Qm * kstd * Qi * (Qm * kstd' * Qi) = Qm * (kstd * (Qi * Qm) * kstd') * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQiQ, Matrix.mul_one, hkk, Matrix.mul_one, hQQi]
  have hkMM' : kMi * kM = 1 := mul_eq_one_comm.mp hkMM
  let kG : GL (Fin n) (Fv F v ⊗[F] E) := ⟨kM, kMi, hkMM, hkMM'⟩
  have hkx : ∀ x, kM *ᵥ x = Qm *ᵥ (kstd *ᵥ (Qi *ᵥ x)) := by
    intro x; rw [hkM, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hmem : kG ∈ HR (Fv F v) σ J := by
    show Formalism.UG.cT (sigR (Fv F v) σ) kM * JR (Fv F v) J * kM = JR (Fv F v) J
    apply hform_ext (sigR (Fv F v) σ)
    intro x y
    rw [← hform_mulVec]
    show hR (Fv F v) σ J (kM *ᵥ x) (kM *ᵥ y) = hR (Fv F v) σ J x y
    rw [hkx, hkx, hQh, ← stdH, hkU, stdH, ← hQh, mulVec_mulVec, mulVec_mulVec, hQQi, one_mulVec,
      one_mulVec]
  let kH : HA (Fv F v) σ J := (⟨kG, hmem⟩ : HR (Fv F v) σ J)
  refine ⟨kH, ?_, ?_⟩
  · intro y
    show y ∈ latLoc (E := E) v Λ ↔ kM *ᵥ y ∈ latLoc (E := E) v Λ
    rw [memΛ, memΛ, hkx, mulVec_mulVec, hQiQ, one_mulVec, hkI]
  · apply locF_injective v
    rw [locF_smul σ J v kH X0r, hYdef]
    funext a
    show kM *ᵥ Y0 a = (h • Y0) a
    rw [hkx]
    have := hkZ a
    simp only [hZ0def, hZdef] at this
    rw [this, mulVec_mulVec, hQQi, one_mulVec]

theorem stepW_of (hS : SplitR) (hLs : LatStd) (hSat : SatSplit) (hC : WCore) : StepW := by
  intro F E _ _ _ _ _ σ n J ψ v r P Λ T hStd hP hSD hUn hEta hPr hL h hPrh
  obtain ⟨e, π₁, π₂, _he, _hσe, h1, h2, hπe1, hπe2, hπsc, hσ2, hσ1, hO⟩ := hS σ J ψ v hStd hUn hEta
  obtain ⟨Q, hQΛ, hQh⟩ := hLs σ J ψ v Λ hStd hSD hUn hEta hL
  exact stepW_core ⟨e, π₁, π₂, h1, h2, hπe1, hπe2, hπsc, hσ1, hσ2, hO⟩ Q hQΛ hQh hSat hC hPr h hPrh

end Core

end PI.LocMassTypW
