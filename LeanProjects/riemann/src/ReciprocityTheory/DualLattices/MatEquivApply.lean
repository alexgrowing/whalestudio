import ReciprocityTheory.DualLattices.DualLenStatement
import ReciprocityTheory.DualLattices.BlockOneMulMulBlockOne

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {R : Type} [CommRing R]

def matEquiv {d : ℕ} (P : Matrix (Fin d) (Fin d) R) (hP : IsUnit P.det) :
    (Fin d → R) ≃ₗ[R] (Fin d → R) :=
  LinearEquiv.ofLinear (Matrix.toLin' P) (Matrix.toLin' P⁻¹)
    (by rw [← Matrix.toLin'_mul, mul_nonsing_inv _ hP, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, nonsing_inv_mul _ hP, Matrix.toLin'_one])

lemma matEquiv_apply {d : ℕ} (P : Matrix (Fin d) (Fin d) R) (hP : IsUnit P.det) (x : Fin d → R) :
    matEquiv P hP x = P *ᵥ x := by
  show Matrix.toLin' P x = P *ᵥ x
  rw [Matrix.toLin'_apply]

lemma sum_val_eq {n : ℕ} (j : ℕ) (f : Fin n → R) :
    ∑ k : Fin n, (if (k : ℕ) = j then f k else 0) = if h : j < n then f ⟨j, h⟩ else 0 := by
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨j, h⟩ (fun k hk => if_neg fun h' => hk (Fin.ext h'))]
    exact if_pos rfl
  · exact Finset.sum_eq_zero fun k _ => if_neg fun (h' : (k : ℕ) = j) => h (h' ▸ k.isLt)

lemma hasLen_pi {C : Type} [Field C] (v : Valuation C NNReal) [Algebra R C] {d : ℕ} (a : Fin d → R) :
    HasLen v R ((Fin d → R) ⧸ Submodule.pi Set.univ (fun j => (Ideal.span {a j} : Submodule R R)))
      (∏ j, v (algebraMap R C (a j))) :=
  ⟨d, a, ⟨Submodule.quotientPi _⟩, rfl⟩

private lemma hasLen_of_linearEquiv' {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
    {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] {x : NNReal}
    (h : HasLen v R M x) (e : M ≃ₗ[R] M') : HasLen v R M' x := by
  obtain ⟨m, c, ⟨e0⟩, hc⟩ := h
  exact ⟨m, c, ⟨e.symm.trans e0⟩, hc⟩

theorem dualLen_fin {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
    (hv : v.Integers R) {d n : ℕ} (A : Matrix (Fin d) (Fin n) R) (c : R) (hc : c ≠ 0)
    (hkill : ∀ w : Fin d → R, ∃ t, A *ᵥ t = c • w) {c₁ : NNReal}
    (hc₁ : HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) c₁) :
    ∃ y : NNReal, HasLen v R ((Fin d → R) ⧸ zSub A c) y ∧ y * c₁ = v (algebraMap R C c) ^ d := by
  classical
  obtain ⟨P, Q, a, hP, hQ, hD⟩ := Smith.smith_mat hv d n A
  have hPQ : ∀ t : Fin n → R, (P * A * Q) *ᵥ (Q⁻¹ *ᵥ t) = P *ᵥ (A *ᵥ t) := by
    intro t
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (P * A), Matrix.mul_nonsing_inv _ hQ,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have hDv : ∀ (s : Fin n → R) (j : Fin d),
      ((P * A * Q) *ᵥ s) j = if h : (j : ℕ) < n then a j * s ⟨j, h⟩ else 0 := by
    intro s j
    have h1 := sum_val_eq (j : ℕ) (fun k => a j * s k)
    rw [← h1]
    simp only [Matrix.mulVec, dotProduct, hD, ite_mul, zero_mul]
  have hDt : ∀ (y : Fin d → R) (k : Fin n),
      ((P * A * Q)ᵀ *ᵥ y) k = if h : (k : ℕ) < d then a ⟨k, h⟩ * y ⟨k, h⟩ else 0 := by
    intro y k
    have h1 := sum_val_eq (k : ℕ) (fun j => a j * y j)
    rw [← h1]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hD, ite_mul, zero_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : (k : ℕ) = (j : ℕ)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hdiv : ∀ j : Fin d, (j : ℕ) < n ∧ ∃ b, a j * b = c := by
    intro j
    obtain ⟨t, ht⟩ := hkill (P⁻¹ *ᵥ Pi.single j 1)
    have h1 : (P * A * Q) *ᵥ (Q⁻¹ *ᵥ t) = c • Pi.single j 1 := by
      rw [hPQ, ht, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP,
        Matrix.one_mulVec]
    have h2 := congrFun h1 j
    rw [hDv] at h2
    by_cases h : (j : ℕ) < n
    · rw [dif_pos h] at h2
      exact ⟨h, (Q⁻¹ *ᵥ t) ⟨j, h⟩, by simpa using h2⟩
    · rw [dif_neg h] at h2
      have h3 : c = 0 := by simpa using h2.symm
      exact absurd h3 hc
  choose hlt b hb using hdiv
  have ha0 : ∀ j, a j ≠ 0 := fun j h => hc (by rw [← hb j, h, zero_mul])
  have hcancel : ∀ j (x z : R), a j * x = a j * z → x = z := by
    intro j x z h
    apply hv.hom_inj
    have h' := congrArg (algebraMap R C) h
    rw [map_mul, map_mul] at h'
    have hne : algebraMap R C (a j) ≠ 0 := by
      intro h0
      apply ha0 j
      apply hv.hom_inj
      rw [h0, map_zero]
    exact mul_left_cancel₀ hne h'
  have e1 : ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[R]
      ((Fin d → R) ⧸ Submodule.pi Set.univ (fun j => (Ideal.span {a j} : Submodule R R))) := by
    refine Submodule.Quotient.equiv _ _ (matEquiv P hP) ?_
    ext x
    rw [Submodule.mem_map, Submodule.mem_pi]
    constructor
    · rintro ⟨y, hy, rfl⟩ j -
      obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hy
      rw [Ideal.mem_span_singleton']
      refine ⟨(Q⁻¹ *ᵥ t) ⟨j, hlt j⟩, ?_⟩
      simp only [LinearEquiv.coe_coe, matEquiv_apply, Matrix.mulVecLin_apply]
      rw [← hPQ, hDv, dif_pos (hlt j), mul_comm]
    · intro hx
      have hx' : ∀ j, ∃ s, s * a j = x j := fun j =>
        Ideal.mem_span_singleton'.mp (hx j (Set.mem_univ _))
      choose s hs using hx'
      refine ⟨A *ᵥ (Q *ᵥ fun k => if h : (k : ℕ) < d then s ⟨k, h⟩ else 0),
        LinearMap.mem_range.mpr ⟨_, rfl⟩, ?_⟩
      simp only [LinearEquiv.coe_coe, matEquiv_apply]
      funext j
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hDv, dif_pos (hlt j)]
      show a j * (if h : (j : ℕ) < d then s ⟨j, h⟩ else 0) = x j
      rw [dif_pos j.isLt, mul_comm]
      exact hs j
  have hT : ∀ x : Fin d → R, (P * A * Q)ᵀ *ᵥ x = Qᵀ *ᵥ (Aᵀ *ᵥ (Pᵀ *ᵥ x)) := by
    intro x
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have e2 : ((Fin d → R) ⧸ zSub A c) ≃ₗ[R]
      ((Fin d → R) ⧸ Submodule.pi Set.univ (fun j => (Ideal.span {b j} : Submodule R R))) := by
    have hPt : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
    refine Submodule.Quotient.equiv _ _ (matEquiv Pᵀ hPt).symm ?_
    ext x
    rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm, Submodule.mem_comap,
      Submodule.mem_pi]
    show (∃ z, Aᵀ *ᵥ ((matEquiv Pᵀ hPt) x) = c • z) ↔ _
    rw [matEquiv_apply]
    constructor
    · rintro ⟨z, hz⟩ j -
      have h1 : (P * A * Q)ᵀ *ᵥ x = c • (Qᵀ *ᵥ z) := by rw [hT, hz, Matrix.mulVec_smul]
      have h2 := congrFun h1 ⟨j, hlt j⟩
      rw [hDt, dif_pos j.isLt, Pi.smul_apply, smul_eq_mul] at h2
      rw [Ideal.mem_span_singleton']
      refine ⟨(Qᵀ *ᵥ z) ⟨j, hlt j⟩, hcancel j _ _ ?_⟩
      rw [mul_comm ((Qᵀ *ᵥ z) _) (b j), ← mul_assoc, hb j]
      exact h2.symm
    · intro hx
      have hx' : ∀ j, ∃ s, s * b j = x j := fun j =>
        Ideal.mem_span_singleton'.mp (hx j (Set.mem_univ _))
      choose s hs using hx'
      have h1 : (P * A * Q)ᵀ *ᵥ x =
          c • (fun k : Fin n => if h : (k : ℕ) < d then s ⟨k, h⟩ else 0) := by
        funext k
        rw [hDt, Pi.smul_apply, smul_eq_mul]
        by_cases h : (k : ℕ) < d
        · rw [dif_pos h, dif_pos h, ← hs ⟨k, h⟩, ← hb ⟨k, h⟩]
          ring
        · rw [dif_neg h, dif_neg h, mul_zero]
      refine ⟨(Q⁻¹)ᵀ *ᵥ (fun k : Fin n => if h : (k : ℕ) < d then s ⟨k, h⟩ else 0), ?_⟩
      calc Aᵀ *ᵥ (Pᵀ *ᵥ x) = (Q⁻¹)ᵀ *ᵥ ((P * A * Q)ᵀ *ᵥ x) := by
            rw [hT, Matrix.mulVec_mulVec (M := (Q⁻¹)ᵀ) (N := Qᵀ), ← Matrix.transpose_mul,
              Matrix.mul_nonsing_inv _ hQ,
              Matrix.transpose_one, Matrix.one_mulVec]
        _ = _ := by rw [h1, Matrix.mulVec_smul]
  have hA1 : HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin)
      (∏ j, v (algebraMap R C (a j))) := hasLen_of_linearEquiv' (hasLen_pi v a) e1.symm
  have hc1 := hasLen_unique hv hc₁ hA1
  refine ⟨∏ j, v (algebraMap R C (b j)), hasLen_of_linearEquiv' (hasLen_pi v b) e2.symm, ?_⟩
  rw [hc1, ← Finset.prod_mul_distrib]
  simp_rw [← map_mul, mul_comm (b _) (a _), hb]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem dualLen : DualLenStatement := by
  intro C _ v R _ _ hv d κ _ _ A c hc hkill c₁ hc₁
  classical
  let e := Fintype.equivFin κ
  let A' : Matrix (Fin d) (Fin (Fintype.card κ)) R := A.submatrix id e.symm
  have hmv : ∀ t : Fin (Fintype.card κ) → R, A' *ᵥ t = A *ᵥ (t ∘ e) := by
    intro t
    funext i
    simp only [Matrix.mulVec, dotProduct]
    exact (Fintype.sum_equiv e (fun j => A i j * t (e j)) _ (fun j => by simp [A'])).symm
  have hmv' : ∀ y : Fin d → R, A'ᵀ *ᵥ y = (Aᵀ *ᵥ y) ∘ e.symm := fun y => by funext k; rfl
  have hrange : LinearMap.range A'.mulVecLin = LinearMap.range A.mulVecLin := by
    ext x
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t ∘ e, (hmv t).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨t ∘ e.symm, ?_⟩
      rw [hmv]
      congr 1
      funext j
      simp
  have hz : zSub A' c = zSub A c := by
    ext y
    show (∃ z, A'ᵀ *ᵥ y = c • z) ↔ (∃ z, Aᵀ *ᵥ y = c • z)
    rw [hmv']
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ e, ?_⟩
      funext j
      have h1 := congrFun hz (e j)
      simpa using h1
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ e.symm, ?_⟩
      rw [hz]
      rfl
  have hk : ∀ w : Fin d → R, ∃ t, A' *ᵥ t = c • w := by
    intro w
    obtain ⟨t, ht⟩ := hkill w
    have h1 : (t ∘ e.symm) ∘ e = t := by funext j; simp
    exact ⟨t ∘ e.symm, by rw [hmv, h1, ht]⟩
  have hc₁' : HasLen v R ((Fin d → R) ⧸ LinearMap.range A'.mulVecLin) c₁ := by
    rw [hrange]; exact hc₁
  obtain ⟨y, hy, hyc⟩ := dualLen_fin hv A' c hc hk hc₁'
  rw [hz] at hy
  exact ⟨y, hy, hyc⟩

theorem lenId : LenIdStatement := lenId_of_B (lenIdB_of dualLen)

end ReciprocityTheory.PGsh.Up
