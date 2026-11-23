import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryCommMulEqOfGram

open Matrix Finset

noncomputable section

namespace GlobalTheory.RealIwasawa

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_isometry_comp {S : Type*} [AddCommGroup S] [Module ℂ S] (f h : S →ₗ[ℂ] E)
    (hn : ∀ s, ‖f s‖ = ‖h s‖) : ∃ φ : E →ₗᵢ[ℂ] E, ∀ s, φ (f s) = h s := by
  obtain ⟨r, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  have hr' : ∀ x : LinearMap.range f, f (r x) = x := fun x => by
    have := congrArg Subtype.val (LinearMap.congr_fun hr x)
    simpa using this
  let L : LinearMap.range f →ₗᵢ[ℂ] E :=
    { toLinearMap := h.comp r
      norm_map' := fun x => by
        simp only [LinearMap.comp_apply]
        rw [← hn, hr']; rfl }
  refine ⟨L.extend, fun s => ?_⟩
  have h1 := L.extend_apply ⟨f s, LinearMap.mem_range_self f s⟩
  refine h1.trans ?_
  have h2 : f (r ⟨f s, LinearMap.mem_range_self f s⟩ - s) = 0 := by
    rw [map_sub, hr', sub_self]
  have h3 := hn (r ⟨f s, LinearMap.mem_range_self f s⟩ - s)
  rw [h2, norm_zero, eq_comm, norm_eq_zero, map_sub, sub_eq_zero] at h3
  exact h3

theorem exists_isometry_flag (W W' : ℕ → Submodule ℂ E) (h0 : W 0 = ⊥) (hW : Monotone W) (hW' : Monotone W')
    (hd : ∀ i, Module.finrank ℂ (W i) = Module.finrank ℂ (W' i)) (l : ℕ) :
    ∃ φ : E →ₗᵢ[ℂ] E, ∀ i ≤ l, ∀ y ∈ W i, φ y ∈ W' i := by
  induction l with
  | zero =>
    refine ⟨LinearIsometry.id, fun i hi y hy => ?_⟩
    obtain rfl : i = 0 := by omega
    rw [h0, Submodule.mem_bot] at hy
    simp [hy]
  | succ l ih =>
    obtain ⟨φ, hφ⟩ := ih
    have e1 := Submodule.finrank_add_inf_finrank_orthogonal (hW (Nat.le_succ l))
    have e2 := Submodule.finrank_add_inf_finrank_orthogonal (hW' (Nat.le_succ l))
    have hD : Module.finrank ℂ ((W l)ᗮ ⊓ W (l + 1) : Submodule ℂ E) =
        Module.finrank ℂ ((W' l)ᗮ ⊓ W' (l + 1) : Submodule ℂ E) := by
      have := hd l
      have := hd (l + 1)
      simp only [Nat.succ_eq_add_one] at e1 e2
      omega
    let ψ := ((stdOrthonormalBasis ℂ ((W l)ᗮ ⊓ W (l + 1) : Submodule ℂ E)).reindex (finCongr hD)).repr.trans
      (stdOrthonormalBasis ℂ ((W' l)ᗮ ⊓ W' (l + 1) : Submodule ℂ E)).repr.symm
    obtain ⟨φ', hφ'⟩ := exists_isometry_comp
      ((W l).subtype.coprod ((W l)ᗮ ⊓ W (l + 1) : Submodule ℂ E).subtype)
      ((φ.toLinearMap.comp (W l).subtype).coprod
        (((W' l)ᗮ ⊓ W' (l + 1) : Submodule ℂ E).subtype.comp ψ.toLinearEquiv.toLinearMap)) (by
      rintro ⟨w, d⟩
      have a1 : inner ℂ (w : E) (d : E) = 0 := (Submodule.mem_orthogonal _ _).1 d.2.1 _ w.2
      have a2 : inner ℂ (φ w) ((ψ d : _) : E) = 0 :=
        (Submodule.mem_orthogonal _ _).1 (ψ d).2.1 _ (hφ l le_rfl _ w.2)
      have b1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ a1
      have b2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ a2
      have c1 : ‖((ψ d : _) : E)‖ = ‖(d : E)‖ := ψ.norm_map d
      rw [c1, φ.norm_map, ← b1] at b2
      exact ((mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 b2).symm)
    have k : ∀ (w : W l) (d : ((W l)ᗮ ⊓ W (l + 1) : Submodule ℂ E)), φ' (w + d) = φ w + ψ d :=
      fun w d => hφ' (w, d)
    refine ⟨φ', fun i hi y hy => ?_⟩
    rcases Nat.lt_or_ge i (l + 1) with hlt | hge
    · have hil : i ≤ l := by omega
      have := k ⟨y, hW hil hy⟩ 0
      simp only [Submodule.coe_zero, add_zero, map_zero] at this
      rw [this]; exact hφ i hil y hy
    · obtain rfl : i = l + 1 := by omega
      rw [← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hW (Nat.le_succ l))] at hy
      obtain ⟨w, hw, d, hd', rfl⟩ := Submodule.mem_sup.1 hy
      have := k ⟨w, hw⟩ ⟨d, hd'⟩
      simp only at this
      rw [this]
      exact add_mem (hW' (Nat.le_succ l) (hφ l le_rfl w hw)) (ψ ⟨d, hd'⟩).2.2

end Inner

section Mat

variable {n : ℕ}

theorem exists_unitary_of_isometry (φ : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ ∀ y, U *ᵥ y = (φ (WithLp.toLp 2 y)).ofLp := by
  have hU : ∀ y, (Matrix.toEuclideanLin.symm φ.toLinearMap) *ᵥ y = (φ (WithLp.toLp 2 y)).ofLp := fun y => by
    have := Matrix.toLpLin_apply 2 2 (Matrix.toEuclideanLin.symm φ.toLinearMap) (WithLp.toLp 2 y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact (congrArg WithLp.ofLp this).symm
  refine ⟨_, ?_, hU⟩
  ext a b
  have h := φ.inner_map_map (WithLp.toLp 2 (Pi.single a 1)) (WithLp.toLp 2 (Pi.single b 1))
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct, ← hU, ← hU] at h
  simp only [Matrix.mulVec_single_one] at h
  rw [Matrix.mul_apply, Matrix.one_apply]
  convert h using 1
  · simp [dotProduct, mul_comm]
  · simp [Pi.single_apply]

theorem exists_unitary_flag (W W' : ℕ → Submodule ℂ (Fin n → ℂ)) (h0 : W 0 = ⊥) (hW : Monotone W)
    (hW' : Monotone W') (hd : ∀ i, Module.finrank ℂ (W i) = Module.finrank ℂ (W' i)) (l : ℕ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ ∀ i ≤ l, ∀ y ∈ W i, U *ᵥ y ∈ W' i := by
  let e := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  obtain ⟨φ, hφ⟩ := exists_isometry_flag (E := EuclideanSpace ℂ (Fin n)) (fun i => (W i).map e.toLinearMap)
    (fun i => (W' i).map e.toLinearMap) (by simp [h0]) (fun i k hik => Submodule.map_mono (hW hik))
    (fun i k hik => Submodule.map_mono (hW' hik))
    (fun i => by rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, hd]) l
  obtain ⟨U, hU, hU'⟩ := exists_unitary_of_isometry φ
  refine ⟨U, hU, fun i hi y hy => ?_⟩
  obtain ⟨z, hz, hz'⟩ := hφ i hi (e y) ⟨y, hy, rfl⟩
  rw [hU']
  have : (φ (WithLp.toLp 2 y)).ofLp = z := (congrArg WithLp.ofLp hz').symm
  rw [this]; exact hz

theorem exists_proj (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, Pᴴ = P ∧ (∀ y, P *ᵥ y ∈ W) ∧ ∀ y ∈ W, P *ᵥ y = y := by
  let e := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let W' : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := W.map e.toLinearMap
  have hU : ∀ y, (Matrix.toEuclideanLin.symm W'.starProjection.toLinearMap) *ᵥ y =
      (W'.starProjection (WithLp.toLp 2 y)).ofLp := fun y => by
    have := Matrix.toLpLin_apply 2 2 (Matrix.toEuclideanLin.symm W'.starProjection.toLinearMap) (WithLp.toLp 2 y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact (congrArg WithLp.ofLp this).symm
  refine ⟨Matrix.toEuclideanLin.symm W'.starProjection.toLinearMap, ?_, fun y => ?_, fun y hy => ?_⟩
  · apply Matrix.isSymmetric_toEuclideanLin_iff.1
    rw [LinearEquiv.apply_symm_apply]
    exact W'.starProjection_isSymmetric
  · obtain ⟨z, hz, hz'⟩ := W'.starProjection_apply_mem (WithLp.toLp 2 y)
    rw [hU, ← hz']; exact hz
  · rw [hU, Submodule.starProjection_eq_self_iff.2 (show WithLp.toLp 2 y ∈ W' from ⟨y, hy, rfl⟩)]

end Mat

section Ring

variable {A : Type*} [Ring A]

theorem exists_diagonal_blocks (P : ℕ → A) (h0 : P 0 = 0) (hl : ∀ i k, i ≤ k → P i * P k = P i)
    (hr : ∀ i k, i ≤ k → P k * P i = P i) (p q : A) (hqp : q * p = 1) (hp : ∀ i, P i * p * P i = p * P i)
    (hq : ∀ i, P i * q * P i = q * P i) (a : ℕ) :
    ∃ α β : A, β * α = P a ∧ (∀ i, P i * α = α * P i) ∧ (∀ i, P i * β = β * P i) ∧ α * P a = α ∧ β * P a = β ∧
      ∀ i < a, P i * ((p - α) * P (i + 1)) = (p - α) * P (i + 1) := by
  let Q : ℕ → A := fun i => P (i + 1) - P i
  have hQP : ∀ i k, Q i * P k = if i < k then Q i else 0 := fun i k => by
    simp only [Q, sub_mul]
    split_ifs with h
    · rw [hl _ _ h, hl _ _ h.le]
    · rw [hr k (i + 1) (by omega), hr k i (by omega), sub_self]
  have hPQ : ∀ i k, P k * Q i = if i < k then Q i else 0 := fun i k => by
    simp only [Q, mul_sub]
    split_ifs with h
    · rw [hr _ _ h, hr _ _ h.le]
    · rw [hl k (i + 1) (by omega), hl k i (by omega), sub_self]
  have hQQ : ∀ i k, Q i * Q k = if i = k then Q i else 0 := fun i k => by
    have : Q i * Q k = Q i * P (k + 1) - Q i * P k := by simp only [Q, mul_sub]
    rw [this, hQP, hQP]
    split_ifs <;> first | omega | simp
  have hc : ∀ (x : A) k, P k * ∑ i ∈ range a, Q i * x * Q i = (∑ i ∈ range a, Q i * x * Q i) * P k := fun x k => by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← mul_assoc, hPQ, mul_assoc _ (Q i) (P k), hQP]
    split_ifs <;> simp
  have ht : ∀ x : A, (∑ i ∈ range a, Q i * x * Q i) * P a = ∑ i ∈ range a, Q i * x * Q i := fun x => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_assoc _ (Q i), hQP, if_pos (Finset.mem_range.1 hi)]
  have hs : ∀ (x : A) k, k < a → (∑ i ∈ range a, Q i * x * Q i) * Q k = Q k * x * Q k := fun x k hk => by
    rw [Finset.sum_mul, Finset.sum_eq_single k]
    · rw [mul_assoc _ (Q k), hQQ, if_pos rfl]
    · intro i _ hik
      rw [mul_assoc _ (Q i), hQQ, if_neg hik, mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 hk) h
  have hz : ∀ x : A, (∀ i, P i * x * P i = x * P i) → ∀ i, Q i * x * P i = 0 := fun x hx i => by
    rw [mul_assoc, ← hx, ← mul_assoc, ← mul_assoc, hQP, if_neg (lt_irrefl _), zero_mul, zero_mul]
  refine ⟨∑ i ∈ range a, Q i * p * Q i, ∑ i ∈ range a, Q i * q * Q i, ?_, hc p, hc q, ht p, ht q, fun i hi => ?_⟩
  · have := Finset.sum_range_sub P a
    rw [h0, sub_zero] at this
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← mul_assoc, ← mul_assoc, hs q i (Finset.mem_range.1 hi)]
    have e1 : Q i * q * Q i = Q i * q * P (i + 1) := by
      conv_lhs => rw [show Q i * q * Q i = Q i * q * P (i + 1) - Q i * q * P i by simp only [Q, mul_sub]]
      rw [hz q hq, sub_zero]
    have e2 : P (i + 1) * p * Q i = p * Q i := by
      have : Q i = P (i + 1) * Q i := by rw [hPQ, if_pos (Nat.lt_succ_self i)]
      rw [this, ← mul_assoc, hp, mul_assoc]
    rw [e1, mul_assoc (Q i * q), mul_assoc (Q i * q), e2, mul_assoc, ← mul_assoc q, hqp, one_mul, hQQ, if_pos rfl]
  · have e0 : ∀ x : A, x * P (i + 1) = x * Q i + x * P i := fun x => by simp only [Q, mul_sub, sub_add_cancel]
    have e1 : P i * ((∑ i ∈ range a, Q i * p * Q i) * P (i + 1)) = (∑ i ∈ range a, Q i * p * Q i) * P i := by
      rw [← mul_assoc, hc, mul_assoc, hl _ _ (Nat.le_succ i)]
    have e2 : p * P (i + 1) = Q i * p * Q i + P i * (p * P (i + 1)) := by
      have : Q i * p * P (i + 1) = Q i * p * Q i := by rw [e0, hz p hp, add_zero]
      rw [← this, ← mul_assoc, ← add_mul, ← add_mul]
      simp only [Q, sub_add_cancel, hp]
    rw [sub_mul, mul_sub, e1, e0 (∑ i ∈ range a, Q i * p * Q i), hs p i hi]
    conv_rhs => rw [e2]
    abel

variable [StarRing A]

theorem exists_levi (J T p q α β : A) (hJ : star J = J) (hJJ : J * J = 1) (hT : star T = T) (hTT : T * T = T)
    (hiso : T * J * T = 0) (hp : star p * J * p = J) (hpq : p * q = 1) (hpT : T * p * T = p * T)
    (hqT : T * q * T = q * T) (hβα : β * α = T) (h1 : T * α = α) (h2 : α * T = α) (h3 : T * β = β)
    (h4 : β * T = β) :
    ∃ m : A, star m * J * m = J ∧ m * T = α ∧ star m * T = star α ∧ J * star m * J * T = β ∧
      T * ((p - m) * (J * star m * J) * (1 - J * T * J)) = (p - m) * (J * star m * J) * (1 - J * T * J) := by
  obtain ⟨R, hR⟩ : ∃ R, R = 1 - T - J * T * J := ⟨_, rfl⟩
  have JJ : ∀ x, J * (J * x) = x := fun x => by rw [← mul_assoc, hJJ, one_mul]
  have TT : ∀ x, T * (T * x) = T * x := fun x => by rw [← mul_assoc, hTT]
  have hiso' : T * (J * T) = 0 := by rw [← mul_assoc, hiso]
  have TJT : ∀ x, T * (J * (T * x)) = 0 := fun x => by rw [← mul_assoc, ← mul_assoc, hiso, zero_mul]
  have sR : star R = R := by simp [hR, hJ, hT, mul_assoc]
  have RT : R * T = 0 := by simp [hR, sub_mul, mul_assoc, hTT, hiso']
  have TR : T * R = 0 := by simp [hR, mul_sub, mul_assoc, hTT, TJT]
  have JR : J * R = R * J := by
    simp only [hR, mul_sub, sub_mul, mul_assoc, JJ, hJJ, one_mul, mul_one]; abel
  have RJT : R * (J * T) = 0 := by rw [← mul_assoc, ← JR, mul_assoc, RT, mul_zero]
  have TJR : T * (J * R) = 0 := by rw [JR, ← mul_assoc, TR, zero_mul]
  have RR : R * R = R := by
    conv_lhs => rw [show R * R = R * (1 - T - J * T * J) by rw [← hR]]
    rw [mul_sub, mul_sub, RT, ← mul_assoc, RJT]; simp
  have s1 : star α * T = star α := by rw [← hT, ← star_mul, h1]
  have s2 : T * star α = star α := by rw [← hT, ← star_mul, h2]
  have s3 : star β * T = star β := by rw [← hT, ← star_mul, h3]
  have s4 : T * star β = star β := by rw [← hT, ← star_mul, h4]
  have s5 : star α * star β = T := by rw [← star_mul, hβα, hT]
  have Jp : J * p = star q * J := by
    conv_rhs => rw [← hp, ← mul_assoc, ← mul_assoc, ← star_mul, hpq, star_one, one_mul]
  have Tq : T * star q = T * star q * T := by
    have := congrArg star hqT
    simp only [star_mul, hT] at this
    rw [mul_assoc, this]
  have TJpR : T * (J * (p * R)) = 0 := by
    rw [← mul_assoc J, Jp, mul_assoc, ← mul_assoc T, Tq, mul_assoc, TJR, mul_zero]
  have pR : p * R = T * (p * R) + R * (p * R) := by
    conv_rhs => rw [show R * (p * R) = (1 - T - J * T * J) * (p * R) by rw [← hR]]
    simp only [sub_mul, mul_assoc, TJpR]; simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = R * (p * R) := ⟨_, rfl⟩
  have Rρ : R * ρ = ρ := by rw [hρ, ← mul_assoc, RR]
  have ρR : ρ * R = ρ := by rw [hρ, mul_assoc, mul_assoc, RR]
  have r1 : star ρ * R = star ρ := by rw [← sR, ← star_mul, Rρ]
  have r2 : R * star ρ = star ρ := by rw [← sR, ← star_mul, ρR]
  have ρT : ρ * T = 0 := by rw [← ρR, mul_assoc, RT, mul_zero]
  have ρT' : star ρ * T = 0 := by rw [← r1, mul_assoc, RT, mul_zero]
  have ρJT' : star ρ * (J * T) = 0 := by rw [← r1, mul_assoc, RJT, mul_zero]
  have Tρ : T * ρ = 0 := by rw [← Rρ, ← mul_assoc, TR, zero_mul]
  have TJρ : T * (J * ρ) = 0 := by rw [← Rρ, ← mul_assoc J, ← mul_assoc, TJR, zero_mul]
  have ρJρ : star ρ * (J * ρ) = R * J := by
    have e : star (p * R) * J * (p * R) = R * J := by
      rw [star_mul, sR, mul_assoc, mul_assoc, ← mul_assoc J, ← mul_assoc (star p), ← mul_assoc (star p), hp, JR,
        ← mul_assoc, RR]
    rw [← hρ] at pR
    rw [pR, star_add, star_mul, hT] at e
    have z : ∀ x, star ρ * (J * (T * x)) = 0 := fun x => by
      rw [← mul_assoc J, ← mul_assoc, ρJT', zero_mul]
    simpa only [add_mul, mul_add, mul_assoc, TJT, TJρ, z, mul_zero, zero_add] using e
  have βJT : star β * (J * T) = 0 := by rw [← s3, mul_assoc, hiso', mul_zero]
  have βJT' : β * (J * T) = 0 := by rw [← h4, mul_assoc, hiso', mul_zero]
  have αJT : star α * (J * T) = 0 := by rw [← s1, mul_assoc, hiso', mul_zero]
  obtain ⟨m, hm⟩ : ∃ m, m = α + ρ + J * star β * J := ⟨_, rfl⟩
  have sm : star m = star α + star ρ + J * β * J := by simp [hm, hJ, mul_assoc]
  have mT : m * T = α := by simp [hm, add_mul, mul_assoc, h2, ρT, βJT]
  have Tm : T * star m = star α := by rw [← hT, ← star_mul, mT]
  refine ⟨m, ?_, mT, by simp [sm, add_mul, mul_assoc, s1, ρT', βJT'], ?_, ?_⟩
  · have a1 : star α * (J * α) = 0 := by rw [← h1, ← mul_assoc J, ← mul_assoc, h1, αJT, zero_mul]
    have a2 : star α * (J * ρ) = 0 := by rw [← s1, mul_assoc, TJρ, mul_zero]
    have a3 : star ρ * (J * α) = 0 := by rw [← h1, ← mul_assoc J, ← mul_assoc, ρJT', zero_mul]
    have a4 : star ρ * (star β * J) = 0 := by rw [← s4, mul_assoc, ← mul_assoc, ρT', zero_mul]
    have a5 : β * ρ = 0 := by rw [← h4, mul_assoc, Tρ, mul_zero]
    have a6 : β * (J * (star β * J)) = 0 := by
      rw [← s4, mul_assoc, ← mul_assoc J, ← mul_assoc, βJT', zero_mul]
    have a7 : star α * (star β * J) = T * J := by rw [← mul_assoc, s5]
    rw [sm, hm]
    simp only [add_mul, mul_add, mul_assoc, JJ, a1, a2, a3, a4, a5, a6, a7, hβα, ρJρ, mul_zero]
    simp only [hR, sub_mul, mul_assoc, hJJ, one_mul, mul_one]
    abel
  · simp [sm, add_mul, mul_add, mul_assoc, JJ, αJT, ρJT', h4]
  · have b1 : J * star m * J * (1 - J * T * J) = (T + R) * (J * star m * J * (1 - J * T * J)) := by
      have : J * T * J * (J * star m * J * (1 - J * T * J)) = 0 := by
        simp only [mul_assoc, JJ]
        rw [← mul_assoc T, Tm, mul_sub, JJ, mul_one, mul_sub, ← mul_assoc (star α), s1, sub_self, mul_zero]
      rw [show T + R = 1 - J * T * J by rw [hR]; abel, sub_mul, this, one_mul, sub_zero]
    have αR : α * R = 0 := by rw [← h2, mul_assoc, TR, mul_zero]
    have βJR : star β * (J * R) = 0 := by rw [← s3, mul_assoc, TJR, mul_zero]
    have mR : m * R = ρ := by simp [hm, add_mul, mul_assoc, αR, ρR, βJR]
    have b2 : T * ((p - m) * (T + R)) = (p - m) * (T + R) := by
      rw [← hρ] at pR
      simp only [sub_mul, mul_add, mT, mR, mul_sub, h1, Tρ]
      rw [← mul_assoc T p T, hpT]
      conv_rhs => rw [pR]
      abel
    rw [mul_assoc (p - m), b1, ← mul_assoc (p - m), ← mul_assoc T, b2]

theorem eq_one_of_fix (J T u : A) (hT : star T = T) (hu : u * J * star u = J) (h2 : T * u = T)
    (h3 : T * ((u - 1) * (1 - J * T * J)) = (u - 1) * (1 - J * T * J)) : u = 1 := by
  have s : star u * T = T := by rw [← hT, ← star_mul, hT, h2, hT]
  have e : u * (J * T * J) = J * T * J := by
    conv_lhs => rw [← s]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hu]
  rw [← mul_assoc, mul_sub T, h2, mul_one, sub_self, zero_mul, mul_sub, mul_one, sub_mul, e, one_mul, sub_self,
    sub_zero] at h3
  exact (sub_eq_zero.1 h3.symm)

end Ring

section Main

variable {n : ℕ}

theorem finrank_map_toLin (g h : Matrix (Fin n) (Fin n) ℂ) (hg : h * g = 1) (W : Submodule ℂ (Fin n → ℂ)) :
    Module.finrank ℂ (W.map (Matrix.toLin' g)) = Module.finrank ℂ W := by
  refine (Submodule.equivMapOfInjective _ (fun x y hxy => ?_) W).finrank_eq.symm
  have := congrArg (h *ᵥ ·) hxy
  simpa [Matrix.mulVec_mulVec, hg] using this

theorem inv_stable (g h : Matrix (Fin n) (Fin n) ℂ) (hg : h * g = 1) (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ y ∈ W, g *ᵥ y ∈ W) : ∀ y ∈ W, h *ᵥ y ∈ W := by
  have e : W.map (Matrix.toLin' g) = W :=
    Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact hW y hy) (finrank_map_toLin g h hg W)
  intro y hy
  rw [← e] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  simpa [Matrix.mulVec_mulVec, hg] using hz

theorem proj_mul_eq {W W' : Submodule ℂ (Fin n → ℂ)} {P P' : Matrix (Fin n) (Fin n) ℂ} (h1 : ∀ y, P *ᵥ y ∈ W)
    (h2 : ∀ y ∈ W', P' *ᵥ y = y) {g : Matrix (Fin n) (Fin n) ℂ} (hg : ∀ y ∈ W, g *ᵥ y ∈ W') :
    P' * g * P = g * P := by
  refine Matrix.ext_iff_mulVec.2 fun y => ?_
  simp only [← Matrix.mulVec_mulVec]
  exact h2 _ (hg _ (h1 y))

theorem proj_comm {W : Submodule ℂ (Fin n → ℂ)} {P : Matrix (Fin n) (Fin n) ℂ} (h0 : Pᴴ = P) (h1 : ∀ y, P *ᵥ y ∈ W)
    (h2 : ∀ y ∈ W, P *ᵥ y = y) {g : Matrix (Fin n) (Fin n) ℂ} (hg : ∀ y ∈ W, g *ᵥ y ∈ W)
    (hg' : ∀ y ∈ W, gᴴ *ᵥ y ∈ W) : P * g = g * P := by
  have a := proj_mul_eq h1 h2 hg
  have b := congrArg conjTranspose (proj_mul_eq h1 h2 hg')
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, h0] at b
  rw [← b, ← mul_assoc, a]

theorem proj_mulVec_eq_zero {W : Submodule ℂ (Fin n → ℂ)} {P : Matrix (Fin n) (Fin n) ℂ} (h0 : Pᴴ = P)
    (h1 : ∀ y, P *ᵥ y ∈ W) {z : Fin n → ℂ} (hz : ∀ x ∈ W, star x ⬝ᵥ z = 0) : P *ᵥ z = 0 := by
  funext b
  have := hz _ (h1 (Pi.single b 1))
  rw [Matrix.star_mulVec, h0, ← Matrix.dotProduct_mulVec] at this
  simpa [Pi.star_single] using this

theorem dot_eq_zero_of_proj {W : Submodule ℂ (Fin n → ℂ)} {P : Matrix (Fin n) (Fin n) ℂ} (h0 : Pᴴ = P)
    (h2 : ∀ y ∈ W, P *ᵥ y = y) {z : Fin n → ℂ} (hz : P *ᵥ z = 0) : ∀ x ∈ W, star x ⬝ᵥ z = 0 := fun x hx => by
  rw [← h2 x hx, Matrix.star_mulVec, h0, ← Matrix.dotProduct_mulVec, hz, dotProduct_zero]

variable {ε : Fin n → Bool}

theorem exists_uMat (m : Matrix (Fin n) (Fin n) ℂ) (hm : mᴴ * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε) :
    ∃ g : Formalism.REAL.UJ ε, uMat g = m ∧ uMat g⁻¹ = Formalism.REAL.Jm ε * mᴴ * Formalism.REAL.Jm ε := by
  have h : Formalism.REAL.Jm ε * mᴴ * Formalism.REAL.Jm ε * m = 1 := by
    rw [mul_assoc, mul_assoc, ← mul_assoc mᴴ, hm, Formalism.REAL.Jm_mul_self]
  exact ⟨⟨⟨m, _, mul_eq_one_comm.1 h, h⟩, hm⟩, rfl, rfl⟩

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel]; rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel]; rfl

theorem uMat_form (g : Formalism.REAL.UJ ε) : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2

variable {a : ℕ} {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}

theorem proj_iso (hW : IsIsoFlag ε j W) {T : Matrix (Fin n) (Fin n) ℂ} (h0 : Tᴴ = T)
    (h1 : ∀ y, T *ᵥ y ∈ W (Fin.last a)) : T * Formalism.REAL.Jm ε * T = 0 := by
  refine Matrix.ext_iff_mulVec.2 fun y => ?_
  simp only [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  exact proj_mulVec_eq_zero h0 h1 fun x hx => hW.2.2.2 x hx _ (h1 y)

theorem exists_stab_mul_compact (hW : IsIsoFlag ε j W) (g : Formalism.REAL.UJ ε) :
    ∃ k ∈ maxK ε, ∀ i, ∀ y ∈ W i, uMat (g * k⁻¹) *ᵥ y ∈ W i := by
  let c : ℕ → Fin (a + 1) := fun i => ⟨min i a, by omega⟩
  have hc : Monotone c := fun i k h => Fin.mk_le_mk.2 (by omega)
  have hci : ∀ i : Fin (a + 1), c i = i := fun i => Fin.ext (by simp only [c]; omega)
  obtain ⟨U, hU, hUW⟩ := exists_unitary_flag (fun i => W (c i)) (fun i => (W (c i)).map (Matrix.toLin' (uMat g⁻¹)))
    (by simpa [c] using hW.1) (hW.2.1.comp hc) (fun i k h => Submodule.map_mono (hW.2.1 (hc h)))
    (fun i => (finrank_map_toLin _ _ (uMat_mul_inv g) _).symm) a
  have hgU : ∀ i, ∀ y ∈ W i, (uMat g * U) *ᵥ y ∈ W i := fun i y hy => by
    obtain ⟨z, hz, hz'⟩ := hUW i (by omega) y (by rw [hci]; exact hy)
    rw [← Matrix.mulVec_mulVec, ← hz', Matrix.toLin'_apply, Matrix.mulVec_mulVec, uMat_mul_inv, Matrix.one_mulVec]
    rw [hci] at hz; exact hz
  obtain ⟨T, hT0, hT1, hT2⟩ := exists_proj (W (Fin.last a))
  have hiso := proj_iso hW hT0 hT1
  have e := proj_mul_eq hT1 hT2 (hgU (Fin.last a))
  obtain ⟨V, hV1, hV2, hV3⟩ := GlobalTheory.HCXi.exists_unitary_comm_mul_eq_of_gram (Formalism.REAL.Jm ε)
    (Formalism.REAL.Jm_conjTranspose ε) (Formalism.REAL.Jm_mul_self ε) T (U * T)
    (by rw [conjTranspose_mul, mul_assoc, ← mul_assoc Uᴴ, hU, one_mul]) (by
      have : (U * T)ᴴ * Formalism.REAL.Jm ε * (U * T) =
          (uMat g * U * T)ᴴ * Formalism.REAL.Jm ε * (uMat g * U * T) := by
        conv_lhs => rw [← uMat_form g]
        simp only [conjTranspose_mul, mul_assoc]
      rw [this, ← e, hT0, hiso, mul_assoc T _ T, conjTranspose_mul, hT0, mul_assoc, mul_assoc, ← mul_assoc T,
        ← mul_assoc _ T, hiso]
      simp)
  obtain ⟨k, hk, -⟩ := exists_uMat (ε := ε) V (by rw [mul_assoc, ← hV2, ← mul_assoc, hV1, one_mul])
  refine ⟨k⁻¹, ?_, fun i y hy => ?_⟩
  · have h1 : uMat k⁻¹ = Vᴴ := by
      have := uMat_inv_mul k
      rw [hk] at this
      rw [← mul_one (uMat k⁻¹), ← mul_eq_one_comm.1 hV1, ← mul_assoc, this, one_mul]
    show _ = _
    rw [h1, conjTranspose_conjTranspose, mul_eq_one_comm.1 hV1]
  · have hy' := hT2 y (hW.2.1 (Fin.le_last i) hy)
    have := hgU i y hy
    rw [inv_inv, uMat_mul, hk, ← hy', Matrix.mulVec_mulVec, mul_assoc, hV3, ← mul_assoc, ← Matrix.mulVec_mulVec, hy']
    exact this

theorem exists_unip_mul_levi (hW : IsIsoFlag ε j W) (p : Formalism.REAL.UJ ε) (hp : ∀ i, ∀ y ∈ W i, uMat p *ᵥ y ∈ W i) :
    ∃ m ∈ flagM ε W, p * m⁻¹ ∈ flagN ε W := by
  let c : ℕ → Fin (a + 1) := fun i => ⟨min i a, by omega⟩
  have hc : Monotone c := fun i k h => Fin.mk_le_mk.2 (by omega)
  have hci : ∀ i : Fin (a + 1), c i = i := fun i => Fin.ext (by simp only [c]; omega)
  have hca : c a = Fin.last a := hci (Fin.last a)
  choose P hP0 hP1 hP2 using fun i => exists_proj (W i)
  have hr : ∀ i k, i ≤ k → P k * P i = P i := fun i k h => by
    simpa using proj_mul_eq (g := 1) (hP1 i) (hP2 k) (fun y hy => by simpa using hW.2.1 h hy)
  have hl : ∀ i k, i ≤ k → P i * P k = P i := fun i k h => by
    have := congrArg conjTranspose (hr i k h)
    rwa [conjTranspose_mul, hP0, hP0] at this
  have hq := fun i => inv_stable _ _ (uMat_inv_mul p) (W i) (hp i)
  obtain ⟨α, β, hβα, hα, hβ, hαT, hβT, hN⟩ := exists_diagonal_blocks (fun i => P (c i))
    (by
      refine Matrix.ext_iff_mulVec.2 fun y => ?_
      have := hP1 0 y
      rw [hW.1, Submodule.mem_bot] at this
      simpa [c] using this)
    (fun i k h => hl _ _ (hc h)) (fun i k h => hr _ _ (hc h)) (uMat p) (uMat p⁻¹) (uMat_inv_mul p)
    (fun i => proj_mul_eq (hP1 _) (hP2 _) (hp _)) (fun i => proj_mul_eq (hP1 _) (hP2 _) (hq _)) a
  replace hα : ∀ i, P i * α = α * P i := fun i => by simpa only [hci] using hα i
  replace hβ : ∀ i, P i * β = β * P i := fun i => by simpa only [hci] using hβ i
  rw [hca] at hβα hαT hβT
  obtain ⟨m, hm, hmT, hmT', hmβ, hmN⟩ := exists_levi (Formalism.REAL.Jm ε) (P (Fin.last a)) (uMat p) (uMat p⁻¹) α β
    (Formalism.REAL.Jm_conjTranspose ε) (Formalism.REAL.Jm_mul_self ε) (hP0 _) (hl _ _ le_rfl) (proj_iso hW (hP0 _) (hP1 _))
    (uMat_form p) (uMat_mul_inv p) (proj_mul_eq (hP1 _) (hP2 _) (hp _)) (proj_mul_eq (hP1 _) (hP2 _) (hq _)) hβα
    (by rw [hα, hαT]) hαT (by rw [hβ, hβT]) hβT
  simp only [star_eq_conjTranspose] at hm hmT' hmβ hmN
  obtain ⟨g, rfl, hg⟩ := exists_uMat m hm
  rw [← hg] at hmβ hmN
  have hu : ∀ y, uMat (p * g⁻¹) *ᵥ y - y = ((uMat p - uMat g) * uMat g⁻¹) *ᵥ y := fun y => by
    rw [sub_mul, uMat_mul_inv, Matrix.sub_mulVec, Matrix.one_mulVec, uMat_mul]
  have key : ∀ (x γ : Matrix (Fin n) (Fin n) ℂ), x * P (Fin.last a) = γ → ∀ i, x * P i = γ * P i := fun x γ h i => by
    rw [← h, mul_assoc, hr _ _ (Fin.le_last i)]
  refine ⟨g, fun i y hy => ⟨?_, ?_⟩, fun i y hy => ?_, fun y hy => ?_⟩
  · rw [← hP2 i y hy, Matrix.mulVec_mulVec, key _ _ hmT, ← hα, ← Matrix.mulVec_mulVec]
    exact hP1 _ _
  · have := congrArg conjTranspose (hα i)
    simp only [conjTranspose_mul, hP0] at this
    rw [← hP2 i y hy, Matrix.mulVec_mulVec, key _ _ hmT', this, ← Matrix.mulVec_mulVec]
    exact hP1 _ _
  · have h := hN i i.2
    have c1 : c i = i.castSucc := hci i.castSucc
    have c2 : c (i + 1) = i.succ := hci i.succ
    simp only [c1, c2] at h
    have e : (uMat p - uMat g) * P i.succ = (uMat p - α) * P i.succ := by rw [sub_mul, sub_mul, key _ _ hmT]
    rw [hu, ← hP2 _ y hy, Matrix.mulVec_mulVec, mul_assoc, key _ _ hmβ, ← hβ, ← mul_assoc, e, ← h, mul_assoc,
      ← Matrix.mulVec_mulVec]
    exact hP1 _ _
  · have hz := proj_mulVec_eq_zero (hP0 _) (hP1 _) hy
    have hy' : (1 - Formalism.REAL.Jm ε * P (Fin.last a) * Formalism.REAL.Jm ε) *ᵥ y = y := by
      simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hz]; simp
    rw [hu, ← hy', Matrix.mulVec_mulVec, ← hmN, ← Matrix.mulVec_mulVec]
    exact hP1 _ _

theorem eq_one_of_mul_mem_compact (hW : IsIsoFlag ε j W) (u : Formalism.REAL.UJ ε) (hu : u ∈ flagN ε W)
    (m : Formalism.REAL.UJ ε) (hm : m ∈ flagM ε W) (hk : u * m ∈ maxK ε) : u = 1 := by
  choose P hP0 hP1 hP2 using fun i => exists_proj (W i)
  have hl : ∀ i k, i ≤ k → P i * P k = P i := fun i k h => by
    have : P k * P i = P i := by
      simpa using proj_mul_eq (g := 1) (hP1 i) (hP2 k) (fun y hy => by simpa using hW.2.1 h hy)
    have := congrArg conjTranspose this
    rwa [conjTranspose_mul, hP0, hP0] at this
  have huW : ∀ i, ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := fun i => by
    refine Fin.cases (fun y hy => ?_) (fun i y hy => ?_) i
    · rw [hW.1, Submodule.mem_bot] at hy
      simp [hy]
    · simpa using add_mem (hW.2.1 (Fin.castSucc_le_succ i) (hu.1 i y hy)) hy
  have hkW : ∀ i, ∀ y ∈ W i, uMat (u * m) *ᵥ y ∈ W i := fun i y hy => by
    rw [uMat_mul, ← Matrix.mulVec_mulVec]
    exact huW i _ (hm i y hy).1
  have hc : ∀ i, P i * uMat u = uMat u * P i := fun i => by
    have h1 := proj_comm (hP0 i) (hP1 i) (hP2 i) (hkW i) (inv_stable _ _ hk _ (hkW i))
    have h2 := proj_comm (hP0 i) (hP1 i) (hP2 i) (fun y hy => (hm i y hy).1) (fun y hy => (hm i y hy).2)
    rw [uMat_mul, mul_assoc, ← h2, ← mul_assoc, ← mul_assoc] at h1
    have := congrArg (· * uMat m⁻¹) h1
    simpa only [mul_assoc, uMat_mul_inv, mul_one] using this
  have hfix : ∀ i, P i * (uMat u - 1) = 0 := fun i => by
    induction i using Fin.induction with
    | zero =>
      refine Matrix.ext_iff_mulVec.2 fun y => ?_
      have := hP1 0 ((uMat u - 1) *ᵥ y)
      rw [hW.1, Submodule.mem_bot] at this
      simpa using this
    | succ i ih =>
      have := proj_mul_eq (g := uMat u - 1) (hP1 i.succ) (hP2 i.castSucc)
        (fun y hy => by simpa [Matrix.sub_mulVec] using hu.1 i y hy)
      rw [ih, zero_mul, sub_mul, ← hc, one_mul] at this
      rw [mul_sub, mul_one, ← this]
  have hiso := proj_iso hW (hP0 _) (hP1 _)
  have h1 : uMat u = 1 := by
    refine eq_one_of_fix (Formalism.REAL.Jm ε) (P (Fin.last a)) _ (hP0 _) ?_ ?_ ?_
    · obtain ⟨g, hg, hg'⟩ := exists_uMat _ (uMat_form u)
      have := uMat_mul_inv g
      rw [hg, hg'] at this
      have := congrArg (· * Formalism.REAL.Jm ε) this
      simpa only [mul_assoc, Formalism.REAL.Jm_mul_self, mul_one, one_mul, star_eq_conjTranspose] using this
    · have := hfix (Fin.last a)
      rwa [mul_sub, mul_one, sub_eq_zero] at this
    · refine Matrix.ext_iff_mulVec.2 fun y => ?_
      simp only [← Matrix.mulVec_mulVec]
      refine hP2 _ _ ?_
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      refine hu.2 _ (dot_eq_zero_of_proj (hP0 _) (hP2 _) ?_)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_sub, ← mul_assoc, ← mul_assoc, mul_assoc (P _) _ (Formalism.REAL.Jm ε),
        Formalism.REAL.Jm_mul_self, mul_one, mul_one, hl _ _ le_rfl, sub_self, Matrix.zero_mulVec]
  exact Subtype.ext (Units.ext h1)

end Main

theorem iwasawa : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ g : Formalism.REAL.UJ ε, ∃ u ∈ flagN ε W, ∃ m ∈ flagM ε W, ∃ k ∈ maxK ε, g = u * m * k) ∧
      ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, u * m ∈ maxK ε → u = 1 := by
  intro n ε a j W hW
  refine ⟨fun g => ?_, eq_one_of_mul_mem_compact hW⟩
  obtain ⟨k, hk, hp⟩ := exists_stab_mul_compact hW g
  obtain ⟨m, hm, hu⟩ := exists_unip_mul_levi hW _ hp
  exact ⟨_, hu, m, hm, k, hk, by group⟩

end GlobalTheory.RealIwasawa
