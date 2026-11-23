import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TripleNe

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open Matrix in
private theorem conj_form {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] {J A A' h : Matrix ι ι R} {ν : R}
    (e1 : A * A' = 1) (hA : Aᵀ * J * A = ν • J) (hh : hᵀ * J * h = J) :
    (A * h * A')ᵀ * J * (A * h * A') = J := by
  have e2 : A'ᵀ * Aᵀ = 1 := by rw [← transpose_mul, e1, transpose_one]
  calc (A * h * A')ᵀ * J * (A * h * A') = A'ᵀ * (hᵀ * (Aᵀ * J * A) * h) * A' := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = A'ᵀ * (Aᵀ * J * A) * A' := by
        rw [hA, mul_smul_comm, smul_mul_assoc, hh]
    _ = (A'ᵀ * Aᵀ) * J * (A * A') := by simp only [Matrix.mul_assoc]
    _ = J := by rw [e1, e2, one_mul, mul_one]

private theorem triple_ne {R ι : Type} [CommRing R] [Fintype ι] {A Y B : Matrix ι ι R} {a b : ι}
    (hab : (A * Y * B) a b ≠ 0) : ∃ c d, A a c ≠ 0 ∧ Y c d ≠ 0 ∧ B d b ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qk1.triple_ne hab

private theorem blk_inv {R ι κ : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (blk : ι → κ) {h h' : Matrix ι ι R}
    (e1 : h * h' = 1) (e2 : h' * h = 1) (hb : ∀ a b, blk a ≠ blk b → h a b = 0) :
    ∀ a b, blk a ≠ blk b → h' a b = 0 := by
  classical
  intro a b hab
  set E : Matrix ι ι R := Matrix.diagonal fun x => if blk x = blk a then 1 else 0 with hE
  have h1 : E * h = h * E := by
    ext x y
    rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hxy : blk x = blk y
    · rw [hxy, mul_comm]
    · rw [hb x y hxy, mul_zero, zero_mul]
  have h2 : h' * E = E * h' := by
    calc h' * E = h' * (E * h) * h' := by rw [mul_assoc, mul_assoc, e1, mul_one]
      _ = E * h' := by rw [h1, ← mul_assoc, e2, one_mul]
  have h3 := congrFun (congrFun h2 a) b
  rw [hE, Matrix.diagonal_mul, Matrix.mul_diagonal, if_neg (Ne.symm hab), if_pos rfl, mul_zero, one_mul] at h3
  exact h3.symm

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

theorem UpperTheory.V.Alg.hh_group :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w) (R : Type) [CommRing R] [Algebra O R] [IsCO O R],
      Φ.HH (1 : Matrix ι ι R) ∧ (∀ h h' : Matrix ι ι R, Φ.HH h → Φ.HH h' → Φ.HH (h * h')) ∧ (∀ h : Matrix ι ι R, Φ.HH h → ∃ h', Φ.HH h' ∧ h * h' = 1 ∧ h' * h = 1) ∧
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (h : Matrix ι ι R), Φ.HH h → Φ.HH (h.map f)) ∧
      (∀ (Γ : Type) [Group Γ] (r0 : Γ →* Matrix ι ι O), Φ.Normalises r0 → ∀ (s : Γ) (h : Matrix ι ι R), Φ.HH h → Φ.HH ((r0 s).map (algebraMap O R) * h * (r0 s⁻¹).map (algebraMap O R))) ∧
      ∀ (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R), Φ.HH h → Φ.HH (Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b) := by
  intro O _ _ ι X _ _ _ w Φ R _ _ _
  refine ⟨⟨by simp, fun a b hab => Matrix.one_apply_ne fun e => hab (by rw [e]), by simp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro h h' ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨?_, fun a b hab => ?_, by rw [map_mul_alg, a3, b3, one_mul]⟩
    · calc (h * h').transpose * Φ.JR R * (h * h') = h'.transpose * (h.transpose * Φ.JR R * h) * h' := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = Φ.JR R := by rw [a1, b1]
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : Φ.blk a = Φ.blk c
      · rw [b2 c b (hc ▸ hab), mul_zero]
      · rw [a2 a c hc, zero_mul]
  · rintro h ⟨a1, a2, a3⟩
    have hJ : IsUnit (Φ.JR R) := Φ.unit.map (algebraMap O R).mapMatrix
    obtain ⟨K, hK⟩ := hJ.exists_left_inv
    have e2 : (K * h.transpose * Φ.JR R) * h = 1 := by
      rw [mul_assoc K, mul_assoc K, a1, hK]
    generalize K * h.transpose * Φ.JR R = h' at e2
    have e1 : h * h' = 1 := mul_eq_one_comm.1 e2
    refine ⟨h', ⟨?_, blk_inv Φ.blk e1 e2 a2, ?_⟩, e1, e2⟩
    · have := conj_form (h := h) (ν := (1 : R)) e1 (by rw [a1, one_smul]) a1
      calc h'.transpose * Φ.JR R * h' = h'.transpose * (h.transpose * Φ.JR R * h) * h' := by rw [a1]
        _ = (h * h').transpose * Φ.JR R * (h * h') := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = Φ.JR R := by rw [e1]; simp
    · have := congrArg (fun A : Matrix ι ι R => A.map (res O R)) e1
      simp only [map_mul_alg, a3, one_mul] at this
      rw [this]; simp
  · rintro R' _ _ _ f h ⟨a1, a2, a3⟩
    have hJ : Φ.JR R' = (Φ.JR R).map f := by
      ext a b; simp [FormData.JR]
    refine ⟨?_, fun a b hab => by simp [a2 a b hab], ?_⟩
    · rw [hJ, ← Matrix.transpose_map, ← map_mul_alg, ← map_mul_alg, a1]
    · rw [← a3]
      ext a b
      simp only [Matrix.map_apply, res_map]
  · rintro Γ _ r0 ⟨h1, ⟨π, h2⟩, -⟩ s h ⟨a1, a2, a3⟩
    have e1 : (r0 s).map (algebraMap O R) * (r0 s⁻¹).map (algebraMap O R) = 1 := by
      rw [← Matrix.map_mul, ← map_mul, mul_inv_cancel, map_one]; simp
    refine ⟨?_, fun a b hab => ?_, ?_⟩
    · obtain ⟨ν, hν⟩ := h1 s
      refine conj_form (ν := algebraMap O R ν) e1 ?_ a1
      have hO : Φ.JR O = Φ.J := by ext a b; simp [FormData.JR]
      rw [hO] at hν
      rw [FormData.JR, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hν]
      ext a b; simp
    · by_contra hne
      obtain ⟨c, d, k1, k2, k3⟩ := triple_ne hne
      have k1' : r0 s a c ≠ 0 := fun e => k1 (by simp [e])
      have k3' : r0 s⁻¹ d b ≠ 0 := fun e => k3 (by simp [e])
      have k4 : Φ.blk c = Φ.blk d := by_contra fun n => k2 (a2 c d n)
      apply hab
      rw [h2 s a c k1', k4, h2 s⁻¹ d b k3', map_inv]
      simp
    · rw [map_mul_alg, map_mul_alg, a3, mul_one, ← map_mul_alg, e1]; simp
  · rintro t h ⟨a1, a2, a3⟩
    refine ⟨?_, fun a b hab => by simp [a2 a b hab], ?_⟩
    · have e : (Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b) =
          Matrix.diagonal (fun a => (t (Multiplicative.ofAdd (w a)) : R)) * h *
            Matrix.diagonal (fun a => (t (Multiplicative.ofAdd (-w a)) : R)) := by
        ext a b
        rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, sub_eq_add_neg, ofAdd_add, map_mul,
          Units.val_mul]
        ring
      rw [e]
      refine conj_form (ν := (t (Multiplicative.ofAdd Φ.c) : R)) ?_ ?_ a1
      · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext a
        rw [← Units.val_mul, ← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one, Units.val_one]
      · ext a b
        rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
        by_cases hJ : Φ.J a b = 0
        · simp [FormData.JR, hJ]
        · rw [← Φ.hw a b hJ, ofAdd_add, map_mul, Units.val_mul]
          ring
    · ext a b
      have k := congrFun (congrFun a3 a) b
      rw [Matrix.map_apply] at k
      rw [Matrix.map_apply, Matrix.of_apply, map_mul, k]
      by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.one_apply_ne hab]
