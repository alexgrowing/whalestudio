import Mathlib

open Polynomial Matrix

namespace GlobalTheory
namespace CofactorOrder

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem exists_diag (M : Matrix n n K) :
    ∃ (P Q : Matrix n n K) (D : n → K), P.det = 1 ∧ Q.det = 1 ∧ P * M * Q = diagonal D := by
  obtain ⟨L, L', D, hL⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M
  have hdet : ∀ T : List (TransvectionStruct n K),
      (T.map TransvectionStruct.toMatrix).prod.det = 1 := by
    intro T
    induction T with
    | nil => simp
    | cons t T ih => rw [List.map_cons, List.prod_cons, det_mul, ih, TransvectionStruct.det, one_mul]
  exact ⟨_, _, D, hdet L, hdet L', hL⟩

theorem mulVec_eq_zero_of_det {P : Matrix n n K} (hP : P.det = 1) {v : n → K}
    (h : P *ᵥ v = 0) : v = 0 := by
  have hu : IsUnit P := (isUnit_iff_isUnit_det P).mpr (by rw [hP]; exact isUnit_one)
  exact (mulVec_injective_iff_isUnit.mpr hu) (by rw [h, mulVec_zero])

theorem ker_eq_bot_of_det {P : Matrix n n K} (hP : P.det = 1) :
    LinearMap.ker P.mulVecLin = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr fun v hv => ?_
  rw [mulVecLin_apply] at hv
  exact mulVec_eq_zero_of_det hP hv

theorem card_le_finrank {M P Q : Matrix n n K} {D : n → K} [DecidablePred fun i => D i = 0]
    (hP : P.det = 1) (hQ : Q.det = 1) (h : P * M * Q = diagonal D) :
    Fintype.card {i // D i = 0} ≤ Module.finrank K (LinearMap.ker M.mulVecLin) := by
  set V := LinearMap.ker M.mulVecLin
  have hmem : ∀ i : {i // D i = 0}, Q *ᵥ Pi.single i.1 (1 : K) ∈ V := by
    intro i
    rw [LinearMap.mem_ker, mulVecLin_apply]
    apply mulVec_eq_zero_of_det hP
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, h]
    funext k
    rw [mulVec_diagonal]
    by_cases hk : k = i.1
    · subst hk; simp [i.2]
    · simp [hk]
  have hsingle : LinearIndependent K (fun i : {i // D i = 0} => (Pi.single i.1 (1 : K) : n → K)) := by
    have := (Pi.basisFun K n).linearIndependent.comp Subtype.val
      (Subtype.val_injective (p := fun i => D i = 0))
    convert this using 1
    funext i
    simp
  have hli : LinearIndependent K (fun i : {i // D i = 0} => (⟨_, hmem i⟩ : V)) := by
    apply LinearIndependent.of_comp V.subtype
    have hmapped := hsingle.map' Q.mulVecLin (ker_eq_bot_of_det hQ)
    have e : (⇑V.subtype ∘ fun i : {i // D i = 0} => (⟨_, hmem i⟩ : V)) =
        ⇑Q.mulVecLin ∘ fun i => (Pi.single i.1 (1 : K) : n → K) := by
      funext i
      simp
    rw [e]
    exact hmapped
  exact hli.fintype_card_le_finrank

theorem adjugate_ne_zero [Nonempty n] (M : Matrix n n K)
    (h : Module.finrank K (LinearMap.ker M.mulVecLin) ≤ 1) : M.adjugate ≠ 0 := by
  classical
  obtain ⟨P, Q, D, hP, hQ, hPQ⟩ := exists_diag M
  have hone := Fintype.card_le_one_iff.mp ((card_le_finrank hP hQ hPQ).trans h)
  obtain ⟨i, hi⟩ : ∃ i, ∀ j, j ≠ i → D j ≠ 0 := by
    by_cases hex : ∃ i, D i = 0
    · obtain ⟨i, hi0⟩ := hex
      exact ⟨i, fun j hj hj0 => hj (congrArg Subtype.val (hone ⟨j, hj0⟩ ⟨i, hi0⟩))⟩
    · push Not at hex
      exact ⟨Classical.arbitrary n, fun j _ => hex j⟩
  intro hM
  have hdiag : (diagonal D).adjugate = 0 := by
    rw [← hPQ, adjugate_mul_distrib, adjugate_mul_distrib, hM, Matrix.zero_mul, Matrix.mul_zero]
  have hii := congrFun (congrFun hdiag i) i
  rw [adjugate_diagonal, diagonal_apply_eq, Matrix.zero_apply] at hii
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => hi j (Finset.ne_of_mem_erase hj)) hii

theorem exists_coeff_adjugate_ne_zero [Nonempty n] (Ψ : Matrix n n K[X])
    (h : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ 1) :
    ∃ b c, ¬ (X : K[X]) ∣ Ψ.adjugate b c := by
  have hmap : (Ψ.map fun p => p.coeff 0) = constantCoeff.mapMatrix Ψ := by
    ext i j
    simp [constantCoeff_apply]
  have hne := adjugate_ne_zero _ h
  rw [hmap, ← RingHom.map_adjugate] at hne
  by_contra hall
  push Not at hall
  apply hne
  ext b c
  rw [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply, constantCoeff_apply]
  exact X_dvd_iff.mp (hall b c)

theorem map_coeff_mul (P Q : Matrix n n K) (Ψ : Matrix n n K[X]) (k : ℕ) :
    ((P.map C * Ψ * Q.map C).map fun p => p.coeff k) = P * (Ψ.map fun p => p.coeff k) * Q := by
  ext i j
  simp only [map_apply, Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Finset.sum_mul]

theorem diag_case [Nonempty n] (Θ : Matrix n n K[X]) (D : n → K)
    [DecidablePred fun i => D i = 0] (hD : (Θ.map fun p => p.coeff 0) = diagonal D)
    (H : ∀ x0 x1 : Fin (1 + 1) → n → K, (∀ j, (Θ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Θ.map fun p => p.coeff 1).mulVec (x0 j) + (Θ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0) :
    ∃ b c, ¬ (X : K[X]) ^ (Fintype.card {i // D i = 0} + 1) ∣ Θ.adjugate b c := by
  obtain ⟨s, hs⟩ : ∃ s : n → K[X], s = fun i => if D i = 0 then X else 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix n n K[X],
      T = Matrix.of fun i j => if D i = 0 then divX (Θ i j) else Θ i j := ⟨_, rfl⟩
  have h0 : ∀ i j, (Θ i j).coeff 0 = diagonal D i j := fun i j => by
    simpa using congrFun (congrFun hD i) j
  have hfac : Θ = diagonal s * T := by
    refine Matrix.ext fun i j => ?_
    rw [diagonal_mul, hs, hT, of_apply]
    by_cases hi : D i = 0
    · have hc : (Θ i j).coeff 0 = 0 := by
        rw [h0]
        by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [diagonal_apply_ne _ hij]
      have hX := X_mul_divX_add (Θ i j)
      rw [hc, C_0, add_zero] at hX
      simp only [hi, if_true]
      exact hX.symm
    · simp [hi]
  have hadj : ∀ b c, Θ.adjugate b c = T.adjugate b c * ∏ j ∈ Finset.univ.erase c, s j := by
    intro b c
    rw [hfac, adjugate_mul_distrib, adjugate_diagonal, mul_diagonal]
  have hprod : ∀ c, (∏ j ∈ Finset.univ.erase c, s j) ∣ X ^ Fintype.card {i // D i = 0} := by
    intro c
    have hall : ∏ j, s j = X ^ Fintype.card {i // D i = 0} := by
      simp [hs, Finset.prod_ite, Fintype.card_subtype]
    rw [← hall]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _)
  have hrow : ∀ (v : n → K) (i : n), ((T.map fun p => p.coeff 0) *ᵥ v) i =
      if D i = 0 then ((Θ.map fun p => p.coeff 1) *ᵥ v) i else D i * v i := by
    intro v i
    by_cases hi : D i = 0
    · simp [Matrix.mulVec, dotProduct, hT, hi, coeff_divX]
    · simp [Matrix.mulVec, dotProduct, hT, hi, h0, diagonal_apply]
  have hker : Module.finrank K (LinearMap.ker (T.map fun p => p.coeff 0).mulVecLin) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    set V := LinearMap.ker (T.map fun p => p.coeff 0).mulVecLin
    have h2 : 1 + 1 ≤ Module.finrank K V := hlt
    have hinj : Function.Injective (Fin.castLE h2) := fun a b hab =>
      Fin.ext (by simpa using congrArg Fin.val hab)
    have hf := (Module.finBasis K V).linearIndependent.comp _ hinj
    have hli := hf.map' V.subtype (Submodule.ker_subtype V)
    refine H (fun j => (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j)
      (fun j i => if D i = 0 then 0 else
        -((Θ.map fun p => p.coeff 1) *ᵥ (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j) i / D i)
      ?_ hli
    intro j
    set v := (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j with hv
    have hvk : (T.map fun p => p.coeff 0) *ᵥ v = 0 := by
      have := (Module.finBasis K V (Fin.castLE h2 j)).2
      rw [LinearMap.mem_ker, mulVecLin_apply] at this
      exact this
    have hvi : ∀ i, (if D i = 0 then ((Θ.map fun p => p.coeff 1) *ᵥ v) i else D i * v i) = 0 := by
      intro i
      rw [← hrow, hvk]
      rfl
    constructor
    · rw [hD]
      funext i
      rw [mulVec_diagonal]
      by_cases hi : D i = 0
      · simp [hi]
      · have := hvi i
        simp only [hi, if_false] at this
        simpa using this
    · rw [hD]
      funext i
      rw [Pi.add_apply, mulVec_diagonal]
      by_cases hi : D i = 0
      · have := hvi i
        simp only [hi, if_true] at this
        simp [hi, this]
      · simp only [hi, if_false]
        rw [Pi.zero_apply, ← mul_div_assoc, mul_div_cancel_left₀ _ hi, add_neg_cancel]
  obtain ⟨b, c, hbc⟩ := exists_coeff_adjugate_ne_zero T hker
  refine ⟨b, c, fun hdvd => hbc ?_⟩
  rw [hadj] at hdvd
  obtain ⟨r, hr⟩ := hprod c
  have h3 := Dvd.dvd.mul_right hdvd r
  rw [mul_assoc, ← hr, pow_succ, mul_comm (X ^ _) X] at h3
  exact (mul_dvd_mul_iff_right (pow_ne_zero _ X_ne_zero)).mp h3

end CofactorOrder

open CofactorOrder in

theorem exists_not_X_pow_dvd_adjugate_of_firstOrderKernel (K : Type) [Field K] (a m : ℕ)
    (Ψ : Matrix (Fin a) (Fin a) (Polynomial K))
    (H : ∀ x0 x1 : Fin (1 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0)
    (hν : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m + 1)
    (ha : a ≠ 0) :
    ∃ b c, ¬ (Polynomial.X : Polynomial K) ^ (2 * m + 1) ∣ Ψ.adjugate b c := by
  classical
  have : Nonempty (Fin a) := ⟨⟨0, Nat.pos_of_ne_zero ha⟩⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨b, c, hbc⟩ := exists_coeff_adjugate_ne_zero Ψ (by simpa using hν)
    exact ⟨b, c, by simpa using hbc⟩
  obtain ⟨P, Q, D, hP, hQ, hPQ⟩ := exists_diag (Ψ.map fun p => p.coeff 0)
  have hΘ0 : ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0) = diagonal D := by
    rw [map_coeff_mul]; exact hPQ
  have hz := card_le_finrank hP hQ hPQ
  have HΘ : ∀ x0 x1 : Fin (1 + 1) → Fin a → K,
      (∀ j, ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
        ((P.map C * Ψ * Q.map C).map fun p => p.coeff 1).mulVec (x0 j) +
          ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0 := by
    intro x0 x1 hx hli
    refine H (fun j => Q *ᵥ x0 j) (fun j => Q *ᵥ x1 j) (fun j => ?_)
      (hli.map' Q.mulVecLin (ker_eq_bot_of_det hQ))
    obtain ⟨h0, h1⟩ := hx j
    rw [map_coeff_mul] at h0 h1
    rw [map_coeff_mul] at h1
    constructor
    · apply mulVec_eq_zero_of_det hP
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc] using h0
    · apply mulVec_eq_zero_of_det hP
      simpa only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc] using h1
  obtain ⟨b, c, hbc⟩ := diag_case _ D hΘ0 HΘ
  by_contra hcon
  push Not at hcon
  apply hbc
  have hle : Fintype.card {i // D i = 0} + 1 ≤ 2 * m + 1 := by omega
  refine (pow_dvd_pow X hle).trans ?_
  rw [adjugate_mul_distrib, adjugate_mul_distrib, ← Matrix.mul_assoc]
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => Dvd.dvd.mul_right
    (Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hcon k l) _) _

end GlobalTheory
