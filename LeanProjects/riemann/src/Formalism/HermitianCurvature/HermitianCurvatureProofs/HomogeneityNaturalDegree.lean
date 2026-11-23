import Formalism.HermitianCurvature.BigCellVanishingOfCommute

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

theorem pd_mono {a b : ℕ} (hab : a ≤ b) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

theorem pd_const (c : ℂ) (d : ℕ) : U.IsPolyDeg (N := N) d (fun _ => c) := by
  refine ⟨MvPolynomial.C c, ?_, fun g => ?_⟩
  · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  · simp

theorem pd_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => g i j) := by
  refine ⟨MvPolynomial.X (Sum.inl (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_star_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g i j)) := by
  refine ⟨MvPolynomial.X (Sum.inr (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g + Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_add]

theorem pd_mul {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg b Q) :
    U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_mul]

theorem pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_sub]

theorem pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 0 a
  | insert x s hx ih =>
    have h1 := pd_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert hx] using h1

theorem pd_prod {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg (s.card * a) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 1 0
  | insert x s hx ih =>
    have h1 := pd_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hc : (insert x s).card * a = a + s.card * a := by
      rw [Finset.card_insert_of_notMem hx]; ring
    rw [hc]
    simpa [Finset.prod_insert hx] using h1

theorem pd_det {l : ℕ} (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin l) (Fin l) ℂ)
    (h : ∀ a b, U.IsPolyDeg 1 (fun g => M g a b)) : U.IsPolyDeg l (fun g => (M g).det) := by
  have key : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin l))),
      U.IsPolyDeg l (fun g => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i) := by
    intro σ _
    have h1 := pd_mul (pd_const (N := N) ((Equiv.Perm.sign σ : ℤ) : ℂ) 0)
      (pd_prod (Finset.univ : Finset (Fin l)) (fun i _ => h (σ i) i))
    refine pd_mono ?_ h1
    simp
  have h2 := pd_sum _ key
  simpa [Matrix.det_apply'] using h2

end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

namespace Formalism.FourierDecayAlt.P

open PartialDerivativeAlgebra

theorem homogeneity_natural_degree : C6.SSNatHomog := by
  intro m m' E _ _ OO h1 h2 w w' Gv T T' th hGv hT hT' _ _
  simp only [C6.unitOf]
  rw [h1, h2, smul_smul, smul_smul]
  congr 1
  have hc : 0 < Real.sqrt (T * T') := Real.sqrt_pos.mpr (mul_pos hT hT')
  have hab : Real.sqrt (T / Gv) * Real.sqrt (T' / Gv) = Real.sqrt (T * T') / Gv := by
    rw [← Real.sqrt_mul (div_nonneg hT.le hGv.le),
      show T / Gv * (T' / Gv) = (T * T') / (Gv * Gv) by ring,
      Real.sqrt_div' _ (mul_self_nonneg Gv), Real.sqrt_mul_self hGv.le]
  have hab' : ((Real.sqrt (T / Gv) : ℝ) : ℂ) * ((Real.sqrt (T' / Gv) : ℝ) : ℂ)
      = ((Real.sqrt (T * T') : ℝ) : ℂ) / (Gv : ℂ) := by
    rw [← Complex.ofReal_mul, hab, Complex.ofReal_div]
  have hc' : ((Real.sqrt (T * T') : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hG' : (Gv : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hGv.ne'
  rw [mul_assoc, hab']
  field_simp

theorem polynomial_root_facts : C6.RootFacts := by
  intro s D' hs hD
  have hs0 : s ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp s hs0
  have hnd : (Polynomial.nthRoots s D').Nodup := hprim.nthRoots_nodup hD
  refine ⟨?_, ?_⟩
  · unfold G.rootSet
    rw [Multiset.toFinset_card_of_nodup hnd, hprim.card_nthRoots D']
    rw [if_pos (IsAlgClosed.exists_pow_nat_eq D' (by omega))]
  · intro z hz
    unfold G.rootSet at hz
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
    rw [← hz, norm_pow, one_div, Real.pow_rpow_inv_natCast (norm_nonneg z) hs0]

theorem gram_function_last_minor : C6.GfDlast := by
  intro k r z z' hz hz' g ε hε
  unfold Gf at hε
  have h0 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) :=
    mul_nonneg (mul_nonneg hz hz') (Complex.normSq_nonneg _)
  linarith

private theorem isPolyDeg_one_mulVec_apply {M : ℕ} (v : Fin M → ℂ) (j : Fin M) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin M) (Fin M) ℂ => Matrix.mulVec g v j) := by
  have h := pd_sum (N := M) (Finset.univ : Finset (Fin M))
    (P := fun m g => g j m * v m) (a := 1 + 0)
    (fun m _ => pd_mul (pd_entry j m) (pd_const (v m) 0))
  simpa [Matrix.mulVec, dotProduct] using h

theorem zhat_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => Zhat k r z z' g a b) := by
  have hH : ∀ i, U.IsPolyDeg 1
      (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
        Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) := by
    intro i
    have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
      (P := fun j g => Hpk k r i j * Matrix.mulVec g (fvec k r z' b) j) (a := 0 + 1)
      (fun j _ => pd_mul (pd_const (Hpk k r i j) 0) (isPolyDeg_one_mulVec_apply _ j))
    simpa [Matrix.mulVec, dotProduct] using h
  have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
    (P := fun i g => star (fvec k r z a i) * Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) (a := 0 + 1)
    (fun i _ => pd_mul (pd_const _ 0) (hH i))
  simpa [Zhat, herm, dotProduct] using h

private theorem isPolyDeg_star' {M a : ℕ} {P : Matrix (Fin M) (Fin M) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · have hm : (map (starRingEnd ℂ) q).totalDegree ≤ q.totalDegree := by
      unfold totalDegree; exact Finset.sup_mono (support_map_subset _ _)
    exact (totalDegree_rename_le _ _).trans (hm.trans hq)
  · dsimp only
    rw [hP g, eval_rename, eval_map]
    change starRingEnd ℂ (eval₂ (RingHom.id ℂ) _ q) = _
    rw [eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem zhat_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => star (Zhat k r z z' g a b)) := by
  exact isPolyDeg_star' (zhat_pd k r z z' a b)

theorem minor_polynomial_property : C6.DminPoly := by
  intro k r z z' l
  exact pd_det (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))) (fun a b => zhat_pd k r z z' _ _)

theorem dmin_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg l.val (fun g => star (Dmin k r z z' g l)) := by
  exact isPolyDeg_star' (minor_polynomial_property k r z z' l)

theorem gram_function_polynomial : C6.GfPoly := by
  intro k r z z'
  have hL := pd_mul (minor_polynomial_property k r z z' (Fin.last (r + 1)))
    (dmin_star_pd k r z z' (Fin.last (r + 1)))
  have hR0 := pd_mul (minor_polynomial_property k r z z' ⟨r, by omega⟩)
    (dmin_star_pd k r z z' ⟨r, by omega⟩)
  have hR := pd_mul (pd_const (((Tz k r z * Tz k r z' : ℝ)) : ℂ) 0) hR0
  have hL' : U.IsPolyDeg (2 * r + 2) (fun g => Dmin k r z z' g (Fin.last (r + 1)) *
      star (Dmin k r z z' g (Fin.last (r + 1)))) :=
    pd_mono (by simp; omega) hL
  have hR' : U.IsPolyDeg (2 * r + 2) (fun g => ((Tz k r z * Tz k r z' : ℝ) : ℂ) *
      (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩))) :=
    pd_mono (by simp; omega) hR
  have h := pd_sub hL' hR'
  convert h using 2 with g
  simp only [Gf, Complex.ofReal_sub, Complex.ofReal_mul, Complex.star_def, Complex.mul_conj]

end Formalism.FourierDecayAlt.P
