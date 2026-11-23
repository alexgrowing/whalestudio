import ReciprocityTheory.DualLattices.ColengthSqBlockVandermonde

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

namespace DeterminantValuationBounds

variable {C : Type} [Field C] {v : Valuation C NNReal}

theorem infinite_residueField [IsAlgClosed C] :
    Infinite (IsLocalRing.ResidueField v.valuationSubring) := by
  classical
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  letI := Fintype.ofFinite (IsLocalRing.ResidueField v.valuationSubring)
  obtain ⟨q, hq⟩ : ∃ q, q = Fintype.card (IsLocalRing.ResidueField v.valuationSubring) := ⟨_, rfl⟩
  have hq2 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := IsLocalRing.ResidueField v.valuationSubring)
    omega
  have hdeg : (Polynomial.X ^ q - (Polynomial.X + Polynomial.C 1) : Polynomial C).degree ≠ 0 := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]
    · exact_mod_cast (by omega : q ≠ 0)
    · rw [Polynomial.degree_X_add_C]
      exact_mod_cast (by omega : 1 < q)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_C] at hα
  have hαq : α ^ q = α + 1 := sub_eq_zero.mp hα
  have hle : v α ≤ 1 := by
    by_contra h
    push_neg at h
    have h1 : v (α + 1) ≤ v α := by
      calc v (α + 1) ≤ max (v α) (v 1) := v.map_add _ _
        _ = v α := by rw [map_one]; exact max_eq_left h.le
    have h2 : v α < v α ^ q := by
      calc v α = v α ^ 1 := (pow_one _).symm
        _ < v α ^ q := pow_lt_pow_right₀ h (by omega)
    rw [← map_pow, hαq] at h2
    exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)
  have hmem : α ∈ v.valuationSubring := (v.mem_valuationSubring_iff α).mpr hle
  have hx : (⟨α, hmem⟩ : v.valuationSubring) ^ q = ⟨α, hmem⟩ + 1 := by
    apply Subtype.ext
    push_cast
    exact hαq
  have hr := congrArg (IsLocalRing.residue v.valuationSubring) hx
  have hpc := FiniteField.pow_card (IsLocalRing.residue v.valuationSubring ⟨α, hmem⟩)
  rw [← hq] at hpc
  rw [map_pow, map_add, map_one, hpc] at hr
  have h10 : (1 : IsLocalRing.ResidueField v.valuationSubring) = 0 := by
    have := congrArg (· - IsLocalRing.residue v.valuationSubring ⟨α, hmem⟩) hr
    simpa using this.symm
  exact one_ne_zero h10

theorem v_eq_one_of_residue_ne_zero {x : v.valuationSubring}
    (hx : IsLocalRing.residue v.valuationSubring x ≠ 0) : v (x : C) = 1 := by
  have hu : IsUnit x := (IsLocalRing.residue_ne_zero_iff_isUnit x).mp hx
  obtain ⟨u, rfl⟩ := hu
  have h1 : v ((u : v.valuationSubring) : C) ≤ 1 := (u : v.valuationSubring).2
  have h2 : v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) ≤ 1 :=
    ((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring).2
  have hmul : ((u : v.valuationSubring) : C) *
      (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) = 1 := by
    have h := congrArg (fun z : v.valuationSubring => (z : C)) (Units.mul_inv u)
    exact_mod_cast h
  have hv : v ((u : v.valuationSubring) : C) *
      v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  have : v ((u : v.valuationSubring) : C) *
      v (((u⁻¹ : (v.valuationSubring)ˣ) : v.valuationSubring) : C) ≤
      v ((u : v.valuationSubring) : C) := mul_le_of_le_one_right zero_le h2
  rw [hv] at this
  exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl _)

theorem eval_det_gen {K : Type} [CommRing K] {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (A : Matrix ι σ K) (z : σ × ι → K) :
    MvPolynomial.eval z (Matrix.det (Matrix.of fun i j =>
      ∑ r, MvPolynomial.C (A i r) * (MvPolynomial.X (r, j) : MvPolynomial (σ × ι) K))) =
      Matrix.det (Matrix.of fun i j => ∑ r, A i r * z (r, j)) := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [map_sum]

theorem exists_generic [IsAlgClosed C] {ι σ T : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [Fintype T] (Q : T → Matrix ι σ C) (hQ : ∀ t i r, v (Q t i r) ≤ 1)
    (hsec : ∀ t, ∃ d : Matrix σ ι C, (∀ r i, v (d r i) ≤ 1) ∧ Q t * d = 1) :
    ∃ c : Matrix σ ι C, (∀ r i, v (c r i) ≤ 1) ∧ ∀ t, v (Q t * c).det = 1 := by
  classical
  haveI : Infinite (IsLocalRing.ResidueField v.valuationSubring) := infinite_residueField
  let QO : T → Matrix ι σ v.valuationSubring :=
    fun t i r => ⟨Q t i r, (v.mem_valuationSubring_iff _).mpr (hQ t i r)⟩
  let Qk : T → Matrix ι σ (IsLocalRing.ResidueField v.valuationSubring) :=
    fun t i r => IsLocalRing.residue v.valuationSubring (QO t i r)
  let p : T → MvPolynomial (σ × ι) (IsLocalRing.ResidueField v.valuationSubring) := fun t =>
    Matrix.det (Matrix.of fun i j =>
      ∑ r, MvPolynomial.C (Qk t i r) * (MvPolynomial.X (r, j) : MvPolynomial (σ × ι) _))
  have hp : ∀ t, p t ≠ 0 := by
    intro t hzero
    obtain ⟨d, hd, hQd⟩ := hsec t
    let dO : Matrix σ ι v.valuationSubring :=
      fun r i => ⟨d r i, (v.mem_valuationSubring_iff _).mpr (hd r i)⟩
    have h1 := eval_det_gen (Qk t) (fun x => IsLocalRing.residue v.valuationSubring (dO x.1 x.2))
    have h1' : MvPolynomial.eval (fun x => IsLocalRing.residue v.valuationSubring (dO x.1 x.2))
        (p t) = _ := h1
    rw [hzero, map_zero] at h1'
    have hone : (Matrix.of fun i j => ∑ r, Qk t i r *
        IsLocalRing.residue v.valuationSubring (dO (r, j).1 (r, j).2)) = 1 := by
      ext i j
      have hij := congrFun (congrFun hQd i) j
      rw [Matrix.mul_apply] at hij
      have hO : ∑ r, QO t i r * dO r j = (1 : Matrix ι ι v.valuationSubring) i j := by
        apply Subtype.ext
        have hc : ((∑ r, QO t i r * dO r j : v.valuationSubring) : C) = ∑ r, Q t i r * d r j := by
          push_cast
          rfl
        rw [hc, hij]
        by_cases hij' : i = j
        · subst hij'
          simp
        · simp [Matrix.one_apply_ne hij']
      simp only [Matrix.of_apply, Qk]
      calc ∑ r, IsLocalRing.residue v.valuationSubring (QO t i r) *
            IsLocalRing.residue v.valuationSubring (dO r j)
          = IsLocalRing.residue v.valuationSubring (∑ r, QO t i r * dO r j) := by
            simp [map_sum, map_mul]
        _ = (1 : Matrix ι ι (IsLocalRing.ResidueField v.valuationSubring)) i j := by
            rw [hO]
            by_cases hij' : i = j
            · subst hij'; simp
            · simp [Matrix.one_apply_ne hij']
    rw [hone, Matrix.det_one] at h1'
    exact zero_ne_one h1'
  have hP : ∏ t, p t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => hp t
  obtain ⟨z, hz⟩ : ∃ z, MvPolynomial.eval z (∏ t, p t) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_prod] at hz
  have hzt : ∀ t, MvPolynomial.eval z (p t) ≠ 0 :=
    fun t => (Finset.prod_ne_zero_iff.mp hz) t (Finset.mem_univ _)
  choose y hy using fun x : σ × ι => IsLocalRing.residue_surjective (z x)
  refine ⟨Matrix.of fun r i => (y (r, i) : C), fun r i => (y (r, i)).2, fun t => ?_⟩
  let cO : Matrix σ ι v.valuationSubring := fun r i => y (r, i)
  have hcoe : (Q t * Matrix.of fun r i => (y (r, i) : C)).det =
      v.valuationSubring.subtype (QO t * cO).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_sum,
      map_mul]
    rfl
  rw [hcoe]
  apply v_eq_one_of_residue_ne_zero
  rw [RingHom.map_det]
  have hzt' := hzt t
  have he : MvPolynomial.eval z (p t) =
      Matrix.det (Matrix.of fun i j => ∑ r, Qk t i r * z (r, j)) := eval_det_gen (Qk t) z
  rw [he] at hzt'
  have hmat : (IsLocalRing.residue v.valuationSubring).mapMatrix (QO t * cO) =
      Matrix.of fun i j => ∑ r, Qk t i r * z (r, j) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply,
      map_sum, map_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← hy (r, j)]
  rw [hmat]
  exact hzt'

variable {n s : ℕ}

theorem pow_stable {a : Fin n → C} {M : Lat v (Fin n × Fin s)} (hM : IsLaStable a M) (k : ℕ)
    {w : Fin n × Fin s → C} (hw : w ∈ M.pts) :
    (fun y : Fin n × Fin s => a y.1 ^ k * w y) ∈ M.pts := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    have e : (fun y : Fin n × Fin s => a y.1 ^ (k + 1) * w y) =
        fun y => a y.1 * (a y.1 ^ k * w y) := by
      funext y
      ring
    rw [e]
    exact hM _ ih

theorem v_det_le_of_cols {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι) (X : Matrix ι ι C)
    (hX : ∀ y, (fun x => X x y) ∈ L.pts) : v X.det ≤ v L.B.det := by
  choose c hc using hX
  set U : Matrix ι ι C := Matrix.of fun i y => c y i with hU
  have hXe : X = L.B * U := by
    ext x y
    rw [show X x y = (L.B *ᵥ c y) x from congrFun (hc y).2 x, Matrix.mul_apply, Matrix.mulVec,
      dotProduct]
    simp [hU]
  have hUi : IsIntegralMat v U := fun i y => by simpa [hU] using (hc y).1 i
  rw [hXe, Matrix.det_mul, map_mul]
  exact mul_le_of_le_one_right zero_le hUi.det_le_one

end DeterminantValuationBounds

open DeterminantValuationBounds in

theorem valuation_pairwiseDifferenceProduct_pow_le_colength_sq (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (n : ℕ)
    (a : Fin n → C) (s : ℕ) (M S : Lat v (Fin n × Fin s)) (Mτ : Fin n → Lat v (Fin s))
    (hM : IsLaStable a M) (hτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ) (hS : S.pts = sumPts Mτ) :
    v (discr a) ^ s ≤ colen M S ^ 2 := by
  classical
  have v_discr : v (discr a) = v (Matrix.vandermonde a).det ^ 2 := by
    rw [Matrix.det_vandermonde, discr, sq]
    simp only [map_prod]
    have hsplit : ∀ τ : Fin n, ∏ τ' ∈ Finset.univ.erase τ, v (a τ - a τ') =
        (∏ τ' ∈ Finset.Ioi τ, v (a τ' - a τ)) * ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') := by
      intro τ
      have hu : Finset.univ.erase τ = Finset.Ioi τ ∪ Finset.Iio τ := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
          Finset.mem_Iio]
        constructor
        · intro h
          rcases lt_or_gt_of_ne h with h | h
          · exact Or.inr h
          · exact Or.inl h
        · rintro (h | h)
          · exact ne_of_gt h
          · exact ne_of_lt h
      rw [hu, Finset.prod_union (Finset.disjoint_left.mpr fun x h1 h2 => by
        simp only [Finset.mem_Ioi, Finset.mem_Iio] at h1 h2
        exact lt_asymm h1 h2)]
      congr 1
      exact Finset.prod_congr rfl fun x _ => Valuation.map_sub_swap _ _ _
    rw [Finset.prod_congr rfl fun τ _ => hsplit τ, Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_comm' (by intro x y; simp only [Finset.mem_univ, Finset.mem_Iio,
      Finset.mem_Ioi, true_and, and_true])
  have v_det_sum : v S.B.det = ∏ τ, v (Mτ τ).B.det := by
    let Bb : Matrix (Fin n × Fin s) (Fin n × Fin s) C :=
      Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
        (Matrix.blockDiagonal fun τ => (Mτ τ).B)
    have hdet : Bb.det = ∏ τ, (Mτ τ).B.det := by
      simp only [Bb, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    let Sb : Lat v (Fin n × Fin s) :=
      ⟨Bb, by rw [hdet]; exact Finset.prod_ne_zero_iff.mpr fun τ _ => (Mτ τ).det_ne⟩
    have hmv : ∀ (c : Fin n × Fin s → C) (τ : Fin n) (i : Fin s),
        (Bb *ᵥ c) (τ, i) = ((Mτ τ).B *ᵥ fun j => c (τ, j)) i := by
      intro c τ i
      simp only [Bb, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.reindex_apply,
        Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
        Matrix.blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_eq_single τ (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    have hpts : Sb.pts = sumPts Mτ := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩ τ
        refine ⟨fun j => c (τ, j), fun j => hc (τ, j), ?_⟩
        ext i
        exact hmv c τ i
      · intro hx
        choose cτ hcτ hxτ using hx
        refine ⟨fun p => cτ p.1 p.2, fun p => hcτ p.1 p.2, ?_⟩
        ext ⟨τ, i⟩
        show x (τ, i) = (Bb *ᵥ fun p => cτ p.1 p.2) (τ, i)
        rw [hmv]
        exact congrFun (hxτ τ) i
    calc v S.B.det = v Sb.B.det := Lat.v_det_eq_of_pts_eq (hS.trans hpts.symm)
      _ = ∏ τ, v (Mτ τ).B.det := by
        show v Bb.det = _
        rw [hdet, map_prod]
  let R : Fin n → Matrix (Fin s) (Fin n × Fin s) C := fun τ => Matrix.of fun i y => M.B (τ, i) y
  let Q : Fin n → Matrix (Fin s) (Fin n × Fin s) C := fun τ => (Mτ τ).B⁻¹ * R τ
  have hB : ∀ τ, (Mτ τ).B⁻¹ * (Mτ τ).B = 1 := fun τ => Matrix.nonsing_inv_mul _ (Mτ τ).isUnit_det
  have hB' : ∀ τ, (Mτ τ).B * (Mτ τ).B⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (Mτ τ).isUnit_det
  have hproj : ∀ τ (w : Fin n × Fin s → C), w ∈ M.pts → (fun i => w (τ, i)) ∈ (Mτ τ).pts := by
    intro τ w hw
    rw [hτ τ]
    exact ⟨w, hw, rfl⟩
  have hcolM : ∀ (c : Fin n × Fin s → C), IsIntegralVec v c → M.B *ᵥ c ∈ M.pts :=
    fun c hc => ⟨c, hc, rfl⟩
  have hQint : ∀ τ i y, v (Q τ i y) ≤ 1 := by
    intro τ i y
    have hcol : M.B *ᵥ Pi.single y 1 ∈ M.pts := hcolM _ (isIntegralVec_single y)
    obtain ⟨c, hc, hce⟩ := hproj τ _ hcol
    have hQc : (fun i => Q τ i y) = c := by
      have h1 : (fun i => Q τ i y) = (Mτ τ).B⁻¹ *ᵥ (fun i => (M.B *ᵥ Pi.single y 1) (τ, i)) := by
        ext i
        simp [Q, R, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [h1, hce, Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
    have := hc i
    rw [← hQc] at this
    exact this
  have hsec : ∀ τ, ∃ d : Matrix (Fin n × Fin s) (Fin s) C, (∀ r i, v (d r i) ≤ 1) ∧ Q τ * d = 1 := by
    intro τ
    have hmem : ∀ j, (fun i => (Mτ τ).B i j) ∈ projPts M.pts τ := by
      intro j
      rw [← hτ τ]
      refine ⟨Pi.single j 1, isIntegralVec_single j, ?_⟩
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    choose w hw hwe using hmem
    choose d hd hde using hw
    refine ⟨Matrix.of fun r j => d j r, fun r j => hd j r, ?_⟩
    have hRd : R τ * (Matrix.of fun r j => d j r) = (Mτ τ).B := by
      ext i j
      have h1 : w j (τ, i) = (Mτ τ).B i j := congrFun (hwe j) i
      rw [hde j] at h1
      rw [← h1]
      simp [R, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    show (Mτ τ).B⁻¹ * R τ * _ = 1
    rw [Matrix.mul_assoc, hRd, hB]
  obtain ⟨c, hcint, hcdet⟩ := exists_generic Q (fun τ i y => hQint τ i y) hsec
  let X : Matrix (Fin n × Fin s) (Fin n × Fin s) C :=
    Matrix.of fun x y => a x.1 ^ (y.1 : ℕ) * (M.B * c) x y.2
  have hXcols : ∀ y, (fun x => X x y) ∈ M.pts := by
    intro y
    have hw : (fun x => (M.B * c) x y.2) ∈ M.pts := by
      refine ⟨fun r => c r y.2, fun r => hcint r y.2, ?_⟩
      ext x
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact pow_stable hM y.1 hw
  have hle : v X.det ≤ v M.B.det := v_det_le_of_cols M X hXcols
  let G : Fin n → Matrix (Fin s) (Fin s) C := fun τ => (Mτ τ).B * (Q τ * c)
  have hG : ∀ τ i j, (M.B * c) (τ, i) j = G τ i j := by
    intro τ i j
    show _ = ((Mτ τ).B * ((Mτ τ).B⁻¹ * R τ * c)) i j
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hB', Matrix.one_mul]
    simp [R, Matrix.mul_apply]
  have hfree : freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a := by
    ext x y
    simp [freeMat, Matrix.blockDiagonal_apply, Matrix.vandermonde_apply]
  have hXfac : X = Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal G) * freeMat a s := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [X, Matrix.of_apply, hG, freeMat, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap, Matrix.blockDiagonal_apply]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  have hGdet : ∀ τ, v (G τ).det = v (Mτ τ).B.det := by
    intro τ
    simp only [G, Matrix.det_mul, map_mul, hcdet τ, mul_one]
  have hdetX : v X.det = (∏ τ, v (Mτ τ).B.det) * v (Matrix.vandermonde a).det ^ s := by
    rw [hXfac, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_blockDiagonal, hfree,
      Matrix.det_blockDiagonal, map_mul, map_prod, map_prod]
    simp only [hGdet, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hSdet := v_det_sum
  have hSpos : 0 < v S.B.det := by
    rw [pos_iff_ne_zero, Ne, map_eq_zero]
    exact S.det_ne
  have hcol : v (Matrix.vandermonde a).det ^ s ≤ colen M S := by
    rw [colen, le_div_iff₀ hSpos, hSdet, mul_comm, ← hdetX]
    exact hle
  rw [v_discr, ← pow_mul, mul_comm 2 s, pow_mul]
  exact pow_le_pow_left₀ zero_le hcol 2

end ReciprocityTheory.PGsh.Up
