import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.MatDefs

noncomputable section

open Matrix

namespace PositivityTheory.KB.BlockInvariants

namespace WeightTwoPolynomials

section Poly

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

def mt (x : Fin q → Matrix ι ι ℂ) : Matrix (Fin q → ι) (Fin q → ι) ℂ :=
  Matrix.of fun I J => ∏ i, x i (I i) (J i)

theorem tp_sum {K : Type} [Fintype K] [DecidableEq K] (M : K → Matrix ι ι ℂ) (c : K → ℂ) :
    tp q (∑ k, c k • M k) = ∑ f : Fin q → K, (∏ j, c (f j)) • mt (fun j => M (f j)) := by
  ext I J
  simp only [tp, mt, of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]

open MvPolynomial in

def polyOf {K : Type} [Fintype K] (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ)
    (M : K → Matrix ι ι ℂ) : MvPolynomial K ℂ :=
  ∑ f : Fin q → K, C (φ (mt fun j => M (f j))) * ∏ j, X (f j)

open MvPolynomial in
theorem eval_polyOf {K : Type} [Fintype K] [DecidableEq K]
    (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (M : K → Matrix ι ι ℂ) (c : K → ℂ) :
    eval c (polyOf φ M) = φ (tp q (∑ k, c k • M k)) := by
  rw [tp_sum, map_sum, polyOf, map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, eval_C, map_prod]
  simp only [eval_X]
  ring

open MvPolynomial in
theorem totalDegree_polyOf {K : Type} [Fintype K]
    (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (M : K → Matrix ι ι ℂ) :
    (polyOf φ M).totalDegree ≤ q := by
  unfold polyOf
  refine totalDegree_finsetSum_le fun f _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  simp [totalDegree_X]

theorem grid {K : Type} [Fintype K] [DecidableEq K]
    (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (M : K → Matrix ι ι ℂ) (S : K → Finset ℂ)
    (hS : ∀ k, q < (S k).card) (h0 : ∀ c : K → ℂ, (∀ k, c k ∈ S k) → φ (tp q (∑ k, c k • M k)) = 0)
    (c : K → ℂ) : φ (tp q (∑ k, c k • M k)) = 0 := by
  have hP : polyOf φ M = 0 := MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ S
    (fun k => lt_of_le_of_lt ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
      (totalDegree_polyOf φ M)) (hS k))
    (fun x hx => by rw [eval_polyOf]; exact h0 x hx)
  rw [← eval_polyOf, hP, map_zero]

end Poly

section GlobalTheory

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

theorem blk_apply (d : W → Matrix (Fin m) (Fin m) ℂ) (x y : Ix W m) :
    blk d x y = if x.1 = y.1 then d x.1 x.2 y.2 else 0 := rfl

theorem blk_add (d e : W → Matrix (Fin m) (Fin m) ℂ) : blk (d + e) = blk d + blk e := by
  ext x y; simp only [blk_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp

theorem blk_smul (a : ℂ) (d : W → Matrix (Fin m) (Fin m) ℂ) : blk (a • d) = a • blk d := by
  ext x y; simp only [blk_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem blk_sum {K : Type} (s : Finset K) (d : K → W → Matrix (Fin m) (Fin m) ℂ) :
    blk (∑ k ∈ s, d k) = ∑ k ∈ s, blk (d k) := by
  ext x y; simp only [blk_apply, Matrix.sum_apply, Finset.sum_apply]; split_ifs <;> simp

theorem eq_blk (M : Matrix (Ix W m) (Ix W m) ℂ) (hM : ∀ x y : Ix W m, x.1 ≠ y.1 → M x y = 0) :
    M = blk (fun w a b => M (w, a) (w, b)) := by
  ext x y
  change M x y = if x.1 = y.1 then M (x.1, x.2) (x.1, y.2) else 0
  split_ifs with h
  · obtain ⟨w, a⟩ := x; obtain ⟨w', b⟩ := y
    simp only at h; subst h; rfl
  · exact hM x y h

theorem herm_of_unit (φ : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ →ₗ[ℂ] ℂ)
    (hU : ∀ d : W → Matrix (Fin m) (Fin m) ℂ, (∀ w, d w ∈ unitaryGroup (Fin m) ℂ) → φ (tp q (blk d)) = 0)
    (d : W → Matrix (Fin m) (Fin m) ℂ) (hd : ∀ w, (d w).IsHermitian) : φ (tp q (blk d)) = 0 := by
  set v : W → Matrix (Fin m) (Fin m) ℂ := fun w => ((hd w).eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have hv : ∀ w, v w ∈ unitaryGroup (Fin m) ℂ := fun w => ((hd w).eigenvectorUnitary).2
  let M : Ix W m → Matrix (Ix W m) (Ix W m) ℂ := fun k =>
    blk fun w => if w = k.1 then v w * diagonal (Pi.single k.2 1) * star (v w) else 0
  have hsum : ∀ c : Ix W m → ℂ, ∑ k, c k • M k =
      blk fun w => v w * diagonal (fun a => c (w, a)) * star (v w) := by
    intro c
    simp_rw [M, ← blk_smul, ← blk_sum]
    congr 1
    funext w
    rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single w]
    · simp only [Pi.smul_apply, if_true]
      have hd1 : ∑ x : Fin m, c (w, x) • diagonal (Pi.single x (1 : ℂ)) = diagonal fun a => c (w, a) := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
        split_ifs with h
        · subst h; simp [Pi.single_apply]
        · simp
      rw [← hd1, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
    · intro w' _ hw'
      simp [Ne.symm hw']
    · simp
  have hcirc : ∀ c : Ix W m → ℂ, (∀ k, ‖c k‖ = 1) → φ (tp q (∑ k, c k • M k)) = 0 := by
    intro c hc
    rw [hsum]
    refine hU _ fun w => ?_
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (hv w) ?_) (Unitary.star_mem (hv w))
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [Complex.star_def, Complex.mul_conj', hc (w, a)]
    simp
  have hq : 0 < q + 1 := Nat.succ_pos q
  have hζ := Complex.isPrimitiveRoot_exp (q + 1) (Nat.succ_ne_zero q)
  have hall := grid φ M (fun _ => Polynomial.nthRootsFinset (q + 1) (1 : ℂ))
    (fun _ => by rw [hζ.card_nthRootsFinset]; omega)
    (fun c hc => hcirc c fun k => Complex.norm_eq_one_of_pow_eq_one
      ((Polynomial.mem_nthRootsFinset hq (1 : ℂ)).1 (hc k)) (Nat.succ_ne_zero q))
  have := hall fun k => ((hd k.1).eigenvalues k.2 : ℂ)
  rw [hsum] at this
  have e : d = fun w => v w * diagonal (fun a => ((hd w).eigenvalues a : ℂ)) * star (v w) := by
    funext w
    conv_lhs => rw [(hd w).spectral_theorem]
    rfl
  rw [e]
  exact this

theorem all_of_herm (φ : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ →ₗ[ℂ] ℂ)
    (hH : ∀ d : W → Matrix (Fin m) (Fin m) ℂ, (∀ w, (d w).IsHermitian) → φ (tp q (blk d)) = 0)
    (d : W → Matrix (Fin m) (Fin m) ℂ) : φ (tp q (blk d)) = 0 := by
  set H : W → Matrix (Fin m) (Fin m) ℂ := fun w => (2 : ℂ)⁻¹ • (d w + (d w)ᴴ)
  set K : W → Matrix (Fin m) (Fin m) ℂ := fun w => ((2 : ℂ)⁻¹ * -Complex.I) • (d w - (d w)ᴴ)
  let M : Fin 2 → Matrix (Ix W m) (Ix W m) ℂ := ![blk H, blk K]
  have hM : ∀ c : Fin 2 → ℂ, ∑ k, c k • M k = blk (c 0 • H + c 1 • K) := by
    intro c
    simp [M, Fin.sum_univ_two, blk_add, blk_smul]
  have hall := grid φ M (fun _ => (Finset.range (q + 1)).image (Nat.cast : ℕ → ℂ))
    (fun _ => by rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]; omega)
    (fun c hc => by
      rw [hM]
      refine hH _ fun w => ?_
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hc 0)
      obtain ⟨b, -, hb⟩ := Finset.mem_image.1 (hc 1)
      rw [← ha, ← hb]
      simp only [IsHermitian, Pi.add_apply, Pi.smul_apply, H, K, conjTranspose_add,
        conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      simp only [star_natCast, star_mul', star_inv₀, star_ofNat, star_neg, Complex.star_def,
        Complex.conj_I]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring)
  have := hall ![1, Complex.I]
  rw [hM] at this
  have e : d = (![1, Complex.I] : Fin 2 → ℂ) 0 • H + (![1, Complex.I] : Fin 2 → ℂ) 1 • K := by
    funext w
    ext i j
    simp only [Pi.add_apply, Pi.smul_apply, H, K, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination (2 : ℂ)⁻¹ * (d w i j - (d w)ᴴ i j) * Complex.I_sq
  rw [e]
  exact this

end GlobalTheory

section Comm

variable {W : Type} [Fintype W] [DecidableEq W] {m q : ℕ}

theorem perm'_apply (σ : Equiv.Perm (Fin q)) (w : Fin q → W) (I J : Fin q → Ix W m) :
    perm' σ w I J = if (∀ i, (I i).1 = w i) ∧ J = I ∘ σ then 1 else 0 := rfl

theorem mul_perm' (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) (σ : Equiv.Perm (Fin q))
    (w : Fin q → W) (A B : Fin q → Ix W m) :
    (Z * perm' σ w : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) A B =
      if (∀ i, ((B ∘ σ.symm) i).1 = w i) then Z A (B ∘ σ.symm) else 0 := by
  have hB : (B ∘ σ.symm) ∘ σ = B := by funext i; simp
  rw [mul_apply, Finset.sum_eq_single (B ∘ σ.symm)]
  · rw [perm'_apply]
    split_ifs with h1 h2 h2
    · rw [mul_one]
    · exact absurd h1.1 h2
    · exact absurd ⟨h2, hB.symm⟩ h1
    · rw [mul_zero]
  · intro K _ hK
    rw [perm'_apply, if_neg, mul_zero]
    rintro ⟨-, rfl⟩
    exact hK (by funext i; simp)
  · simp

theorem perm'_mul (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) (σ : Equiv.Perm (Fin q))
    (w : Fin q → W) (A B : Fin q → Ix W m) :
    (perm' σ w * Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ) A B =
      if (∀ i, (A i).1 = w i) then Z (A ∘ σ) B else 0 := by
  rw [mul_apply, Finset.sum_eq_single (A ∘ σ)]
  · rw [perm'_apply]
    split_ifs with h1 h2 h2
    · rw [one_mul]
    · exact absurd h1.1 h2
    · exact absurd ⟨h2, rfl⟩ h1
    · rw [zero_mul]
  · intro K _ hK
    rw [perm'_apply, if_neg, zero_mul]
    rintro ⟨-, rfl⟩
    exact hK rfl
  · simp

theorem compat_of_comm (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ)
    (hZ : ∀ (σ : Equiv.Perm (Fin q)) (w : Fin q → W), Z * perm' σ w = perm' σ w * Z)
    (I J : Fin q → Ix W m) (h : Z I J ≠ 0) : ∀ i, (I i).1 = (J i).1 := by
  have := congrFun (congrFun (hZ 1 fun i => (J i).1) I) J
  rw [mul_perm', perm'_mul] at this
  have e1 : J ∘ (1 : Equiv.Perm (Fin q)).symm = J := by funext i; rfl
  rw [e1] at this
  rw [if_pos (fun _ => rfl)] at this
  by_contra hne
  rw [if_neg hne] at this
  exact h this

theorem sym_of_comm (Z : Matrix (Fin q → Ix W m) (Fin q → Ix W m) ℂ)
    (hZ : ∀ (σ : Equiv.Perm (Fin q)) (w : Fin q → W), Z * perm' σ w = perm' σ w * Z)
    (σ : Equiv.Perm (Fin q)) (I J : Fin q → Ix W m) : Z (I ∘ σ) (J ∘ σ) = Z I J := by
  have := congrFun (congrFun (hZ σ fun i => (I i).1) I) (J ∘ σ)
  rw [mul_perm', perm'_mul] at this
  have hJ : (J ∘ σ) ∘ σ.symm = J := by funext i; simp
  rw [hJ] at this
  rw [if_pos (fun _ => rfl)] at this
  rw [← this]
  by_cases h : Z I J = 0
  · rw [h]; split_ifs <;> rfl
  · rw [if_pos fun i => (compat_of_comm Z hZ I J h i).symm]

end Comm

section Sym

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

def symU (I J : Fin q → ι) : Matrix (Fin q → ι) (Fin q → ι) ℂ :=
  ∑ σ : Equiv.Perm (Fin q), Matrix.single (I ∘ σ) (J ∘ σ) 1

theorem decomp (Z : Matrix (Fin q → ι) (Fin q → ι) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin q)) I J, Z (I ∘ σ) (J ∘ σ) = Z I J) :
    ((Nat.factorial q : ℕ) : ℂ) • Z = ∑ I, ∑ J, Z I J • symU I J := by
  have key : ∀ (σ : Equiv.Perm (Fin q)) (K L : Fin q → ι),
      ∑ I, ∑ J, Z I J * Matrix.single (I ∘ σ) (J ∘ σ) (1 : ℂ) K L = Z K L := by
    intro σ K L
    rw [Finset.sum_eq_single (K ∘ σ.symm)]
    · rw [Finset.sum_eq_single (L ∘ σ.symm)]
      · have h1 : (K ∘ σ.symm) ∘ σ = K := by funext i; simp
        have h2 : (L ∘ σ.symm) ∘ σ = L := by funext i; simp
        rw [h1, h2, Matrix.single_apply_same, mul_one, hsym]
      · intro J _ hJ
        rw [Matrix.single_apply, if_neg, mul_zero]
        rintro ⟨-, h⟩
        exact hJ (by rw [← h]; funext i; simp)
      · simp
    · intro I _ hI
      refine Finset.sum_eq_zero fun J _ => ?_
      rw [Matrix.single_apply, if_neg, mul_zero]
      rintro ⟨h, -⟩
      exact hI (by rw [← h]; funext i; simp)
    · simp
  ext K L
  simp only [Matrix.smul_apply, Matrix.sum_apply, symU, smul_eq_mul, Finset.mul_sum]
  conv_rhs => enter [2, I]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem nu_iff (f : Fin q → Fin q) :
    (∑ j, Finsupp.single (f j) 1 : Fin q →₀ ℕ) = ∑ j, Finsupp.single j 1 ↔ Function.Bijective f := by
  constructor
  · intro h
    have hs : Function.Surjective f := by
      intro k
      by_contra hk
      push_neg at hk
      have := congrArg (fun g : Fin q →₀ ℕ => g k) h
      simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply] at this
      simp [hk] at this
    exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩
  · intro h
    exact Fintype.sum_bijective f h _ _ fun _ => rfl

theorem sum_perm_mt (x : Fin q → Matrix ι ι ℂ) (I J : Fin q → ι)
    (hx : ∀ j, x j = Matrix.single (I j) (J j) 1) :
    ∑ σ : Equiv.Perm (Fin q), mt (fun j => x (σ j)) = symU I J := by
  refine Finset.sum_congr rfl fun σ _ => ?_
  ext K L
  simp only [mt, of_apply, hx, Matrix.single_apply]
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩
  · rintro ⟨h1, h2⟩ i
    exact ⟨congrFun h1 i, congrFun h2 i⟩

open MvPolynomial in

theorem sym_zero (φ : Matrix (Fin q → ι) (Fin q → ι) ℂ →ₗ[ℂ] ℂ) (x : Fin q → Matrix ι ι ℂ)
    (h0 : ∀ t : Fin q → ℂ, φ (tp q (∑ j, t j • x j)) = 0) :
    φ (∑ σ : Equiv.Perm (Fin q), mt (fun j => x (σ j))) = 0 := by
  have hP : polyOf φ x = 0 := MvPolynomial.funext fun t => by rw [eval_polyOf, h0, map_zero]
  have hc := congrArg (coeff (∑ j : Fin q, Finsupp.single j 1)) hP
  rw [coeff_zero, polyOf, coeff_sum] at hc
  have hX : ∀ f : Fin q → Fin q, (∏ j, X (f j) : MvPolynomial (Fin q) ℂ) =
      monomial (∑ j, Finsupp.single (f j) 1) 1 := fun f => by
    rw [monomial_sum_one]; rfl
  simp only [hX, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero] at hc
  rw [← Finset.sum_filter] at hc
  have hfil : (Finset.univ.filter fun f : Fin q → Fin q =>
      (∑ j, Finsupp.single (f j) 1 : Fin q →₀ ℕ) = ∑ j, Finsupp.single j 1) =
      Finset.univ.map ⟨fun σ : Equiv.Perm (Fin q) => (σ : Fin q → Fin q), DFunLike.coe_injective⟩ := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk,
      nu_iff]
    exact ⟨fun h => ⟨Equiv.ofBijective f h, rfl⟩, fun ⟨σ, hσ⟩ => hσ ▸ σ.bijective⟩
  rw [hfil, Finset.sum_map] at hc
  rw [map_sum]
  exact hc

end Sym

end WeightTwoPolynomials

open WeightTwoPolynomials in
theorem sw2 : PlacePermOperatorCommutantSpan := by
  intro W _ _ m q Z hZ
  by_contra hZS
  obtain ⟨φ, hφZ, hφS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hZS inferInstance
  have hφ : ∀ y ∈ Submodule.span ℂ {M | ∃ d : W → Matrix (Fin m) (Fin m) ℂ,
      (∀ w, d w ∈ Matrix.unitaryGroup (Fin m) ℂ) ∧ M = tp q (blk d)}, φ y = 0 := by
    intro y hy
    have : φ y ∈ (Submodule.span ℂ _).map φ := Submodule.mem_map_of_mem hy
    rw [hφS] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hU : ∀ d : W → Matrix (Fin m) (Fin m) ℂ, (∀ w, d w ∈ unitaryGroup (Fin m) ℂ) →
      φ (tp q (blk d)) = 0 := fun d hd => hφ _ (Submodule.subset_span ⟨d, hd, rfl⟩)
  have hAll := all_of_herm φ (herm_of_unit φ hU)
  apply hφZ
  have hfac : ((Nat.factorial q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero q)
  have hdec := congrArg φ (decomp Z (sym_of_comm Z hZ))
  rw [map_smul, smul_eq_mul, map_sum] at hdec
  have hterm : ∀ I J, φ (Z I J • symU I J) = 0 := by
    intro I J
    rw [map_smul, smul_eq_mul]
    by_cases h : Z I J = 0
    · rw [h, zero_mul]
    · have hc := compat_of_comm Z hZ I J h
      have h0 : ∀ t : Fin q → ℂ, φ (tp q (∑ j, t j • Matrix.single (I j) (J j) (1 : ℂ))) = 0 := by
        intro t
        rw [eq_blk (∑ j, t j • Matrix.single (I j) (J j) (1 : ℂ))]
        · exact hAll _
        · intro x y hxy
          simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [if_neg, mul_zero]
          rintro ⟨rfl, rfl⟩
          exact hxy (hc j)
      have hs := sym_zero φ (fun j => Matrix.single (I j) (J j) (1 : ℂ)) h0
      rw [sum_perm_mt _ I J fun _ => rfl] at hs
      rw [hs, mul_zero]
  simp only [map_sum, hterm, Finset.sum_const_zero] at hdec
  exact (mul_eq_zero.1 hdec).resolve_left hfac

end PositivityTheory.KB.BlockInvariants

end
