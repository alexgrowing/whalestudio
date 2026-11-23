import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.CocharacterLieAlgebra.StCochar

noncomputable section

open Polynomial

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Div.CochLie

theorem eval₂_dual {R K σ : Type} [CommRing R] [Field K] [Fintype σ] (φ : R →+* K)
    (x v : σ → K) (f : MvPolynomial σ R) :
    MvPolynomial.eval₂ ((algebraMap K (DualNumber K)).comp φ)
        (fun i => algebraMap K (DualNumber K) (x i) + DualNumber.eps * algebraMap K (DualNumber K) (v i)) f =
      algebraMap K (DualNumber K) (MvPolynomial.eval₂ φ x f) +
        DualNumber.eps * algebraMap K (DualNumber K)
          (∑ i, MvPolynomial.eval₂ φ x (MvPolynomial.pderiv i f) * v i) := by
  classical
  induction f using MvPolynomial.induction_on
  next a =>
    simp [MvPolynomial.eval₂_C, MvPolynomial.pderiv_C]
  next p q hp hq =>
    simp only [MvPolynomial.eval₂_add, hp, hq, map_add, add_mul, Finset.sum_add_distrib]
    ring
  next p n hp =>
    have hterm : ∀ i, MvPolynomial.eval₂ φ x (MvPolynomial.pderiv i (p * MvPolynomial.X n)) * v i =
        x n * (MvPolynomial.eval₂ φ x (MvPolynomial.pderiv i p) * v i) +
          (if i = n then MvPolynomial.eval₂ φ x p * v n else 0) := by
      intro i
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
      by_cases h : i = n
      · subst h
        simp [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
        try ring
      · simp [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.single_apply, h, Ne.symm h]
        try ring
    rw [MvPolynomial.eval₂_mul, hp, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_ite_eq']
    simp only [MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul, Finset.mem_univ, if_true, map_add, map_mul]
    linear_combination (algebraMap K (DualNumber K) (∑ i, MvPolynomial.eval₂ φ x (MvPolynomial.pderiv i p) * v i) *
      algebraMap K (DualNumber K) (v n)) * DualNumber.eps_mul_eps (R := K)

def epsUnit (K : Type) [Field K] : (DualNumber K)ˣ where
  val := 1 + DualNumber.eps
  inv := 1 - DualNumber.eps
  val_inv := by linear_combination (-1 : DualNumber K) * DualNumber.eps_mul_eps (R := K)
  inv_val := by linear_combination (-1 : DualNumber K) * DualNumber.eps_mul_eps (R := K)

theorem epsUnit_zpow (K : Type) [Field K] (m : ℤ) :
    ((epsUnit K ^ m : (DualNumber K)ˣ) : DualNumber K) =
      1 + DualNumber.eps * algebraMap K (DualNumber K) (m : K) := by
  have key : ∀ a b : K, (1 + DualNumber.eps * algebraMap K (DualNumber K) a) *
      (1 + DualNumber.eps * algebraMap K (DualNumber K) b) =
      1 + DualNumber.eps * algebraMap K (DualNumber K) (a + b) := by
    intro a b
    rw [map_add]
    linear_combination (algebraMap K (DualNumber K) a * algebraMap K (DualNumber K) b) *
      DualNumber.eps_mul_eps (R := K)
  have hv : ((epsUnit K : (DualNumber K)ˣ) : DualNumber K) =
      1 + DualNumber.eps * algebraMap K (DualNumber K) 1 := by
    simp only [map_one, mul_one]; rfl
  have hvi : (((epsUnit K)⁻¹ : (DualNumber K)ˣ) : DualNumber K) =
      1 + DualNumber.eps * algebraMap K (DualNumber K) (-1) := by
    simp only [map_neg, map_one, mul_neg, mul_one, ← sub_eq_add_neg]; rfl
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, Units.val_mul, ih, hv, key]
    push_cast
    try rfl
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hvi, key]
    push_cast
    try ring_nf

theorem laurent_eq_zero {K : Type} [Field K] [Infinite K] (L : LaurentPolynomial K)
    (h : ∀ u : Kˣ, LaurentPolynomial.eval₂ (RingHom.id K) u L = 0) : L = 0 := by
  obtain ⟨m, p, hp⟩ := LaurentPolynomial.exists_T_pow L
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.finite_singleton (0 : K)).infinite_compl
    intro t ht
    have ht0 : t ≠ 0 := Set.mem_compl_singleton_iff.mp ht
    have h1 := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 t ht0)) hp
    rw [LaurentPolynomial.eval₂_toLaurent, map_mul, h (Units.mk0 t ht0), zero_mul] at h1
    exact h1
  rw [hp0, map_zero] at hp
  exact (LaurentPolynomial.isUnit_T (m : ℤ)).mul_left_eq_zero.mp hp.symm

theorem conj_apply {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (d : ι → R)
    (B : Matrix ι ι R) (a b : ι) : (A * Matrix.diagonal d * B) a b = ∑ j, A a j * d j * B j b := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]

theorem isRoot_conj {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (P : Matrix ι ι K) (hP : IsUnit P.det)
    (d : ι → K) (j : ι) : (P * Matrix.diagonal d * P⁻¹).charpoly.IsRoot (d j) := by
  have hc := Matrix.charpoly_units_conj (Matrix.nonsingInvUnit P hP) (Matrix.diagonal d)
  have hval : (Matrix.nonsingInvUnit P hP).val = P := rfl
  rw [hval] at hc
  rw [Polynomial.IsRoot, hc, Matrix.charpoly_diagonal, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

theorem inLie_of_cochar {K K' ι : Type} [Field K] [Field K'] [Algebra K K'] [IsAlgClosed K']
    [Fintype ι] [DecidableEq ι] (P : Matrix ι ι K') (hP : IsUnit P.det) (k : ι → ℤ)
    (f : MvPolynomial (ι × ι) K)
    (hf : ∀ t : K', t ≠ 0 → MvPolynomial.eval
      (fun p : ι × ι => (P * Matrix.diagonal (fun j => t ^ (k j)) * P⁻¹) p.1 p.2)
        (MvPolynomial.map (algebraMap K K') f) = 0) :
    ∑ p : ι × ι, algebraMap K K'
        (MvPolynomial.eval (fun q : ι × ι => (1 : Matrix ι ι K) q.1 q.2) (MvPolynomial.pderiv p f)) *
      (P * Matrix.diagonal (fun j => ((k j : ℤ) : K')) * P⁻¹) p.1 p.2 = 0 := by
  classical
  set X : Matrix ι ι K' := P * Matrix.diagonal (fun j => ((k j : ℤ) : K')) * P⁻¹ with hX
  let ent : ι × ι → LaurentPolynomial K' := fun p =>
    ∑ j, LaurentPolynomial.C (P p.1 j) * LaurentPolynomial.T (k j) * LaurentPolynomial.C (P⁻¹ j p.2)
  let Lp : LaurentPolynomial K' := MvPolynomial.eval₂ (LaurentPolynomial.C.comp (algebraMap K K')) ent f
  have hev : ∀ {S : Type} [CommRing S] (ψ : K' →+* S) (u : Sˣ), LaurentPolynomial.eval₂ ψ u Lp =
      MvPolynomial.eval₂ (ψ.comp (algebraMap K K'))
        (fun p => ∑ j, ψ (P p.1 j) * ((u ^ (k j) : Sˣ) : S) * ψ (P⁻¹ j p.2)) f := by
    intro S _ ψ u
    have h1 : (LaurentPolynomial.eval₂ ψ u).comp (LaurentPolynomial.C.comp (algebraMap K K')) =
        ψ.comp (algebraMap K K') := by
      ext c
      simp [LaurentPolynomial.eval₂_C]
    have h2 : (⇑(LaurentPolynomial.eval₂ ψ u) ∘ ent) =
        fun p => ∑ j, ψ (P p.1 j) * ((u ^ (k j) : Sˣ) : S) * ψ (P⁻¹ j p.2) := by
      funext p
      simp [ent, map_sum, map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]
    rw [MvPolynomial.eval₂_comp_left, h1, h2]
  have hL0 : Lp = 0 := by
    apply laurent_eq_zero
    intro u
    rw [hev]
    have := hf (u : K') u.ne_zero
    rw [MvPolynomial.eval_map] at this
    have e1 : (RingHom.id K').comp (algebraMap K K') = algebraMap K K' := RingHom.id_comp _
    have hfun : (fun p : ι × ι => ∑ j, (RingHom.id K') (P p.1 j) * ((u ^ (k j) : K'ˣ) : K') *
        (RingHom.id K') (P⁻¹ j p.2)) = fun p => ((P * Matrix.diagonal fun j => (u : K') ^ k j) * P⁻¹) p.1 p.2 := by
      funext p
      rw [conj_apply]
      simp [Units.val_zpow_eq_zpow_val]
    rw [e1, hfun]
    exact this
  have hd := hev (algebraMap K' (DualNumber K')) (epsUnit K')
  rw [hL0, map_zero] at hd
  have hent : ∀ p : ι × ι, (∑ j, algebraMap K' (DualNumber K') (P p.1 j) *
      ((epsUnit K' ^ (k j) : (DualNumber K')ˣ) : DualNumber K') * algebraMap K' (DualNumber K') (P⁻¹ j p.2)) =
      algebraMap K' (DualNumber K') ((1 : Matrix ι ι K') p.1 p.2) +
        DualNumber.eps * algebraMap K' (DualNumber K') (X p.1 p.2) := by
    intro p
    have h1 : (1 : Matrix ι ι K') p.1 p.2 = ∑ j, P p.1 j * P⁻¹ j p.2 := by
      rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv P hP]
    simp only [epsUnit_zpow]
    rw [h1, hX, conj_apply]
    simp only [map_sum, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hent] at hd
  have hd2 := eval₂_dual (algebraMap K K') (fun p : ι × ι => (1 : Matrix ι ι K') p.1 p.2)
    (fun p : ι × ι => X p.1 p.2) f
  rw [← hd] at hd2
  have hB := congrArg TrivSqZeroExt.snd hd2
  simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.algebraMap_eq_inl] at hB
  have hconv : ∀ g : MvPolynomial (ι × ι) K,
      MvPolynomial.eval₂ (algebraMap K K') (fun p : ι × ι => (1 : Matrix ι ι K') p.1 p.2) g =
        algebraMap K K' (MvPolynomial.eval (fun q : ι × ι => (1 : Matrix ι ι K) q.1 q.2) g) := by
    intro g
    show _ = algebraMap K K' (MvPolynomial.eval₂ (RingHom.id K) (fun q : ι × ι => (1 : Matrix ι ι K) q.1 q.2) g)
    have h3 : (⇑(algebraMap K K') ∘ fun q : ι × ι => (1 : Matrix ι ι K) q.1 q.2) =
        fun p : ι × ι => (1 : Matrix ι ι K') p.1 p.2 := by
      funext q
      simp [Matrix.one_apply, apply_ite]
    rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id, h3]
  simp only [hconv, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl] at hB
  exact hB.symm

end PositivityTheory.AutomorphicGaloisHodgeTate.Div.CochLie

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Div

open PositivityTheory.AutomorphicGaloisHodgeTate.Div.CochLie in
theorem cocharToLie_holds : CocharToLie := by
  intro hHT E Ω _ _ _ _ _ l _ N n V hV hL
  obtain ⟨K', _, _, _, P, k, e, hP, he, hlac, hke, hvan⟩ := hHT E Ω l N n V hV hL
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap (Formalism.ConjugateSelfDual.Qbar l) K').injective
  refine ⟨K', inferInstance, inferInstance, inferInstance,
    P * Matrix.diagonal (fun j => ((k j : ℤ) : K')) * P⁻¹, ?_, fun i => ((e i : ℤ) : K'), ?_, ?_, ?_⟩
  · intro f hf
    exact inLie_of_cochar P hP k f (hvan f hf)
  · intro i j hij
    exact he (by simpa using hij)
  · intro A B hA hB hAB heq
    apply hlac A B hA hB hAB
    have h1 : ((((B.card : ℚ) * ∑ i ∈ A, ((e i : ℤ) : ℚ) : ℚ)) : K') =
        ((((A.card : ℚ) * ∑ i ∈ B, ((e i : ℤ) : ℚ) : ℚ)) : K') := by
      push_cast
      exact heq
    show (B.card : ℚ) * ∑ i ∈ A, ((e i : ℤ) : ℚ) = (A.card : ℚ) * ∑ i ∈ B, ((e i : ℤ) : ℚ)
    exact_mod_cast h1
  · intro i
    obtain ⟨j, hj⟩ := hke i
    have := isRoot_conj P hP (fun j => ((k j : ℤ) : K')) j
    simpa [hj] using this

end PositivityTheory.AutomorphicGaloisHodgeTate.Div
