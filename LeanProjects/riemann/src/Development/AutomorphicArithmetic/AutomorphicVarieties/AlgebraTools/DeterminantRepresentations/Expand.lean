import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenEval
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenHomog

open Polynomial UpperTheory.V.W

private theorem hom_two {A : Type} [CommRing A] {n : ℕ} (P : MvPolynomial (Fin 2) A) (hP : P.IsHomogeneous n) :
    ∃ c : ℕ → A, ∀ (B : Type) [CommRing B] [Algebra A B] (s t : B),
      MvPolynomial.aeval ![s, t] P = ∑ i ∈ Finset.range (n + 1), algebraMap A B (c i) * s ^ (n - i) * t ^ i := by
  classical
  let e : ℕ → (Fin 2 →₀ ℕ) := fun i => Finsupp.single 0 (n - i) + Finsupp.single 1 i
  refine ⟨fun i => P.coeff (e i), ?_⟩
  intro B _ _ s t
  have hF : ∀ d : Fin 2 →₀ ℕ, MvPolynomial.aeval ![s, t] (MvPolynomial.monomial d (P.coeff d)) =
      algebraMap A B (P.coeff d) * s ^ (d 0) * t ^ (d 1) := by
    intro d
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp [mul_assoc]
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  simp_rw [hF]
  have hinj : Set.InjOn e (Finset.range (n + 1)) := by
    intro i _ j _ h
    have := congrArg (fun f => f 1) h
    simpa [e] using this
  have hR : ∑ i ∈ Finset.range (n + 1), algebraMap A B (P.coeff (e i)) * s ^ (n - i) * t ^ i =
      ∑ d ∈ (Finset.range (n + 1)).image e, algebraMap A B (P.coeff d) * s ^ (d 0) * t ^ (d 1) := by
    rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [e]
  rw [hR]
  apply Finset.sum_subset
  · intro d hd
    rw [Finset.mem_image]
    have hdeg := hP (MvPolynomial.mem_support_iff.mp hd)
    have h2 : d 0 + d 1 = n := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hdeg
    refine ⟨d 1, Finset.mem_range.mpr (by omega), ?_⟩
    ext j
    fin_cases j <;> simp [e] <;> omega
  · intro d _ hd
    have h0 : P.coeff d = 0 := by simpa [MvPolynomial.mem_support_iff] using hd
    simp [h0]

theorem UpperTheory.V.AlgebraTools.Det.expand :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) (B : Type) [CommRing B] [Algebra A B] (s t : B),
    D.D B (MonoidAlgebra.single 1 s + t • MonoidAlgebra.mapRingHom G (algebraMap A B) y) =
      ∑ i ∈ Finset.range (n + 1), algebraMap A B (D.lam i y) * s ^ (n - i) * t ^ i := by
  intro n A G _ _ D y B _ _ s t
  let y2 : Fin 2 → MonoidAlgebra A G := ![1, y]
  have hP := UpperTheory.V.AlgebraTools.Det.genHomog D 2 y2
  obtain ⟨c, hc⟩ := hom_two _ hP
  have hev : ∀ (B : Type) [CommRing B] [Algebra A B] (s t : B),
      D.D B (MonoidAlgebra.single 1 s + t • MonoidAlgebra.mapRingHom G (algebraMap A B) y) =
        ∑ i ∈ Finset.range (n + 1), algebraMap A B (c i) * s ^ (n - i) * t ^ i := by
    intro B _ _ s t
    rw [← hc B s t, ← UpperTheory.V.AlgebraTools.Det.genEval D B 2 y2 ![s, t]]
    congr 1
    rw [Fin.sum_univ_two]
    simp [y2, MonoidAlgebra.one_def, MonoidAlgebra.smul_single']
  have hlam : ∀ i ∈ Finset.range (n + 1), D.lam i y = c i := by
    intro i hi
    have hchi : D.chi y = ∑ j ∈ Finset.range (n + 1), Polynomial.C (c j * (-1) ^ j) * X ^ (n - j) := by
      have h := hev A[X] X (-1)
      rw [neg_one_smul, ← sub_eq_add_neg, Polynomial.algebraMap_eq] at h
      unfold GDet.chi
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, map_neg, map_one]
      ring
    unfold GDet.lam
    rw [hchi, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_left_comm, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
    · intro j hj hji
      rw [if_neg]
      intro h
      apply hji
      have := Finset.mem_range.mp hi
      have := Finset.mem_range.mp hj
      omega
    · intro h
      exact absurd hi h
  rw [hev B s t]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hlam i hi]
