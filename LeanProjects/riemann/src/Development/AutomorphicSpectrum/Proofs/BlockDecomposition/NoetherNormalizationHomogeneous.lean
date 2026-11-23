import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailMore

set_option backward.isDefEq.respectTransparency false

open MvPolynomial

namespace GlobalTheory.CompanionTheory.ConeNoether

theorem prod_pow_lead {R ι : Type*} [CommRing R] (s : Finset ι) (e : ι → ℕ)
    (g : ι → Polynomial R) (c : ι → R) (hd : ∀ i, (g i).natDegree ≤ 1)
    (hc : ∀ i, (g i).coeff 1 = c i) :
    (∏ i ∈ s, g i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧
      (∏ i ∈ s, g i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, c i ^ e i :=
  _root_.UpperTheory.Reformulated.B.Yra8.main s e g c hd hc

theorem isIntegral_of_homogeneous_relation {K R S ι : Type*} [Field K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S] [Fintype ι]
    (F : MvPolynomial ι K) {n : ℕ} (hF : F.IsHomogeneous n) (a : ι → K) (ha : eval a F ≠ 0)
    (v : ι → R) (u : S)
    (h0 : aeval (fun i => algebraMap R S (v i) + algebraMap K S (a i) * u) F = 0) :
    IsIntegral R u := by
  classical
  let g : ι → Polynomial R := fun i =>
    Polynomial.C (v i) + Polynomial.C (algebraMap K R (a i)) * Polynomial.X
  have hgd : ∀ i, (g i).natDegree ≤ 1 := fun i => by
    simpa [g, add_comm] using
      Polynomial.natDegree_linear_le (a := algebraMap K R (a i)) (b := v i)
  have hgc : ∀ i, (g i).coeff 1 = algebraMap K R (a i) := fun i => by
    simp [g, Polynomial.coeff_C]
  have hdeg : ∀ d ∈ F.support, ∑ i, d i = n := fun d hd => by
    have := hF (mem_support_iff.1 hd)
    simpa [Finsupp.degree_eq_sum, Finsupp.weight_apply, Finsupp.sum_fintype] using this
  let p : Polynomial R := aeval g F
  have hp : p = ∑ d ∈ F.support,
      Polynomial.C (algebraMap K R (coeff d F)) * ∏ i, g i ^ d i := by
    simp only [p, aeval_def, eval₂_eq']
    rfl
  have hpd : p.natDegree ≤ n := by
    rw [hp]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    have := (prod_pow_lead Finset.univ d g _ hgd hgc).1
    rwa [hdeg d hd] at this
  have hpc : p.coeff n = algebraMap K R (eval a F) := by
    rw [hp, eval_eq', map_sum, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun d hd => ?_
    have := (prod_pow_lead Finset.univ d g _ hgd hgc).2
    rw [hdeg d hd] at this
    rw [Polynomial.coeff_C_mul, this]
    simp
  have hpe : Polynomial.eval₂ (algebraMap R S) u p = 0 := by
    have h1 := comp_aeval_apply (R := K) (f := g)
      ((Polynomial.aeval (R := R) u).restrictScalars K) F
    have h2 : (fun i => ((Polynomial.aeval (R := R) u).restrictScalars K) (g i)) =
        fun i => algebraMap R S (v i) + algebraMap K S (a i) * u := by
      funext i
      simp [g, IsScalarTower.algebraMap_apply K R S]
    rw [h2, h0] at h1
    simpa [Polynomial.aeval_def, p] using h1
  let b : R := algebraMap K R (eval a F)⁻¹
  have hb : b * algebraMap K R (eval a F) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  refine ⟨Polynomial.C b * p, ?_, ?_⟩
  · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
      ((Polynomial.natDegree_C_mul_le _ _).trans hpd) ?_
    rw [Polynomial.coeff_C_mul, hpc, hb]
  · rw [Polynomial.eval₂_mul, hpe, mul_zero]

theorem homogeneousComponent_aeval {K σ ι : Type*} [Field K] (l : ι → MvPolynomial σ K)
    (hl : ∀ i, (l i).IsHomogeneous 1) (F : MvPolynomial ι K) (n : ℕ) :
    homogeneousComponent n (aeval l F) = aeval l (homogeneousComponent n F) := by
  classical
  have key : ∀ k, homogeneousComponent n (aeval l (homogeneousComponent k F)) =
      if n = k then aeval l (homogeneousComponent k F) else 0 := fun k => by
    have h := (homogeneousComponent_isHomogeneous k F).aeval l hl
    rw [one_mul] at h
    exact homogeneousComponent_of_mem h
  conv_lhs => rw [← sum_homogeneousComponent F]
  rw [map_sum, map_sum]
  simp only [key, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

theorem exists_homogeneous_relation {K σ ι : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ n : ℕ, homogeneousComponent n f ∈ I) (l : ι → MvPolynomial σ K)
    (hl : ∀ i, (l i).IsHomogeneous 1)
    (h : ¬ AlgebraicIndependent K fun i => Ideal.Quotient.mk I (l i)) :
    ∃ (d : ℕ) (F : MvPolynomial ι K), F ≠ 0 ∧ F.IsHomogeneous d ∧ aeval l F ∈ I := by
  rw [algebraicIndependent_iff] at h
  push_neg at h
  obtain ⟨F, hF, hF0⟩ := h
  have hmem : aeval l F ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hF]
    have := comp_aeval_apply (R := K) (f := l) (Ideal.Quotient.mkₐ K I) F
    simpa using this
  obtain ⟨n, hn⟩ : ∃ n, homogeneousComponent n F ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hF0 (by rw [← sum_homogeneousComponent F]; simp [hc])
  exact ⟨n, _, hn, homogeneousComponent_isHomogeneous n F, by
    rw [← homogeneousComponent_aeval l hl]; exact hI _ hmem n⟩

theorem isIntegral_trans_subalgebra {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (A R : Subalgebra K S) (h : ∀ x ∈ A, IsIntegral R x) (s : S) (hs : IsIntegral A s) :
    IsIntegral R s := by
  let φ : A →+* integralClosure R S :=
    { toFun := fun x => ⟨x.1, h x.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h1 : IsIntegral (integralClosure R S) s :=
    IsIntegral.map_of_comp_eq φ (RingHom.id S) (by ext; rfl) hs
  exact isIntegral_trans s h1

theorem exists_linear_of_integral {K σ : Type} [Field K] [Infinite K]
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ f ∈ I, ∀ n : ℕ, homogeneousComponent n f ∈ I)
    (hne : I ≠ ⊤) (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] (l : ι → MvPolynomial σ K), Fintype.card ι = n →
      (∀ i, (l i).IsHomogeneous 1) →
      (∀ s : MvPolynomial σ K ⧸ I,
        IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (l i))) s) →
      ∃ (m : ℕ) (y : Fin m → MvPolynomial σ K), (∀ i, (y i).IsHomogeneous 1) ∧
        AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧
        ∀ s : MvPolynomial σ K ⧸ I,
          IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i))) s := by
  classical
  have hnt : Nontrivial (MvPolynomial σ K ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  have done : ∀ (ι : Type) [Fintype ι] (l : ι → MvPolynomial σ K),
      (∀ i, (l i).IsHomogeneous 1) →
      (∀ s : MvPolynomial σ K ⧸ I,
        IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (l i))) s) →
      AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (l i)) →
      ∃ (m : ℕ) (y : Fin m → MvPolynomial σ K), (∀ i, (y i).IsHomogeneous 1) ∧
        AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧
        ∀ s : MvPolynomial σ K ⧸ I,
          IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i))) s := by
    intro ι _ l hl hs hind
    let e := Fintype.equivFin ι
    refine ⟨_, fun i => l (e.symm i), fun i => hl _, hind.comp _ e.symm.injective, ?_⟩
    have hr : (Set.range fun i => Ideal.Quotient.mk I (l (e.symm i))) =
        Set.range fun i => Ideal.Quotient.mk I (l i) :=
      e.symm.surjective.range_comp fun i => Ideal.Quotient.mk I (l i)
    rw [hr]
    exact hs
  induction n with
  | zero =>
    intro ι _ l hc hl hs
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
    exact done ι l hl hs (algebraicIndependent_empty_type_iff.2 (algebraMap K _).injective)
  | succ n ih =>
    intro ι _ l hc hl hs
    by_cases hind : AlgebraicIndependent K fun i => Ideal.Quotient.mk I (l i)
    · exact done ι l hl hs hind
    obtain ⟨d, F, hF0, hFd, hFI⟩ := exists_homogeneous_relation I hI l hl hind
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨j⟩ := this
    have hGd : (X j * F).IsHomogeneous (1 + d) := (isHomogeneous_X K j).mul hFd
    have hG0 : (X j * F : MvPolynomial ι K) ≠ 0 := mul_ne_zero (X_ne_zero j) hF0
    obtain ⟨a, ha⟩ : ∃ a : ι → K, eval a (X j * F) ≠ 0 := by
      by_contra hc'
      push_neg at hc'
      exact hG0 (MvPolynomial.funext fun x => by simpa using hc' x)
    have haj : a j ≠ 0 := fun h0 => ha (by simp [h0])
    have hGI : aeval l (X j * F) ∈ I := by
      rw [map_mul]
      exact I.mul_mem_left _ hFI
    let u : MvPolynomial σ K := C (a j)⁻¹ * l j
    let v : ι → MvPolynomial σ K := fun i => l i - C (a i) * u
    have hvj : v j = 0 := by
      simp only [v, u]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ haj, C_1, one_mul, sub_self]
    have hvh : ∀ i, (v i).IsHomogeneous 1 := fun i =>
      (hl i).sub (((hl j).C_mul _).C_mul _)
    let R := Algebra.adjoin K (Set.range fun i : {i // i ≠ j} => Ideal.Quotient.mk I (v i.1))
    have hmem : ∀ i, Ideal.Quotient.mk I (v i) ∈ R := fun i => by
      by_cases h : i = j
      · subst h
        rw [hvj, map_zero]
        exact zero_mem _
      · exact Algebra.subset_adjoin ⟨⟨i, h⟩, rfl⟩
    have hdec : ∀ i, Ideal.Quotient.mk I (v i) +
        algebraMap K (MvPolynomial σ K ⧸ I) (a i) * Ideal.Quotient.mk I u =
        Ideal.Quotient.mk I (l i) := fun i => by
      have : algebraMap K (MvPolynomial σ K ⧸ I) (a i) = Ideal.Quotient.mk I (C (a i)) := rfl
      rw [this, ← map_mul, ← map_add]
      simp only [v, sub_add_cancel]
    have hu : IsIntegral R (Ideal.Quotient.mk I u) := by
      refine isIntegral_of_homogeneous_relation (X j * F) hGd a ha
        (fun i => (⟨_, hmem i⟩ : R)) _ ?_
      have h1 : (fun i => algebraMap R (MvPolynomial σ K ⧸ I) ⟨_, hmem i⟩ +
          algebraMap K (MvPolynomial σ K ⧸ I) (a i) * Ideal.Quotient.mk I u) =
          fun i => Ideal.Quotient.mkₐ K I (l i) := by
        funext i
        exact hdec i
      rw [h1, ← comp_aeval_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hGI
    have hA : ∀ x ∈ Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (l i)),
        IsIntegral R x := by
      have hle : Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (l i)) ≤
          (integralClosure R (MvPolynomial σ K ⧸ I)).restrictScalars K := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨i, rfl⟩
        change IsIntegral R _
        simp only []
        rw [← hdec i]
        refine IsIntegral.add ?_ (IsIntegral.mul ?_ hu)
        · exact isIntegral_algebraMap (x := (⟨_, hmem i⟩ : R))
        · rw [IsScalarTower.algebraMap_apply K R]
          exact isIntegral_algebraMap
      exact fun x hx => hle hx
    refine ih {i // i ≠ j} (fun i => v i.1) ?_ (fun i => hvh _) fun s =>
      isIntegral_trans_subalgebra _ R hA s (hs s)
    simp [Fintype.card_subtype_compl, hc]

theorem main : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ)
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)), I ≠ ⊤ →
    (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) →
    ∃ (e m : ℕ) (y : Fin m → MvPolynomial (Fin (N + 1)) K), 0 < e ∧
      (∀ i, (y i).IsHomogeneous e) ∧
      AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧
      Module.Finite (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i)))
        (MvPolynomial (Fin (N + 1)) K ⧸ I) := by
  intro K _ _ N I hne hI
  have htop : ∀ s : MvPolynomial (Fin (N + 1)) K ⧸ I,
      s ∈ Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (X i)) := by
    intro s
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective s
    induction f using MvPolynomial.induction_on with
    | C a => exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  obtain ⟨m, y, hy, hind, hint⟩ := exists_linear_of_integral I hI hne _ (Fin (N + 1)) X rfl
    (fun i => isHomogeneous_X K i)
    (fun s => isIntegral_algebraMap (x := (⟨s, htop s⟩ :
      Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (X i)))))
  refine ⟨1, m, y, one_pos, hy, hind, ?_⟩
  have : Algebra.IsIntegral (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i)))
      (MvPolynomial (Fin (N + 1)) K ⧸ I) := ⟨hint⟩
  have : Algebra.FiniteType K (MvPolynomial (Fin (N + 1)) K ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ_surjective K I)
  have : Algebra.FiniteType (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i)))
      (MvPolynomial (Fin (N + 1)) K ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  exact Algebra.IsIntegral.finite

end GlobalTheory.CompanionTheory.ConeNoether
