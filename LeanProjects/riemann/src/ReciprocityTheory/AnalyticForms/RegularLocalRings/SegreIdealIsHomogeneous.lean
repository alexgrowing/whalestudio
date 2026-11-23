import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry

noncomputable section

section Quot

variable {σ : Type} (I : Ideal (MvPolynomial σ ℂ))

attribute [local instance] MvPolynomial.gradedAlgebra

def quotGrading : ℕ → Submodule ℂ (MvPolynomial σ ℂ ⧸ I) :=
  fun d => (homogeneousSubmodule σ ℂ d).map (Ideal.Quotient.mkₐ ℂ I).toLinearMap

theorem quot_gradedAlgebra (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) :
    Nonempty (GradedAlgebra (quotGrading I)) := by
  classical
  have hgm : SetLike.GradedMonoid (quotGrading I) :=
    { one_mem := ⟨1, SetLike.one_mem_graded (homogeneousSubmodule σ ℂ), map_one (Ideal.Quotient.mkₐ ℂ I)⟩
      mul_mem := by
        rintro i j _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        exact ⟨f * g, SetLike.mul_mem_graded hf hg, map_mul (Ideal.Quotient.mkₐ ℂ I) f g⟩ }
  have hproj : ∀ i, (⨆ j, ⨆ (_ : j ≠ i), homogeneousSubmodule σ ℂ j) ≤
      LinearMap.ker (GradedAlgebra.proj (homogeneousSubmodule σ ℂ) i) := by
    intro i
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro g hg
    rw [LinearMap.mem_ker, GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne _ hg hj]
  have hint : DirectSum.IsInternal (quotGrading I) := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      rintro x ⟨f, hf, rfl⟩ hx
      have hx' : (Ideal.Quotient.mkₐ ℂ I).toLinearMap f ∈
          (⨆ j, ⨆ (_ : j ≠ i), homogeneousSubmodule σ ℂ j).map (Ideal.Quotient.mkₐ ℂ I).toLinearMap := by
        simp only [Submodule.map_iSup]
        exact hx
      obtain ⟨g, hg, hgf⟩ := hx'
      have hfg : f - g ∈ I := by
        rw [← Ideal.Quotient.eq]
        exact hgf.symm
      have hcomp := (hI.mem_iff (homogeneousSubmodule σ ℂ)).mp hfg i
      have hgi : (DirectSum.decompose (homogeneousSubmodule σ ℂ) g i : MvPolynomial σ ℂ) = 0 := by
        have := hproj i hg
        rwa [LinearMap.mem_ker, GradedAlgebra.proj_apply] at this
      rw [DirectSum.decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub, hgi, sub_zero,
        DirectSum.decompose_of_mem_same _ hf] at hcomp
      show Ideal.Quotient.mk I f = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hcomp
    · have htop : (⨆ i, homogeneousSubmodule σ ℂ i) = ⊤ :=
        (DirectSum.Decomposition.isInternal (homogeneousSubmodule σ ℂ)).submodule_iSup_eq_top
      unfold quotGrading
      rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective ℂ I
  exact ⟨{ hgm, hint.chooseDecomposition with }⟩

end Quot

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ :=
  aeval fun p => ∏ k, X ⟨k, p k⟩

def segreIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Ideal (MvPolynomial ((k : K) → ι k) ℂ) :=
  P.comap (segreMap : MvPolynomial ((k : K) → ι k) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ)

private lemma isWH_of_multiHomog [DecidableEq K] {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f a := by
  intro d hd
  have h := hf d (MvPolynomial.mem_support_iff.mpr hd)
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, ← h k, Finset.sum_eq_single k]
  · apply Finset.sum_congr rfl
    intro i _
    simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro i _
    simp [Pi.single_apply, Ne.symm hb]
  · simp

private lemma segre_isWH [DecidableEq K] {φ : MvPolynomial ((k : K) → ι k) ℂ} {n : ℕ}
    (hφ : φ.IsHomogeneous n) :
    IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) (segreMap φ)
      (fun _ => n) := by
  classical
  have hg : ∀ p : (k : K) → ι k, IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ))
      (∏ k, X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) (fun _ => 1) := by
    intro p
    have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ))
      (fun k => (Pi.single k 1 : K → ℕ))
      (fun k _ => isWeightedHomogeneous_X ℂ (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) ⟨k, p k⟩)
    convert this using 1
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← mem_weightedHomogeneousSubmodule]
  show aeval (fun p : (k : K) → ι k => ∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ)) φ ∈ _
  rw [φ.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_weightedHomogeneousSubmodule, aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
  have hdeg : (0 : K → ℕ) + ∑ p ∈ d.support, d p • (fun _ : K => 1) = fun _ => n := by
    have hw := hφ (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum] at hw
    funext j
    simp only [zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    simpa using hw
  rw [← hdeg]
  exact (isWeightedHomogeneous_C _ _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun p _ => (hg p).pow (d p))

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem segreIdeal_isHomogeneous {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    (segreIdeal P).IsHomogeneous (homogeneousSubmodule ((k : K) → ι k) ℂ) := by
  classical
  obtain ⟨S, hS, rfl⟩ := hP
  letI := MvPolynomial.weightedGradedAlgebra ℂ (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ))
  have hPh : (Ideal.span S).IsHomogeneous
      (weightedHomogeneousSubmodule ℂ (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ))) := by
    apply Ideal.homogeneous_span
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWH_of_multiHomog ha)⟩
  intro n φ hφ
  unfold segreIdeal at hφ ⊢
  rw [Ideal.mem_comap] at hφ ⊢
  have hdec : (DirectSum.decompose (homogeneousSubmodule ((k : K) → ι k) ℂ) φ n :
      MvPolynomial ((k : K) → ι k) ℂ) = homogeneousComponent n φ :=
    MvPolynomial.decomposition.decompose'_apply φ n
  rw [hdec]
  have h1 := (hPh.mem_iff _).mp hφ (fun _ => n)
  have hwdec : (DirectSum.decompose (weightedHomogeneousSubmodule ℂ (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)))
      (segreMap φ) (fun _ => n) : MvPolynomial (Σ k, ι k) ℂ) =
      weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) (fun _ => n) (segreMap φ) :=
    MvPolynomial.weightedDecomposition.decompose'_apply ℂ _ _ _
  rw [hwdec] at h1
  have hsum : segreMap φ = ∑ m ∈ Finset.range (φ.totalDegree + 1), segreMap (homogeneousComponent m φ) := by
    rw [← map_sum, sum_homogeneousComponent]
  have hterm : ∀ m, weightedHomogeneousComponent (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) (fun _ => n)
      (segreMap (homogeneousComponent m φ)) = if n = m then segreMap (homogeneousComponent m φ) else 0 := by
    intro m
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      (segre_isWH (homogeneousComponent_isHomogeneous m φ)))]
    by_cases h : n = m
    · subst h
      simp
    · rw [if_neg, if_neg h]
      intro he
      obtain ⟨k⟩ := ‹Nonempty K›
      exact h (congrFun he k)
  rw [hsum, map_sum] at h1
  simp only [hterm, Finset.sum_ite_eq] at h1
  split_ifs at h1 with hn
  · exact h1
  · rw [homogeneousComponent_eq_zero _ _ (by simp at hn; omega), map_zero]
    exact zero_mem _

abbrev segreGrading (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :
    ℕ → Submodule ℂ (MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P) :=
  quotGrading (segreIdeal P)

@[reducible] def segreGraded {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    GradedAlgebra (segreGrading P) :=
  Classical.choice (quot_gradedAlgebra _ (segreIdeal_isHomogeneous hP))

def projX (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) : Scheme :=
  letI := segreGraded hP
  Proj (segreGrading P)

abbrev segreW (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    MvPolynomial ((k : K) → ι k) ℂ ⧸ segreIdeal P :=
  Ideal.Quotient.mk _ (X p)

theorem segreW_mem (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    segreW P p ∈ segreGrading P 1 := by
  exact ⟨X p, (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℂ p), rfl⟩

def chartOpen {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) :
    (projX P hP).affineOpens :=
  letI := segreGraded hP
  ⟨Proj.basicOpen (segreGrading P) (segreW P p), Proj.isAffineOpen_basicOpen _ _ (segreW_mem P p) one_pos⟩

theorem chartOpen_cover {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (x : projX P hP) : ∃ p, x ∈ (chartOpen hP p).1 := by
  classical
  letI := segreGraded hP
  by_contra hcon
  push_neg at hcon
  have hall : ∀ p, segreW P p ∈ x.asHomogeneousIdeal := by
    intro p
    by_contra h
    exact hcon p ((Proj.mem_basicOpen (segreGrading P) (segreW P p) x).mpr h)
  have key : ∀ f ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set ((k : K) → ι k))),
      Ideal.Quotient.mk (segreIdeal P) f ∈ x.asHomogeneousIdeal.toIdeal := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨p, -, rfl⟩
      exact hall p
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact add_mem ha hb
    · intro a b _ hb
      rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hb
  apply ProjectiveSpectrum.not_irrelevant_le x
  intro a ha
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha
  change a ∈ x.asHomogeneousIdeal.toIdeal
  rw [x.asHomogeneousIdeal.isHomogeneous.mem_iff]
  intro i
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [ha]
    exact zero_mem _
  · obtain ⟨f, hf, hfa⟩ := (DirectSum.decompose (segreGrading P) a i).2
    rw [← hfa]
    apply key
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hne
    push_neg at hne
    have hm0 : m = 0 := Finsupp.ext fun p => hne p (Set.mem_univ p)
    have hw := ((mem_homogeneousSubmodule i f).mp hf) (MvPolynomial.mem_support_iff.mp hm)
    rw [hm0, map_zero] at hw
    omega

end

end ReciprocityTheory.AnForm.R
