import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LocLenAPieceSupSpanSqLeAdd

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem homRange {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] {ι : Type} (t : ι → A) (d : ℤ) (ht : ∀ i, t i ∈ 𝒜 d) :
    (Ideal.span (Set.range t)).IsHomogeneous 𝒜 := by
  refine Ideal.homogeneous_span 𝒜 _ ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨d, ht i⟩

private theorem sqMem {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] {t : A} {d : ℤ} (ht : t ∈ 𝒜 d) : t ^ 2 ∈ 𝒜 (d + d) := by
  rw [pow_two]
  exact SetLike.mul_mem_graded ht ht

private theorem spanSucc {A : Type} [CommRing A] {n : ℕ} (t : Fin (n + 1) → A) :
    Ideal.span (Set.range t) = Ideal.span {t 0} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ) := by
  rw [Fin.range_fin_succ, Ideal.span_insert]
  rfl

private theorem gen {O K A : Type} [CommRing O] [Field K] [Algebra O K] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (σ : 𝒜 0 →ₐ[O] K) (d : ℤ) (c : ℕ∞) (n : ℕ) :
    ∀ (t : Fin n → A), (∀ i, t i ∈ 𝒜 d) → ∀ J : Ideal A, J.IsHomogeneous 𝒜 →
      (∀ w, locLen σ (aPiece 𝒜 (J ⊔ Ideal.span (Set.range t)) w) ≤ c) →
      ∀ w, locLen σ (aPiece 𝒜 (J ⊔ Ideal.span (Set.range fun i => t i ^ 2)) w) ≤ 2 ^ n * c := by
  induction n generalizing c with
  | zero =>
    intro t _ J _ h w
    have e1 : Set.range (fun i : Fin 0 => t i ^ 2) = Set.range t := by
      simp [Set.range_eq_empty]
    rw [e1, pow_zero, one_mul]
    exact h w
  | succ n ih =>
    intro t ht J hJ h w
    have hJ1 : (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)).IsHomogeneous 𝒜 :=
      hJ.sup (homRange 𝒜 _ d fun i => ht i.succ)
    have h1 : ∀ w', locLen σ (aPiece 𝒜 ((J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔
        Ideal.span {t 0 ^ 2}) w') ≤ 2 * c := by
      intro w'
      have e : (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔ Ideal.span {t 0} =
          J ⊔ Ideal.span (Set.range t) := by
        rw [spanSucc t, sup_assoc, sup_comm (Ideal.span (Set.range fun i : Fin n => t i.succ))]
      refine (locLen_aPiece_sup_span_sq_le_add O K A 𝒜 σ _ hJ1 d (t 0) (ht 0) w').trans ?_
      rw [e, two_mul]
      exact add_le_add (h _) (h _)
    have hsq : (Ideal.span ({t 0 ^ 2} : Set A)).IsHomogeneous 𝒜 := by
      apply Ideal.homogeneous_span
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact ⟨d + d, sqMem 𝒜 (ht 0)⟩
    have hJ2 : (J ⊔ Ideal.span {t 0 ^ 2}).IsHomogeneous 𝒜 := hJ.sup hsq
    have h2 := ih (2 * c) (fun i => t i.succ) (fun i => ht i.succ) (J ⊔ Ideal.span {t 0 ^ 2}) hJ2
      (by
        intro w'
        have e : J ⊔ Ideal.span {t 0 ^ 2} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ) =
            (J ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ)) ⊔ Ideal.span {t 0 ^ 2} := by
          rw [sup_assoc, sup_assoc, sup_comm (Ideal.span {t 0 ^ 2})]
        rw [e]
        exact h1 w') w
    have e : J ⊔ Ideal.span {t 0 ^ 2} ⊔ Ideal.span (Set.range fun i : Fin n => t i.succ ^ 2) =
        J ⊔ Ideal.span (Set.range fun i => t i ^ 2) := by
      rw [spanSucc (fun i => t i ^ 2), sup_assoc]
    rw [e] at h2
    calc _ ≤ 2 ^ n * (2 * c) := h2
      _ = 2 ^ (n + 1) * c := by rw [pow_succ, mul_assoc]

theorem UpperTheory.V.Alg.M.locLen_aPiece_ideal2_le_two_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ σ : 𝒜 0 →ₐ[O] K, (∀ w, locLen σ (aPiece 𝒜 Q.ideal w) ≤ 1) → ∀ w, locLen σ (aPiece 𝒜 (ideal2 Q) w) ≤ 2 ^ (r + 1 + r') := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q σ h1
  have hJ0 : (Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z)).IsHomogeneous 𝒜 := by
    apply Ideal.homogeneous_span
    rintro y ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨-2, Q.hG i⟩
    · exact ⟨2, Q.hE' i⟩
    · exact ⟨0, (Q.hZ i).1⟩
  have hE := homRange 𝒜 Q.E 1 Q.hE
  have hF2 := homRange 𝒜 (fun i => Q.F i ^ 2) (-1 + -1) fun i => sqMem 𝒜 (Q.hF i)
  have step1 := gen 𝒜 σ (-1) 1 (r + 1) Q.F Q.hF
    (Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range Q.E))
    (hJ0.sup hE)
    (by
      intro w'
      have e : Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range Q.E) ⊔
          Ideal.span (Set.range Q.F) = Q.ideal := by
        simp only [Eqns.ideal, Ideal.span_union]
        ac_rfl
      rw [e]
      exact h1 w')
  have step2 := gen 𝒜 σ 1 (2 ^ (r + 1) * 1) r' Q.E Q.hE
    (Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range fun i => Q.F i ^ 2))
    (hJ0.sup hF2)
    (by
      intro w'
      have e : Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔
          Ideal.span (Set.range fun i => Q.F i ^ 2) ⊔ Ideal.span (Set.range Q.E) =
          Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔ Ideal.span (Set.range Q.E) ⊔
          Ideal.span (Set.range fun i => Q.F i ^ 2) := by
        ac_rfl
      rw [e]
      exact step1 w')
  intro w
  have e : Ideal.span (Set.range Q.G ∪ Set.range Q.E' ∪ Set.range Q.Z) ⊔
      Ideal.span (Set.range fun i => Q.F i ^ 2) ⊔ Ideal.span (Set.range fun i => Q.E i ^ 2) = ideal2 Q := by
    simp only [ideal2, Ideal.span_union]
    ac_rfl
  have h := step2 w
  rw [e] at h
  calc _ ≤ 2 ^ r' * (2 ^ (r + 1) * 1) := h
    _ = 2 ^ (r + 1 + r') := by rw [mul_one, pow_add (2 : ℕ∞) (r + 1) r', mul_comm]
