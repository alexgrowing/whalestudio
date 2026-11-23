import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import Lemmata.FirstBlockLemmaK.Imports

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

variable {R : Type} [CommRing R]

theorem isUnit_of_aug {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (hJ : IsNilpotent (RingHom.ker aug))
    (a : A) (ha : IsUnit (aug a)) : IsUnit a := by
  exact @Bl.FirstBlockLemmaK.goal1 R _ A _ _ aug hJ a ha

theorem nil_of_pow {A : Type} [CommRing A] (J : Ideal A) {m : ℕ} (hJ : J ^ (m + 1) = ⊥) : IsNilpotent J :=
  ⟨m + 1, by rw [hJ, Ideal.zero_eq_bot]⟩

theorem elt_nil {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) : ∀ a ∈ J, IsNilpotent a := by
  obtain ⟨N, hN⟩ := hJ
  intro a ha
  refine ⟨N, ?_⟩
  have := Ideal.pow_mem_pow ha N
  rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact this

theorem aug_surj {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) : Function.Surjective aug :=
  fun r => ⟨algebraMap R A r, by rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]⟩

theorem jetAug_comp_trunc (n m : ℕ) : (jetAug R (Fin n) m).comp (jetTruncR R (Fin n) m) = jetAug R (Fin n) (m + 1) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact jetAug_zR (R := R) m j

theorem jetAug_comp_zero (n m : ℕ) : (jetAug R (Fin n) 0).comp (jetZeroR R (Fin n) m) = jetAug R (Fin n) m :=
  jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact jetAug_zR (R := R) 0 j

theorem jetZero_zR (n m : ℕ) (j : Fin n) : jetZeroR R (Fin n) m (zR m j) = 0 := by
  show Ideal.Quotient.mk _ (MvPolynomial.X j) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact Ideal.subset_span ⟨j, rfl⟩

theorem algChart [IsLocalRing R] (B : Type) [CommRing B] [Algebra R B] [Algebra.Smooth R B] (eps : B →ₐ[R] R) :
    ∃ (n : ℕ) (π : ∀ m : ℕ, B →ₐ[R] JetR R (Fin n) m),
      (∀ m, (jetTruncR R (Fin n) m).comp (π (m + 1)) = π m) ∧
      (∀ m, (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp eps) ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ →
        ∀ φ : B →ₐ[R] A, aug.comp φ = eps →
          ∃! ψ : JetR R (Fin n) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin n) m ∧ ψ.comp (π m) = φ := by
  let q : Ideal B := (IsLocalRing.maximalIdeal R).comap eps
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨f, hfq, n, _, hST, hSE⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := q)
  haveI := hST
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) R) (Localization.Away f) := inferInstance
  have hf : IsUnit (eps f) := by
    by_contra h
    exact hfq ((IsLocalRing.mem_maximalIdeal _).mpr h)
  let toS : B →ₐ[R] Localization.Away f := IsScalarTower.toAlgHom R B (Localization.Away f)
  let ε' : Localization.Away f →ₐ[R] R := IsLocalization.Away.liftAlgHom f hf
  have hε' : ε'.comp toS = eps := by
    ext b
    exact IsLocalization.Away.lift_eq f hf b
  have locExt : ∀ {A : Type} [CommRing A] [Algebra R A] (φ₁ φ₂ : Localization.Away f →ₐ[R] A),
      φ₁.comp toS = φ₂.comp toS → φ₁ = φ₂ := by
    intro A _ _ φ₁ φ₂ h
    ext s
    exact AlgHom.congr_fun h s
  have hπ : ∀ m : ℕ, ∃ π : Localization.Away f →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε' ∧
      ∀ j, π (sX R j) = algebraMap R _ (ε' (sX R j)) + zR m j := fun m =>
    etale_exists (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun j => by
      rw [map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])
  choose π hπaug hπX using hπ
  refine ⟨n, fun m => (π m).comp toS, ?_, ?_, ?_⟩
  · intro m
    rw [← AlgHom.comp_assoc]
    congr 1
    refine etale_ext (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_trunc]
      exact hπaug (m + 1)
    · exact hπaug m
    · intro j
      rw [AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]
      rfl
  · intro m
    rw [← hε', ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
    congr 1
    refine etale_ext (n := n) ε' (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_zero]
      exact hπaug m
    · ext s
      simp
    · intro j
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]
      rfl
  · intro A _ _ aug m hJ φ hφ
    have hJn := nil_of_pow _ hJ
    have hu : IsUnit (φ f) := isUnit_of_aug aug hJn _ (by rw [← AlgHom.comp_apply, hφ]; exact hf)
    let φ' : Localization.Away f →ₐ[R] A := IsLocalization.Away.liftAlgHom f hu
    have hφ' : φ'.comp toS = φ := by
      ext b
      exact IsLocalization.Away.lift_eq f hu b
    have hφ'aug : aug.comp φ' = ε' := locExt _ _ (by rw [AlgHom.comp_assoc, hφ', hφ, hε'])
    have hmem : ∀ j : Fin n, φ' (sX (S := Localization.Away f) R j) -
        algebraMap R A (ε' (sX (S := Localization.Away f) R j)) ∈ RingHom.ker aug := by
      intro j
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← AlgHom.comp_apply, hφ'aug, sub_self]
    let ψ := jetLift R (RingHom.ker aug) hJ
      (fun j : Fin n => φ' (sX (S := Localization.Away f) R j) - algebraMap R A (ε' (sX (S := Localization.Away f) R j))) hmem
    have hψaug : aug.comp ψ = jetAug R (Fin n) m := jet_ext fun j => by
      rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hmem j
    have hψπ : ψ.comp (π m) = φ' := by
      refine etale_ext (n := n) ε' aug hJn _ _ ?_ ?_ ?_
      · rw [← AlgHom.comp_assoc, hψaug]
        exact hπaug m
      · exact hφ'aug
      · intro j
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]
    refine ⟨ψ, ⟨hψaug, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hψπ, hφ']
    · rintro ψ₂ ⟨_, h2⟩
      rw [← AlgHom.comp_assoc, ← hφ'] at h2
      have h4 : ψ₂.comp (π m) = φ' := locExt _ _ h2
      apply jet_ext
      intro j
      rw [jetLift_zR]
      have := AlgHom.congr_fun h4 (sX R j)
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes] at this
      rw [← this, add_sub_cancel_left]

end ReciprocityTheory.ChartRestriction.G.Chart
