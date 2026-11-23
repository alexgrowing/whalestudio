import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.CardOfIsFiniteLength

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem locLen_le_of_exact {O B K : Type} [CommRing O] [CommRing B] [Algebra O B] [Field K] [Algebra O K]
    (σ : B →ₐ[O] K) {M N P : Type} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (f : M →ₗ[B] N) (g : N →ₗ[B] P) (h : Function.Exact f g) :
    locLen σ N ≤ locLen σ M + locLen σ P := by
  haveI : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
  exact Formalism.MainNotions.V.Pf.V2.length_le_of_exact (LocalizedModule.map (RingHom.ker σ).primeCompl f)
    (LocalizedModule.map (RingHom.ker σ).primeCompl g) (LocalizedModule.map_exact _ f g h)

theorem UpperTheory.V.Alg.M.locLen_aPiece_sup_span_sq_le_add :
    ∀ (O K A : Type) [CommRing O] [Field K] [Algebra O K] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
      (σ : 𝒜 0 →ₐ[O] K) (J : Ideal A), J.IsHomogeneous 𝒜 → ∀ (d : ℤ) (t : A), t ∈ 𝒜 d → ∀ w : ℤ,
      locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w) ≤
        locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t}) (w - d)) + locLen σ (aPiece 𝒜 (J ⊔ Ideal.span {t}) w) := by
  intro O K A _ _ _ _ _ 𝒜 _ σ J hJ d t ht w
  have h1 : J ⊔ Ideal.span {t} ≤ Submodule.comap (LinearMap.mulLeft A t) (J ⊔ Ideal.span {t ^ 2}) := by
    intro a ha
    obtain ⟨j, hj, b, hb, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    show t * (j + c * t) ∈ J ⊔ Ideal.span {t ^ 2}
    rw [show t * (j + c * t) = t * j + c * t ^ 2 by ring]
    exact Submodule.add_mem_sup (J.mul_mem_left _ hj) (Ideal.mem_span_singleton'.2 ⟨c, rfl⟩)
  have h2 : J ⊔ Ideal.span {t ^ 2} ≤ Submodule.comap (LinearMap.id : A →ₗ[A] A) (J ⊔ Ideal.span {t}) :=
    sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self t two_ne_zero)) J
  let F : (A ⧸ (J ⊔ Ideal.span {t})) →ₗ[𝒜 0] A ⧸ (J ⊔ Ideal.span {t ^ 2}) :=
    (Submodule.mapQ _ _ (LinearMap.mulLeft A t) h1).restrictScalars (𝒜 0)
  let G : (A ⧸ (J ⊔ Ideal.span {t ^ 2})) →ₗ[𝒜 0] A ⧸ (J ⊔ Ideal.span {t}) :=
    (Submodule.mapQ _ _ (LinearMap.id : A →ₗ[A] A) h2).restrictScalars (𝒜 0)
  have hF : ∀ a : A, F (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (t * a) := fun a => rfl
  have hG : ∀ a : A, G (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := fun a => rfl
  have hF' : ∀ x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t}) (w - d), F x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨t * a, ?_, (hF a).symm⟩
    have := SetLike.GradedMul.mul_mem ht (show a ∈ 𝒜 (w - d) from ha)
    rwa [add_sub_cancel] at this
  have hG' : ∀ x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t ^ 2}) w, G x ∈ aPiece 𝒜 (J ⊔ Ideal.span {t}) w := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (hG a).symm⟩
  refine locLen_le_of_exact σ (F.restrict hF') (G.restrict hG') ?_
  rintro ⟨_, a, ha, rfl⟩
  constructor
  · intro h
    have h0 : Ideal.Quotient.mk (J ⊔ Ideal.span {t}) a = 0 := congrArg Subtype.val h
    obtain ⟨j, hj, b, hb, hab⟩ := Submodule.mem_sup.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    have ha' : a ∈ 𝒜 w := ha
    have e1 : ((DirectSum.decompose 𝒜 (t * c)) (d + (w - d)) : A) = t * DirectSum.decompose 𝒜 c (w - d) :=
      DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 ht
    rw [add_sub_cancel] at e1
    have e2 : a = (DirectSum.decompose 𝒜 j w : A) + t * DirectSum.decompose 𝒜 c (w - d) := by
      rw [← e1, ← DirectSum.decompose_of_mem_same 𝒜 ha', ← hab, DirectSum.decompose_add, mul_comm c t]
      rfl
    refine ⟨⟨Ideal.Quotient.mk _ (DirectSum.decompose 𝒜 c (w - d) : A),
      ⟨_, (DirectSum.decompose 𝒜 c (w - d)).2, rfl⟩⟩, Subtype.ext ?_⟩
    show Ideal.Quotient.mk _ (t * (DirectSum.decompose 𝒜 c (w - d) : A)) = Ideal.Quotient.mk _ a
    rw [eq_comm, Ideal.Quotient.eq, e2, add_sub_cancel_right]
    exact Submodule.mem_sup_left (hJ w hj)
  · rintro ⟨⟨_, c, hc, rfl⟩, h⟩
    rw [← h]
    apply Subtype.ext
    show Ideal.Quotient.mk (J ⊔ Ideal.span {t}) (t * c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Submodule.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))
