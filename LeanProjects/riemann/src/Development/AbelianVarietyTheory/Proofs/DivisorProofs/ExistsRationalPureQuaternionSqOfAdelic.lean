import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.PureSq

theorem mul_self_of_re_eq_zero {R : Type*} [CommRing R] {a b : R} (p : ℍ[R, a, b]) (hp : p.re = 0) :
    p * p = algebraMap R ℍ[R, a, b] (a * p.imI ^ 2 + b * p.imJ ^ 2 - a * b * p.imK ^ 2) := by
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, hp] <;> ring

theorem exists_completion_hom_of_real {K : Type} [Field K] (σ : K →+* ℝ) :
    ∃ (w : InfinitePlace K) (f : w.Completion →+* ℝ), ∀ x : K, f (algebraMap K w.Completion x) = σ x := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw, fun x => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv _).symm x)
  refine Eq.trans he ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

variable {F : Type} [Field F] [NumberField F]

theorem isotropic_of_ringHom {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c))
    {k : Type*} [Field k] (φ : AF F →+* k) (ψ : F →+* k)
    (hφ : ∀ x, φ (algebraMap F (AF F) x) = ψ x) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, ψ (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 := by
  rw [mul_self_of_re_eq_zero q hq0] at hqq
  have h1 := congrArg QuaternionAlgebra.re hqq
  simp only [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.re_coe] at h1
  have h2 := congrArg φ h1
  simp only [map_add, map_sub, map_mul, map_pow, hφ] at h2
  refine ⟨![φ q.imI, φ q.imJ, φ q.imK, 1], fun h => by simpa using congrFun h 3, ?_⟩
  simp [Fin.sum_univ_four]
  linear_combination h2

end GlobalTheory.QSA.PureSq

namespace GlobalTheory.QSA.PureSq

variable {F : Type} [Field F] [NumberField F]

theorem isotropic_real {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c)) (σ : F →+* ℝ) :
    ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, σ (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 := by
  obtain ⟨w, f, hf⟩ := exists_completion_hom_of_real σ
  refine isotropic_of_ringHom q hq0 hqq
    (f.comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)) σ
    (fun x => ?_)
  rw [← hf x]
  rfl

theorem isotropic_finite {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : Fin 4 → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 :=
  isotropic_of_ringHom q hq0 hqq ((evalV F v).comp (sndA F)).toRingHom (algebraMap F _)
    (fun x => ((evalV F v).comp (sndA F)).commutes x)

theorem exists_ternary_eq {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) {u₁ u₂ u₃ : F}
    (hu : (u₁, u₂, u₃) ≠ (0, 0, 0)) (h : a * u₁ ^ 2 + b * u₂ ^ 2 - a * b * u₃ ^ 2 = 0) (c : F) :
    ∃ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c := by
  have key : ∀ v₁ v₂ v₃ : F, a * u₁ * v₁ + b * u₂ * v₂ - a * b * u₃ * v₃ ≠ 0 →
      ∃ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c := by
    intro v₁ v₂ v₃ hD
    set D := a * u₁ * v₁ + b * u₂ * v₂ - a * b * u₃ * v₃ with hDdef
    set t := (c - (a * v₁ ^ 2 + b * v₂ ^ 2 - a * b * v₃ ^ 2)) / (2 * D) with ht
    have h2 : (2 : F) * D ≠ 0 := mul_ne_zero two_ne_zero hD
    have ht' : t * (2 * D) = c - (a * v₁ ^ 2 + b * v₂ ^ 2 - a * b * v₃ ^ 2) := div_mul_cancel₀ _ h2
    refine ⟨t * u₁ + v₁, t * u₂ + v₂, t * u₃ + v₃, ?_⟩
    linear_combination t ^ 2 * h + ht'
  by_cases h1 : u₁ = 0
  · by_cases h2 : u₂ = 0
    · have h3 : u₃ ≠ 0 := fun h3 => hu (by simp [h1, h2, h3])
      exact key 0 0 1 (by simp [ha, hb, h3])
    · exact key 0 1 0 (by simp [hb, h2, h1])
  · exact key 1 0 0 (by simp [ha, h1])

theorem exists_rat_of_adelic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 →
    ∀ q : DA F a b, q.re = 0 → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) →
    ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
  intro F _ _ a b ha hb c hc q hq0 hqq
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.LocalQuad.isotropic_of_locally_isotropic GlobalTheory.QNorm.hasseNormSt F
    (ι := Fin 4) (by simp) ![a, b, -(a * b), -c]
    (fun i => by fin_cases i <;> simp [ha, hb, hc])
    (isotropic_real q hq0 hqq) (isotropic_finite q hq0 hqq)
  simp [Fin.sum_univ_four] at hx
  have pure : ∀ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c →
      ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
    intro y₁ y₂ y₃ hy
    refine ⟨⟨0, y₁, y₂, y₃⟩, rfl, ?_⟩
    rw [mul_self_of_re_eq_zero _ rfl]
    change algebraMap F ℍ[F, a, b] (a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2) = _
    rw [hy]
  by_cases h3 : x 3 = 0
  · rw [h3] at hx
    obtain ⟨y₁, y₂, y₃, hy⟩ := exists_ternary_eq ha hb (u₁ := x 0) (u₂ := x 1) (u₃ := x 2)
      (fun h => hx0 (by
        simp only [Prod.mk.injEq] at h
        funext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2, h3]))
      (by linear_combination hx) c
    exact pure y₁ y₂ y₃ hy
  · refine pure (x 0 / x 3) (x 1 / x 3) (x 2 / x 3) ?_
    field_simp
    linear_combination hx

end GlobalTheory.QSA.PureSq
