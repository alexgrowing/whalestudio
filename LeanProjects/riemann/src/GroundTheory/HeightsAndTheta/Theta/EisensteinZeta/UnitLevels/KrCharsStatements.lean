import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.UnitLevels.KrFieldExample

noncomputable section

namespace GroundTheory.Heights₂.Theta

open NumberField NumberField.InfinitePlace IsDedekindDomain ComplexConjugate
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing nonZeroDivisors

section Objects

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsCMQuadratic : Prop :=
  IsTotallyReal F ∧ IsTotallyComplex E ∧ Module.finrank F E = 2

def RootsOfUnityArePlusMinusOne : Prop :=
  ∀ ζ : Eˣ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ζ = 1 ∨ ζ = -1

variable {F E}

def IsCMType (Ψ : Finset (E →+* ℂ)) : Prop :=
  ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ

open Classical in

def extAt (τ : E →+* ℂ) : (InfinitePlace.mk τ).Completion →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then Completion.extensionEmbedding (InfinitePlace.mk τ)
  else (starRingEnd ℂ).comp (Completion.extensionEmbedding (InfinitePlace.mk τ))

def HasAngularType (χ : HeckeCharacter E) (τ : E →+* ℂ) (k : ℤ) : Prop :=
  ∀ z : ((InfinitePlace.mk τ).Completion)ˣ,
    ((χ.infiniteComponent (InfinitePlace.mk τ) z : Circle) : ℂ) =
      (extAt τ (z : (InfinitePlace.mk τ).Completion) /
        (‖extAt τ (z : (InfinitePlace.mk τ).Completion)‖ : ℂ)) ^ k

def HasQuotientType (χ : HeckeCharacter E) (τ : E →+* ℂ) (e : ℤ) : Prop :=
  ∀ z : ((InfinitePlace.mk τ).Completion)ˣ,
    ((χ.infiniteComponent (InfinitePlace.mk τ) z : Circle) : ℂ) =
      (extAt τ (z : (InfinitePlace.mk τ).Completion) /
        conj (extAt τ (z : (InfinitePlace.mk τ).Completion))) ^ (-e)

def IsUnramifiedAt (χ : HeckeCharacter E) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ a ∈ unitsLevel (K := E) w 0, χ.localComponent w a = 1

variable (F) in

def IsTrivialOnBase (χ : HeckeCharacter E) : Prop :=
  ∀ x : IdeleClassGroup F, χ (ideleClassMap F E x) = 1

variable (E) in

def IsQuadraticCharacterOf (η : HeckeCharacter F) : Prop :=
  ∀ x : IdeleClassGroup F, η x = 1 ↔ x ∈ (ideleClassNorm F E).range

def conjPlace (c : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  comapPrime (c : E ≃+* E) w

def IsSplitSelection (c : E ≃ₐ[F] E) (S : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ w ∈ S, conjPlace c w ≠ w ∧ conjPlace c w ∉ S

def unitAt (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) : (w.adicCompletion E)ˣ :=
  Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom x

theorem mem_unitsLevel_zero_of_valued_eq_one {w : HeightOneSpectrum (𝓞 E)}
    {x : (w.adicCompletion E)ˣ} (hx : Valued.v (x : w.adicCompletion E) = 1) :
    x ∈ unitsLevel (K := E) w 0 := by
  refine mem_unitsLevel.2 ⟨hx, ?_⟩
  calc Valued.v ((x : w.adicCompletion E) - 1)
      ≤ max (Valued.v (x : w.adicCompletion E)) (Valued.v (1 : w.adicCompletion E)) :=
        Valuation.map_sub _ _ _
    _ = _ := by simp [hx]

def negOneAt (w : HeightOneSpectrum (𝓞 E)) : unitsLevel (K := E) w 0 :=
  ⟨-1, mem_unitsLevel_zero_of_valued_eq_one (by simp)⟩

theorem unitAt_mem_of_pow_eq_one (w : HeightOneSpectrum (𝓞 E)) {ζ : Eˣ}
    (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) : unitAt w ζ ∈ unitsLevel (K := E) w 0 := by
  obtain ⟨n, hn, h⟩ := hζ
  apply mem_unitsLevel_zero_of_valued_eq_one
  have hζn : unitAt w ζ ^ n = 1 := by
    simp only [unitAt, ← map_pow, h, map_one]
  have hpow : Valued.v (unitAt w ζ : w.adicCompletion E) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hζn, Units.val_one, map_one]
  have h0 : Valued.v (unitAt w ζ : w.adicCompletion E) ≠ 0 := by simp
  rcases lt_trichotomy (Valued.v (unitAt w ζ : w.adicCompletion E)) 1 with hl | he | hg
  · exact absurd hpow (pow_lt_one₀ zero_le hl hn.ne').ne
  · exact he
  · exact absurd hpow (one_lt_pow₀ hg hn.ne').ne'

def rootAt (w : HeightOneSpectrum (𝓞 E)) {ζ : Eˣ} (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) :
    unitsLevel (K := E) w 0 :=
  ⟨unitAt w ζ, unitAt_mem_of_pow_eq_one w hζ⟩

variable (F) in

def IsSplitTypeCharacter (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ))
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (θ : (w : HeightOneSpectrum (𝓞 E)) → unitsLevel (K := E) w 0 →ₜ* Circle)
    (e : (E →+* ℂ) → ℤ) (μ : HeckeCharacter E) : Prop :=
  IsTrivialOnBase F μ ∧ (∀ τ ∈ Ψ, HasQuotientType μ τ (e τ)) ∧
    (∀ w, w ∉ S → conjPlace c w ∉ S → IsUnramifiedAt μ w) ∧
    ∀ w ∈ S, ∀ a : unitsLevel (K := E) w 0, μ.localComponent w a = θ w a

variable (F E) in

def UnramifiedAnticyclotomic : Set (HeckeCharacter E) :=
  {χ | IsTrivialOnBase F χ ∧ (∀ (w : InfinitePlace E) (z : (w.Completion)ˣ), χ.infiniteComponent w z = 1) ∧
    ∀ w, IsUnramifiedAt χ w}

end Objects

section Ties

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem extAt_coe (τ : E →+* ℂ) (x : WithAbs (InfinitePlace.mk τ).1) :
    extAt τ (x : (InfinitePlace.mk τ).Completion) = τ (WithAbs.equiv _ x) := by
  unfold extAt
  split_ifs with h
  · rw [Completion.extensionEmbedding_coe, h]
  · have h' := (embedding_mk_eq τ).resolve_left h
    rw [RingHom.comp_apply, Completion.extensionEmbedding_coe, h', ComplexEmbedding.conjugate_coe_eq]
    simp

omit [NumberField E] in

theorem extAt_surjective [IsTotallyComplex E] (τ : E →+* ℂ) : Function.Surjective (extAt τ) := by
  have hs := Completion.surjective_extensionEmbedding_of_isComplex
    (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
  unfold extAt
  split_ifs
  · exact hs
  · intro y
    obtain ⟨x, hx⟩ := hs (conj y)
    exact ⟨x, by simp [hx]⟩

theorem one_hasAngularType_zero (τ : E →+* ℂ) : HasAngularType (1 : HeckeCharacter E) τ 0 := by
  intro z
  simp [HeckeCharacter.infiniteComponent_apply, HeckeCharacter.toIdele_apply]

theorem not_one_hasAngularType_one [IsTotallyComplex E] (τ : E →+* ℂ) :
    ¬ HasAngularType (1 : HeckeCharacter E) τ 1 := by
  intro h
  obtain ⟨x, hx⟩ := extAt_surjective τ Complex.I
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact Complex.I_ne_zero hx.symm
  have := h (Units.mk0 x hx0)
  simp only [Units.val_mk0, hx, Complex.norm_I, zpow_one] at this
  simp [HeckeCharacter.infiniteComponent_apply, HeckeCharacter.toIdele_apply] at this
  have := congrArg Complex.re this
  simp at this

theorem one_isUnramifiedAt (w : HeightOneSpectrum (𝓞 E)) :
    IsUnramifiedAt (1 : HeckeCharacter E) w := by
  intro a _
  rfl

theorem one_isTrivialOnBase : IsTrivialOnBase F (1 : HeckeCharacter E) := by
  intro x
  rfl

theorem IsQuadraticCharacterOf.sq_eq_one {η : HeckeCharacter F} (h : IsQuadraticCharacterOf E η)
    (h2 : Module.finrank F E = 2) (x : IdeleClassGroup F) : η x ^ 2 = 1 := by
  rw [← map_pow, h, ← h2, ← ideleClassNorm_ideleClassMap]
  exact ⟨_, rfl⟩

omit [NumberField F] [NumberField E] in

theorem isSplitSelection_empty (c : E ≃ₐ[F] E) : IsSplitSelection c ∅ := by
  intro w hw
  simp at hw

variable (E) in

def embeddingImage : Finset (E →+* ℂ) :=
  open Classical in Finset.univ.image fun w : InfinitePlace E ↦ w.embedding

theorem mem_embeddingImage_iff (σ : E →+* ℂ) :
    σ ∈ embeddingImage E ↔ (InfinitePlace.mk σ).embedding = σ := by
  classical
  simp only [embeddingImage, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, rfl⟩
    rw [mk_embedding]
  · intro h
    exact ⟨InfinitePlace.mk σ, h⟩

theorem isCMType_embeddingImage [IsTotallyComplex E] : IsCMType (embeddingImage E) := by
  intro σ
  rw [mem_embeddingImage_iff, mem_embeddingImage_iff, mk_conjugate_eq]
  have hσ : ComplexEmbedding.conjugate σ ≠ σ := IsTotallyComplex.complexEmbedding_not_isReal σ
  rcases embedding_mk_eq σ with h | h
  · rw [h]
    exact ⟨fun _ h' ↦ hσ h'.symm, fun _ ↦ rfl⟩
  · rw [h]
    exact ⟨fun h' ↦ absurd h' hσ, fun h' ↦ absurd rfl h'⟩

end Ties

section Statements

def SplitCharacterExistence.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E →
    RootsOfUnityArePlusMinusOne E → Even (Module.finrank ℚ F) → IsCMType Ψ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), IsSplitSelection c S →
    ∀ (θ : (w : HeightOneSpectrum (𝓞 E)) → unitsLevel (K := E) w 0 →ₜ* Circle),
      (∀ w ∈ S, ∃ n : ℕ, 0 < n ∧ ∀ a, θ w a ^ n = 1) →
    ∀ (e : (E →+* ℂ) → ℤ),
      (∃ μ : HeckeCharacter E, IsSplitTypeCharacter F c Ψ S θ e μ) ↔
        (-1 : ℂ) ^ (∑ τ ∈ Ψ, e τ) * ∏ w ∈ S, ((θ w (negOneAt w) : Circle) : ℂ) = 1

def SplitCharacterDifference.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E →
    RootsOfUnityArePlusMinusOne E → Even (Module.finrank ℚ F) → IsCMType Ψ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), IsSplitSelection c S →
    ∀ (θ : (w : HeightOneSpectrum (𝓞 E)) → unitsLevel (K := E) w 0 →ₜ* Circle),
      (∀ w ∈ S, ∃ n : ℕ, 0 < n ∧ ∀ a, θ w a ^ n = 1) →
    ∀ (e : (E →+* ℂ) → ℤ),
      (UnramifiedAnticyclotomic F E).Finite ∧
      ∀ μ₁ μ₂ : HeckeCharacter E, IsSplitTypeCharacter F c Ψ S θ e μ₁ →
        IsSplitTypeCharacter F c Ψ S θ e μ₂ → μ₁ / μ₂ ∈ UnramifiedAnticyclotomic F E

def SplitCharacterExistenceRoots.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E → IsCMType Ψ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), IsSplitSelection c S →
    ∀ (θ : (w : HeightOneSpectrum (𝓞 E)) → unitsLevel (K := E) w 0 →ₜ* Circle)
      (e : (E →+* ℂ) → ℤ),
      (∃ μ : HeckeCharacter E, IsSplitTypeCharacter F c Ψ S θ e μ) ↔
        ∀ (ζ : Eˣ) (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1),
          (∏ τ ∈ Ψ, (τ (ζ : E)) ^ (-e τ)) * ∏ w ∈ S, ((θ w (rootAt w hζ) : Circle) : ℂ) = 1

def EtaTildeExistence.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)) (η : HeckeCharacter F),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E →
    RootsOfUnityArePlusMinusOne E → Even (Module.finrank ℚ F) → IsCMType Ψ →
    IsQuadraticCharacterOf E η →
    ∀ (n : (E →+* ℂ) → ℤ), (∀ τ ∈ Ψ, Odd (n τ)) →
    ∀ (d : ℕ) (δ : 𝓞 E), 0 < d → δ ^ 2 = -(d : 𝓞 E) →
    ∀ (𝔞 : Ideal (𝓞 F)), Ideal.span {δ} = 𝔞.map (algebraMap (𝓞 F) (𝓞 E)) →
    ∀ (a : IdeleGroup F), IdeleGroup.toInfinite F a = 1 →
      ((IdeleGroup.toFractionalIdeal a : FractionalIdeal (𝓞 F)⁰ F) = (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) →
      ((∃ η' : HeckeCharacter E, (∀ w, IsUnramifiedAt η' w) ∧
          (∀ x : IdeleClassGroup F, η' (ideleClassMap F E x) = η x) ∧
          ∀ τ ∈ Ψ, HasAngularType η' τ (n τ)) ↔
        ((η (IdeleClassGroup.mk F a) : ℂ) *
          ∏ τ ∈ Ψ, (τ (δ : E) / (‖τ (δ : E)‖ : ℂ)) ^ n τ = 1))

def TameCharactersDistinct.Statement : Prop :=
  ∀ (g m : ℕ), g.Prime → 1 ≤ m → (4 * m * (g : ℝ) ^ ((1 : ℝ) / 4) < (g : ℝ) - 1) →
    ∀ ω : (ZMod g)ˣ →* ℂˣ, orderOf ω = g - 1 →
      (∀ k k' : ℤ, |k| ≤ m → |k'| ≤ m → ω ^ (2 * k) = ω ^ (2 * k') → k = k') ∧
      ∀ j : ℤ, (ω ^ (2 * j)) (-1) = 1

def FrameCharactersEven.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)) (η : HeckeCharacter F),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E → IsCMType Ψ →
    IsQuadraticCharacterOf E η →
    ∀ (a a' : ℕ) (κ : (E →+* ℂ) → ℤ), Even a → Even a' →
      ((∃ α β : HeckeCharacter E, (∀ w, IsUnramifiedAt α w) ∧ (∀ w, IsUnramifiedAt β w) ∧
          (∀ x : IdeleClassGroup F, α (ideleClassMap F E x) = η x ^ a') ∧
          (∀ x : IdeleClassGroup F, β (ideleClassMap F E x) = η x ^ a) ∧
          ∀ τ ∈ Ψ, HasAngularType (α / β) τ (-κ τ)) ↔
        (∀ τ ∈ Ψ, Even (κ τ)) ∧
          ∀ ζ : Eˣ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ∏ τ ∈ Ψ, (τ (ζ : E)) ^ (κ τ / 2) = 1)

end Statements

end GroundTheory.Heights₂.Theta
