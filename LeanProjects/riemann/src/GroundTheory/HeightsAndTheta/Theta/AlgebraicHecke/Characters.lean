import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.UnitLevels.KrCharsStatements

noncomputable section

namespace GroundTheory.Heights₂.Theta

open NumberField NumberField.InfinitePlace IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  ComplexConjugate WithZero
open GroundTheory.Global
open scoped nonZeroDivisors

section Objects

variable (E : Type*) [Field E] [NumberField E]

def IsOneModTimes (𝔪 : Ideal (𝓞 E)) (α : E) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔪 →
    v.valuation E (α - 1) ≤ exp (-(multiplicity v.asIdeal 𝔪 : ℤ))

variable (LL : Type*) [Field LL] (ι : LL →+* ℂ)

structure AlgHeckeCharacter where

  modulus : Ideal (𝓞 E)
  modulus_ne_bot : modulus ≠ ⊥

  toHom : idealsPrimeTo modulus →* LLˣ

  infType : (E →+* ℂ) → ℤ

  map_principal : ∀ (α : Eˣ) (I : idealsPrimeTo modulus),
    ((I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (α : E) →
    IsOneModTimes E modulus (α : E) →
    ι (toHom I : LL) = ∏ σ : E →+* ℂ, σ (α : E) ^ (-infType σ)

namespace AlgHeckeCharacter

variable {E LL ι} (ch : AlgHeckeCharacter E LL ι)

def HasWeight (w : ℤ) : Prop :=
  ∀ σ : E →+* ℂ, ch.infType σ + ch.infType (ComplexEmbedding.conjugate σ) = -w

def IsDefinedModulo (𝔣 : Ideal (𝓞 E)) : Prop :=
  𝔣 ∣ ch.modulus ∧ ∀ (α : Eˣ) (I : idealsPrimeTo ch.modulus),
    ((I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (α : E) →
    IsOneModTimes E 𝔣 (α : E) →
    ι (ch.toHom I : LL) = ∏ σ : E →+* ℂ, σ (α : E) ^ (-ch.infType σ)

def conductor : Ideal (𝓞 E) :=
  sSup {𝔣 | ch.IsDefinedModulo 𝔣}

def IsAttached (w : ℤ) (χ : HeckeCharacter E) : Prop :=
  (∀ (x : IdeleGroup E) (hx : x ∈ IdeleGroup.primeToLevel ch.modulus),
    ((χ.toIdele x : Circle) : ℂ) =
      ι (ch.toHom ⟨IdeleGroup.toFractionalIdeal x,
          IdeleGroup.toFractionalIdeal_mem_idealsPrimeTo hx⟩ : LL) *
        (((FractionalIdeal.absNorm ((IdeleGroup.toFractionalIdeal x :
          (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) : ℚ) : ℝ) ^
            (-(w : ℝ) / 2) : ℝ)) ∧
  ∀ σ : E →+* ℂ, HasAngularType χ σ (ch.infType σ - ch.infType (ComplexEmbedding.conjugate σ))

theorem isDefinedModulo_modulus : ch.IsDefinedModulo ch.modulus :=
  ⟨dvd_rfl, ch.map_principal⟩

theorem modulus_le_conductor : ch.modulus ≤ ch.conductor :=
  le_sSup ch.isDefinedModulo_modulus

end AlgHeckeCharacter

end Objects

section Norm

variable {E : Type*} [Field E] [NumberField E]

theorem prod_embeddings_eq_norm (x : E) :
    ∏ σ : E →+* ℂ, σ x = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast] at h
  rw [h]
  exact (Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ ↦ σ x) (fun σ ↦ σ x)
    fun _ ↦ rfl)

omit [NumberField E] in

theorem conjugate_conjugate_embedding (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
  RingHom.ext fun x ↦ by simp

theorem algebraNorm_pos [IsTotallyComplex E] {x : E} (hx : x ≠ 0) :
    0 < Algebra.norm ℚ x := by
  classical
  have hfib : ∀ w : InfinitePlace E,
      ∏ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ ↦ InfinitePlace.mk σ = w), σ x =
        ((Complex.normSq (w.embedding x) : ℝ) : ℂ) := by
    intro w
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h ↦
      IsTotallyComplex.complexEmbedding_not_isReal w.embedding h.symm
    have hset : Finset.univ.filter (fun σ : E →+* ℂ ↦ InfinitePlace.mk σ = w) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      conv_lhs => rw [← mk_embedding w]
      rw [mk_eq_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · right
          rw [← h, conjugate_conjugate_embedding]
      · rintro (h | h)
        · exact Or.inl h
        · right
          rw [h, conjugate_conjugate_embedding]
    rw [hset, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  have key : ∏ σ : E →+* ℂ, σ x =
      ((∏ w : InfinitePlace E, Complex.normSq (w.embedding x) : ℝ) : ℂ) := by
    rw [← Finset.prod_fiberwise Finset.univ (fun σ : E →+* ℂ ↦ InfinitePlace.mk σ) (fun σ ↦ σ x),
      Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun w _ ↦ hfib w
  rw [prod_embeddings_eq_norm, ← Complex.ofReal_ratCast] at key
  have hre : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace E, Complex.normSq (w.embedding x) :=
    Complex.ofReal_injective key
  have hpos : 0 < ∏ w : InfinitePlace E, Complex.normSq (w.embedding x) :=
    Finset.prod_pos fun w _ ↦ Complex.normSq_pos.2 ((map_ne_zero w.embedding).2 hx)
  rw [← hre] at hpos
  exact_mod_cast hpos

end Norm

section NormCharacter

variable (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E]
variable (LL : Type*) [Field LL] [CharZero LL] (ι : LL →+* ℂ)

def absNormUnits : (FractionalIdeal (𝓞 E)⁰ E)ˣ →* ℚˣ :=
  Units.map (FractionalIdeal.absNorm : FractionalIdeal (𝓞 E)⁰ E →*₀ ℚ).toMonoidHom

omit [IsTotallyComplex E] in
theorem absNormUnits_apply (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    ((absNormUnits E I : ℚˣ) : ℚ) = FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 E)⁰ E) :=
  rfl

def normCharacter : AlgHeckeCharacter E LL ι where
  modulus := ⊤
  modulus_ne_bot := top_ne_bot
  toHom := (Units.map (algebraMap ℚ LL).toMonoidHom).comp
    ((absNormUnits E).comp (idealsPrimeTo (⊤ : Ideal (𝓞 E))).subtype)
  infType := fun _ ↦ -1
  map_principal := by
    intro α I hI _
    simp only [neg_neg, zpow_one]
    rw [prod_embeddings_eq_norm]
    change ι (algebraMap ℚ LL ((absNormUnits E (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : ℚˣ) : ℚ)) = _
    rw [absNormUnits_apply, hI, FractionalIdeal.absNorm_span_singleton, eq_ratCast, map_ratCast,
      abs_of_pos (algebraNorm_pos α.ne_zero)]

variable {E LL ι}

theorem normCharacter_apply (I : idealsPrimeTo ((normCharacter E LL ι).modulus)) :
    (((normCharacter E LL ι).toHom I : LLˣ) : LL) =
      ((FractionalIdeal.absNorm ((I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
        FractionalIdeal (𝓞 E)⁰ E) : ℚ) : LL) := by
  change algebraMap ℚ LL ((absNormUnits E (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : ℚˣ) : ℚ) = _
  rw [absNormUnits_apply, eq_ratCast]

theorem normCharacter_hasWeight : (normCharacter E LL ι).HasWeight 2 := by
  intro σ
  simp [normCharacter]

theorem normCharacter_conductor : (normCharacter E LL ι).conductor = ⊤ :=
  top_le_iff.1 (normCharacter E LL ι).modulus_le_conductor

theorem normCharacter_isAttached : (normCharacter E LL ι).IsAttached 2 1 := by
  refine ⟨fun x hx ↦ ?_, fun σ ↦ ?_⟩
  · have hne : (FractionalIdeal.absNorm ((IdeleGroup.toFractionalIdeal x :
        (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) : ℚ) ≠ 0 :=
      FractionalIdeal.absNorm_eq_zero_iff.not.2 (Units.ne_zero _)
    have hne' : ((FractionalIdeal.absNorm ((IdeleGroup.toFractionalIdeal x :
        (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast hne
    rw [normCharacter_apply, map_ratCast]
    change ((1 : Circle) : ℂ) = _
    rw [Circle.coe_one]
    norm_num
    rw [Real.rpow_neg_one, Complex.ofReal_inv]
    push_cast
    field_simp
  · simpa [normCharacter] using one_hasAngularType_zero σ

end NormCharacter

end GroundTheory.Heights₂.Theta
