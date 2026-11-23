import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.TendstoUnderCofinite
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.ResidueUnit

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

variable {E : Type*} [Field E] [NumberField E]

noncomputable def primeToMod (𝔪 : Ideal (𝓞 E)) : Subgroup (IdealGroup E) where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 E), 𝔪 ≤ v.asIdeal →
    FractionalIdeal.count E v (I : FractionalIdeal (𝓞 E)⁰ E) = 0}
  one_mem' := by simp [FractionalIdeal.count_one]
  mul_mem' := by
    intro I J h1 h2 v hv
    rw [Units.val_mul, FractionalIdeal.count_mul E _ I.ne_zero J.ne_zero, h1 v hv, h2 v hv,
      add_zero]
  inv_mem' := by
    intro I h1 v hv
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, h1 v hv, neg_zero]

def IsResMod (𝔪 : Ideal (𝓞 E)) (x : E) (r : 𝓞 E ⧸ 𝔪) : Prop :=
  ∃ a b : 𝓞 E, b ≠ 0 ∧ IsUnit (Ideal.Quotient.mk 𝔪 b) ∧ x * (b : E) = (a : E) ∧
    r * Ideal.Quotient.mk 𝔪 b = Ideal.Quotient.mk 𝔪 a

def IsHeckeIdeal (𝔪 : Ideal (𝓞 E)) (inf : Eˣ →* ℂˣ) (fin : (𝓞 E ⧸ 𝔪)ˣ →* ℂˣ)
    (ψ : primeToMod 𝔪 →* ℂˣ) : Prop :=
  ∀ (α : Eˣ) (hα : toPrincipalIdeal (𝓞 E) E α ∈ primeToMod 𝔪) (r : (𝓞 E ⧸ 𝔪)ˣ),
    IsResMod 𝔪 (α : E) r → ψ ⟨_, hα⟩ * fin r * inf α = 1

example (𝔪 : Ideal (𝓞 E)) : IsHeckeIdeal 𝔪 1 1 1 := fun _ _ _ _ => by simp

variable (E) in

abbrev Idele := (AdeleRing (𝓞 E) E)ˣ

variable (E) in

noncomputable def principalIdele : Eˣ →* Idele E :=
  Units.map (algebraMap E (AdeleRing (𝓞 E) E)).toMonoidHom

variable (E) in

noncomputable def infPart : Idele E →* (InfiniteAdeleRing E)ˣ :=
  Units.map (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom

variable (E) in

noncomputable def infDiag : Eˣ →* (InfiniteAdeleRing E)ˣ :=
  Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom

noncomputable def finComp (v : HeightOneSpectrum (𝓞 E)) : Idele E →* v.adicCompletion E :=
  (((RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (B := fun v => v.adicCompletionIntegers E) v).comp
      (RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))).toMonoidHom).comp
    (Units.coeHom _)

noncomputable def unitsAt (S : Set (HeightOneSpectrum (𝓞 E))) : Subgroup (Idele E) where
  carrier := {x | ∀ v ∈ S, Valued.v (finComp v x) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro x y h1 h2 v hv
    rw [map_mul, map_mul, h1 v hv, h2 v hv, one_mul]
  inv_mem' := by
    intro x h1 v hv
    have h : Valued.v (finComp v x⁻¹) * Valued.v (finComp v x) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    rwa [h1 v hv, mul_one] at h

noncomputable def localUnits (w : HeightOneSpectrum (𝓞 E)) : Subgroup (Idele E) :=
  unitsAt {w} ⊓ (infPart E).ker ⊓
    ⨅ v : {v // v ≠ w}, (finComp v.1).toHomUnits.ker

def IsIdeleIdeal (x : Idele E) (I : IdealGroup E) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (finComp v x) =
    WithZero.exp (-FractionalIdeal.count E v (I : FractionalIdeal (𝓞 E)⁰ E))

def IsIdeleRes (𝔪 : Ideal (𝓞 E)) (x : Idele E) (r : 𝓞 E ⧸ 𝔪) : Prop :=
  ∃ a : 𝓞 E, Ideal.Quotient.mk 𝔪 a = r ∧ ∀ v : HeightOneSpectrum (𝓞 E), 𝔪 ≤ v.asIdeal →
    Valued.v (finComp v x - algebraMap E (v.adicCompletion E) (a : E)) ≤
      WithZero.exp (-FractionalIdeal.count E v (𝔪 : FractionalIdeal (𝓞 E)⁰ E))

structure IsHeckeIdele (𝔪 : Ideal (𝓞 E)) (inf : (InfiniteAdeleRing E)ˣ →* ℂˣ)
    (fin : (𝓞 E ⧸ 𝔪)ˣ →* ℂˣ) (χ : Idele E →* ℂˣ) : Prop where
  continuous : Continuous χ
  principal : ∀ α : Eˣ, χ (principalIdele E α) = 1
  units : ∀ x ∈ unitsAt Set.univ, ∀ r : (𝓞 E ⧸ 𝔪)ˣ, IsIdeleRes 𝔪 x r →
    χ x = inf (infPart E x) * fin r

example (𝔪 : Ideal (𝓞 E)) : IsHeckeIdele 𝔪 1 1 1 :=
  ⟨continuous_const, fun _ => rfl, fun _ _ _ _ => by simp⟩

def HeckeCompat (𝔪 : Ideal (𝓞 E)) (inf : (InfiniteAdeleRing E)ˣ →* ℂˣ)
    (fin : (𝓞 E ⧸ 𝔪)ˣ →* ℂˣ) (χ : Idele E →* ℂˣ) (ψ : primeToMod 𝔪 →* ℂˣ) : Prop :=
  ∀ (x : Idele E) (I : primeToMod 𝔪) (r : (𝓞 E ⧸ 𝔪)ˣ), IsIdeleIdeal x I → IsIdeleRes 𝔪 x r →
    χ x = inf (infPart E x) * fin r * ψ I

noncomputable def ideleMap (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Idele F →* Idele E :=
  Units.map (adeleMap F E).toMonoidHom

noncomputable def idealMap (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : IdealGroup F →* IdealGroup E :=
  Units.map (FractionalIdeal.extendedHom E (𝓞 E) :
    FractionalIdeal (𝓞 F)⁰ F →+* FractionalIdeal (𝓞 E)⁰ E).toMonoidHom

open Classical in

noncomputable def embInf (φ : E →+* ℂ) : InfiniteAdeleRing E →+* ℂ :=
  (if (InfinitePlace.mk φ).embedding = φ then RingHom.id ℂ else starRingEnd ℂ).comp
    ((InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)).comp
      (Pi.evalRingHom (fun v : InfinitePlace E => v.Completion) (InfinitePlace.mk φ)))

noncomputable def conjRatio : ℂˣ →* ℂˣ :=
  MonoidHom.id ℂˣ / Units.map (starRingEnd ℂ).toMonoidHom

noncomputable def phase : ℂˣ →* ℂˣ :=
  MonoidHom.id ℂˣ /
    Units.map (Complex.ofRealHom.toMonoidHom.comp (normHom : ℂ →*₀ ℝ).toMonoidHom)

noncomputable def infType {ι : Type*} [Fintype ι] (f : ℂˣ →* ℂˣ) (τ : ι → E →+* ℂ) (e : ι → ℤ) :
    (InfiniteAdeleRing E)ˣ →* ℂˣ :=
  ∏ i, (f.comp (Units.map (embInf (τ i)).toMonoidHom)) ^ e i

def galEmb (K : Type*) [Field K] [Algebra K E] (τ₀ : E →+* ℂ) (σ : E ≃ₐ[K] E) : E →+* ℂ :=
  τ₀.comp (σ : E →+* E)

end KStar.Choice
