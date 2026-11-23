import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CNorm

def pows (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) : Subgroup G := U.map (powMonoidHom p)

def pIdx (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) : ℕ := (pows p U).relIndex U

def pTor (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) : ℕ :=
  Nat.card {x : G // x ∈ U ∧ x ^ p = 1}

def nrm {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) : A →* A where
  toFun a := ∏ i ∈ Finset.range n, σ^[i] a
  map_one' := by simp [iterate_map_one]
  map_mul' a b := by simp [iterate_map_mul, Finset.prod_mul_distrib]

def dif {A : Type} [CommGroup A] (σ : A →* A) : A →* A where
  toFun a := σ a / a
  map_one' := by simp
  map_mul' a b := by rw [map_mul, mul_div_mul_comm]

def fix {A : Type} [CommGroup A] (σ : A →* A) : Subgroup A := σ.eqLocus (MonoidHom.id A)

theorem nrm_apply {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) (a : A) :
    nrm σ n a = ∏ i ∈ Finset.range n, σ^[i] a := rfl

theorem dif_apply {A : Type} [CommGroup A] (σ : A →* A) (a : A) : dif σ a = σ a / a := rfl

open NumberField IsDedekindDomain Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.CNorm.mem_fix {A : Type} [CommGroup A] (σ : A →* A) (a : A) :
    a ∈ _root_.GlobalTheory.CNorm.fix σ ↔ σ a = a := Iff.rfl

def oneUnits {O : Type} [CommRing O] (t : O) : Subgroup Oˣ :=
  (Units.map (Ideal.Quotient.mk (Ideal.span {t}) : O →* O ⧸ Ideal.span {t})).ker

def powSub (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) : Subgroup Fˣ where
  carrier := {x | ∃ r : L, r ^ p = φ (x : F)}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r * s, by rw [mul_pow, hr, hs, Units.val_mul, map_mul]⟩
  inv_mem' := by
    rintro a ⟨r, hr⟩
    exact ⟨r⁻¹, by rw [inv_pow, hr, Units.val_inv_eq_inv_val, map_inv₀]⟩

open NumberField IsDedekindDomain Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.CNorm.mem_powSub (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L)
    (x : Fˣ) : x ∈ _root_.GlobalTheory.CNorm.powSub p φ ↔ ∃ r : L, r ^ p = φ (x : F) := Iff.rfl

def kNorm (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) : Subgroup Fˣ :=
  (Units.map (Algebra.norm L : AdjoinRoot (X ^ p - C (φ δ) : L[X]) →* L)).range.comap
    (Units.map (φ : F →* L))

open NumberField IsDedekindDomain Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.CNorm.mem_kNorm (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L)
    (δ : F) (x : Fˣ) :
    x ∈ _root_.GlobalTheory.CNorm.kNorm p φ δ ↔ ∃ y : (AdjoinRoot (X ^ p - C (φ δ) : L[X]))ˣ,
      Algebra.norm L (y : AdjoinRoot (X ^ p - C (φ δ) : L[X])) = φ (x : F) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by simpa using congrArg Units.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Units.ext (by simpa using hy)⟩

structure IsKum (p : ℕ) {F E : Type} [Field F] [Field E] [Algebra F E] (ζ δ : F) (θ : E)
    (σ : E ≃ₐ[F] E) : Prop where
  prime : p.Prime
  root : IsPrimitiveRoot ζ p
  nonpow : ∀ r : F, r ^ p ≠ δ
  pow : θ ^ p = algebraMap F E δ
  conj : σ θ = algebraMap F E ζ * θ
  gen : Algebra.adjoin F {θ} = ⊤

def TNorm (F E L : Type) [Field F] [Field E] [Algebra F E] [Field L] [Algebra F L] (x : F) : Prop :=
  ∃ y : L ⊗[F] E, Algebra.norm L y = algebraMap F L x

section
variable (p : ℕ) (F : Type) [Field F] [NumberField F]

def finPow (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  ⨅ v ∈ S, powSub p (algebraMap F (v.adicCompletion F))

def finNorm (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  ⨅ v ∈ S, kNorm p (algebraMap F (v.adicCompletion F)) δ

def tNon (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  Set.ncard {v : HeightOneSpectrum (𝓞 F) |
    v ∈ S ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ}

def AdmP (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  GlobalTheory.QNorm.admitted F S ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v.valuation F (p : F) = 1

end

def LocNorm (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (x : F) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F), TNorm F E (v.adicCompletion F) x) ∧
    ∀ a : Algebra F ℝ, @TNorm F E ℝ _ _ _ _ a x

def NP (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] : Prop :=
  ∀ x : F, x ≠ 0 → LocNorm F E x → ∃ y : E, Algebra.norm F y = x

end GlobalTheory.CNorm

end
