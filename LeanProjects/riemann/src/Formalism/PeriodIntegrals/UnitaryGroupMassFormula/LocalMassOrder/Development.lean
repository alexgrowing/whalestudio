import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol

noncomputable section

namespace LocMassOrdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory
  NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def primSet (Λ : Set (Fin n → E)) (r : ℕ) : Set (TupV (E := E) v n (r + 1)) :=
  {X | IsPrim v Λ (locF v X)}

def stabilizerConjugateCompact {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) (y : HA (Fv F v) σ J) :
    Set (S0 (Fv F v) σ J P) :=
  {h | y * (h : HA (Fv F v) σ J) * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v}

def orbImg {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) (y : HA (Fv F v) σ J) :
    Set (TupV (E := E) v n (r + 1)) :=
  (fun k : HA (Fv F v) σ J => (k * y) • ratTup (Fv F v) (F0 P)) '' Formalism.L2.SG.TypedSets.Kv σ J Λ v

def FrameHyp {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) (μG : Measure (HA (Fv F v) σ J))
    (μS : Measure (Ssub (Fv F v) σ J P)) (μS0 : Measure (S0 (Fv F v) σ J P))
    (y : HA (Fv F v) σ J) : Prop :=
  StdHyp σ J ψ ∧ (∃ T : F, P.IsStd σ J T) ∧ IsSDLoc σ J v Λ ∧ UnramAt (E := E) v ∧
    μG.IsHaarMeasure ∧ μS.IsHaarMeasure ∧ μS0.IsHaarMeasure ∧
    IsCompatLoc σ J v (F0 P) μG μS0 (omAt σ J ψ v (TFl σ J v P)) ∧
    IsProdU σ J v P μS μS0 (sdE (E := E) ψ v (UIdx r)) ∧
    IsPrim v Λ (locF v (y • ratTup (Fv F v) (F0 P)))

end Defs

def OrbitPrim : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J),
    FrameHyp σ J ψ v P Λ μG μS μS0 y →
    primSet v Λ r ∩ (gramR (Fv F v) σ J ⁻¹' {TFl σ J v P} ∩ IndepV (E := E) (n := n) v (r + 1)) =
      orbImg σ J v P Λ y

def UnimodG : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μG : Measure (HA (Fv F v) σ J)),
    StdHyp σ J ψ → μG.IsHaarMeasure → μG.IsMulRightInvariant

def CompatOrbit : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J),
    FrameHyp σ J ψ v P Λ μG μS μS0 y → μG.IsMulRightInvariant →
    omAt σ J ψ v (TFl σ J v P) (orbImg σ J v P Λ y) * μS0 (stabilizerConjugateCompact σ J v P Λ y) =
      μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v)

def StepC : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J),
    FrameHyp σ J ψ v P Λ μG μS μS0 y →
    μS (KSvT σ J v P Λ y) = μS0 (stabilizerConjugateCompact σ J v P Λ y) * sdE (E := E) ψ v (UIdx r) (UO v r)

def NonDeg : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J),
    FrameHyp σ J ψ v P Λ μG μS μS0 y →
    (μS0 (stabilizerConjugateCompact σ J v P Λ y)).toReal ≠ 0 ∨
      (omAt σ J ψ v (TFl σ J v P) (primSet v Λ r)).toReal = 0

def OmSF : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)), StdHyp σ J ψ →
    ∀ {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)), SFinite (omAt σ J ψ v T)

def SdESF : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)), StdHyp σ J ψ →
    ∀ r : ℕ, SFinite (sdE (E := E) ψ v (UIdx r))

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

end Glue

def IsLatLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Set (Fin n → E)) : Prop :=
  (latLoc (E := E) v Λ).FG ∧
    Submodule.span (Fv F v ⊗[F] E) (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) = ⊤

def NonDegLat : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J),
    FrameHyp σ J ψ v P Λ μG μS μS0 y → IsLatLoc v Λ → (μS0 (stabilizerConjugateCompact σ J v P Λ y)).toReal ≠ 0

end LocMassOrdW
