import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Development

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

def K1 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (g : ℕ) (P : Frame E n r) : Set (HA (Fv F v) σ J) :=
  {k | k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v ∧ ∀ a, ∃ y ∈ latLoc (E := E) v Λ,
    locF v (k • ratTup (Fv F v) (F0 P)) a - locF v (ratTup (Fv F v) (F0 P)) a =
      sc (E := E) v (g : Fv F v) • y}

def UOg {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (g r : ℕ) : Set (UIdx r → Fv F v ⊗[F] E) :=
  {x | ∀ p, sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2 * (g : Fv F v)⁻¹) * x p ∈ OEv (E := E) v}

def stabilizerCompact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (P : Frame E n r) : Set (S0 (Fv F v) σ J P) :=
  Subtype.val ⁻¹' Formalism.L2.SG.TypedSets.Kv σ J Λ v

theorem stabilizer_compact_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (P : Frame E n r) :
    LocMassOrdW.stabilizerConjugateCompact σ J v P Λ 1 = stabilizerCompact σ J v Λ P := by
  ext h
  simp [LocMassOrdW.stabilizerConjugateCompact, stabilizerCompact]

theorem KSv_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) {r : ℕ} (P : Frame E n r) :
    KSvT σ J v P Λ 1 = KSv σ J v P Λ := by
  ext s
  simp [KSvT, KSv]

def StepOm : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E))
    (T T' : F) (κ : HA (Fv F v) σ J) (μG : Measure (HA (Fv F v) σ J))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (μS0' : Measure (S0 (Fv F v) σ J P')),
    StdHyp σ J ψ → P.IsStd σ J T → P'.IsStd σ J T' → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    g.Prime → (g : 𝓞 F) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g → etaV (E := E) v = 1 →
    κ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v →
    (∀ a, ∃ y ∈ latLoc (E := E) v Λ,
      locF v (κ • ratTup (Fv F v) (F0 P')) a - locF v (ratTup (Fv F v) (F0 P)) a =
        sc (E := E) v (g : Fv F v) • y) →
    μG.IsHaarMeasure →
    μS0.IsHaarMeasure → IsCompatLoc σ J v (F0 P) μG μS0 (omAt σ J ψ v (TFl σ J v P)) →
    μS0'.IsHaarMeasure → IsCompatLoc σ J v (F0 P') μG μS0' (omAt σ J ψ v (TFl σ J v P')) →
    IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) → IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P'))) →
    LocMassOrdW.IsLatLoc v Λ →
    (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 → (μS0' (stabilizerCompact σ J v Λ P')).toReal ≠ 0 →
    Mv σ J ψ v (TFl σ J v P) (TFl σ J v P') (OmTyp v Λ g r) *
        ((μS0 (stabilizerCompact σ J v Λ P)).toReal * (μS0' (stabilizerCompact σ J v Λ P')).toReal) =
      (μG (Formalism.L2.SG.TypedSets.Kv σ J Λ v)).toReal * (μG (K1 σ J v Λ g P)).toReal

def StepU : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ),
    StdHyp σ J ψ → g.Prime → (g : 𝓞 F) ∈ v.asIdeal →
    volU (E := E) ψ v (deepCongruenceVolume v g r) =
      (sdE (E := E) ψ v (UIdx r) (UO v r)).toReal * (sdE (E := E) ψ v (UIdx r) (UOg (E := E) v g r)).toReal

def StepIdx : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P : Frame E n r) (Λ : Set (Fin n → E))
    (T : F) (μG : Measure (HA (Fv F v) σ J)) (μS0 : Measure (S0 (Fv F v) σ J P)),
    StdHyp σ J ψ → P.IsStd σ J T → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    g.Prime → (g : 𝓞 F) ∈ v.asIdeal → Ideal.absNorm v.asIdeal = g → etaV (E := E) v = 1 →
    IsPrim v Λ (locF v (ratTup (Fv F v) (F0 P))) → μG.IsHaarMeasure → LocMassOrdW.IsLatLoc v Λ →
    μS0.IsHaarMeasure → (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0 →
    (μG (Formalism.L2.SG.TypedSets.Knatv σ J Λ P g v)).toReal *
        (sdE (E := E) ψ v (UIdx r) (UOg (E := E) v g r)).toReal =
      (μG (K1 σ J v Λ g P)).toReal * (sdE (E := E) ψ v (UIdx r) (UO v r)).toReal

def StepPos : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ),
    StdHyp σ J ψ → g.Prime → (g : 𝓞 F) ∈ v.asIdeal →
    (sdE (E := E) ψ v (UIdx r) (UO v r)).toReal ≠ 0 →
      (sdE (E := E) ψ v (UIdx r) (UOg (E := E) v g r)).toReal ≠ 0

def NonDegT : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)),
    LocMassOrdW.FrameHyp σ J ψ v P Λ μG μS μS0 1 →
    (LocMassOrdW.IsLatLoc v Λ ∧ (μS0 (stabilizerCompact σ J v Λ P)).toReal ≠ 0) ∨
      ((μS0 (stabilizerCompact σ J v Λ P)).toReal = 0 ∧ omAt σ J ψ v (TFl σ J v P) (LocMassOrdW.primSet v Λ r) = 0)

theorem arith (M a a' k k1 kn s s' u ug : ℝ) (hM : M * (a * a') = k * k1) (hs : s = a * u)
    (hs' : s' = a' * u) (hidx : kn * ug = k1 * u) (ha : a ≠ 0) (ha' : a' ≠ 0) (hug : u ≠ 0 → ug ≠ 0) :
    M / (u * ug) = k * kn / (s * s') := by
  subst hs hs'
  by_cases hu : u = 0
  · subst hu
    simp
  · have hug' := hug hu
    rw [div_eq_div_iff (mul_ne_zero hu hug') (mul_ne_zero (mul_ne_zero ha hu) (mul_ne_zero ha' hu))]
    linear_combination (u * u) * hM - (k * u) * hidx

def LatOfGlob : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Set (Fin n → E)),
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    LocMassOrdW.IsLatLoc v Λ

end PI.LocMassTypW
