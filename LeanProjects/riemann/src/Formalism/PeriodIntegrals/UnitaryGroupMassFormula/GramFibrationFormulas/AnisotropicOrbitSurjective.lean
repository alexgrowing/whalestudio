import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.FundamentalDomainPigeonhole

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def FinVolH (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Prop :=
  ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure →
    ∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ ∧ μ 𝓕 < ⊤

def FinVolStab (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin M → E) : Prop :=
  ∀ μ' : Measure (Hstab (AF F) σ J x), μ'.IsHaarMeasure →
    ∃ 𝓕', IsFundamentalDomain (HstabFin (AF F) σ J x) 𝓕' μ' ∧ μ' 𝓕' < ⊤

def X0int {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin M → Fv F v ⊗[F] E) :=
  {y | y ∈ latW b v ∧ (∃ z ∈ latW (M := M) b v, hR (Fv F v) σ J y z = 1) ∧ qR (Fv F v) σ J y = 0}

def AnisotropicOrbitSurjective : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (x : Fin 1 → Fin M → E) (β : F), β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
      let X := {y : Fin 1 → Fin M → AF F ⊗[F] E | qR (AF F) σ J (y 0) = algebraMap F (AF F) β}
      (∀ y ∈ X, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) ∧
      Continuous (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) x) ∧
      ∀ U : Set (HA (AF F) σ J), IsOpen U →
        ∃ O, IsOpen O ∧ (fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) x) '' U = O ∩ X

def IsotropicOrbitSurjective : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ x : Fin 1 → Fin M → E, x 0 ≠ 0 → hE σ J (x 0) (x 0) = 0 →
      let Xv := fun (v : HeightOneSpectrum (𝓞 F)) (y : Fin 1 → Fin M → AF F ⊗[F] E) => projV v (projFin y)
      let X0 := {y : Fin 1 → Fin M → AF F ⊗[F] E | qR (AF F) σ J (y 0) = 0 ∧
        FreeT (F := F) (E := E) (Ainf F) (projInf y) ∧ (∀ v, FreeT (F := F) (E := E) (Fv F v) (Xv v y)) ∧
        ∀ᶠ v in Filter.cofinite, Xv v y 0 ∈ X0int b σ J v}
      (∀ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x ∈ X0) ∧
      (∀ y ∈ X0, ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) ∧
      ∀ (U : Set (HA (AF F) σ J)) (g : HA (AF F) σ J), IsOpen U → g ∈ U →
        ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (Ui : Set (Fin 1 → Fin M → Ainf F ⊗[F] E))
          (Uv : ∀ v, Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsOpen Ui ∧ (∀ v ∈ S, IsOpen (Uv v)) ∧
          g • ratTup (F := F) (AF F) x ∈ {y | projInf y ∈ Ui ∧ ∀ v, (v ∈ S → Xv v y ∈ Uv v) ∧
            (v ∉ S → Xv v y 0 ∈ X0int b σ J v)} ∧
          {y ∈ X0 | projInf y ∈ Ui ∧ ∀ v, (v ∈ S → Xv v y ∈ Uv v) ∧ (v ∉ S → Xv v y 0 ∈ X0int b σ J v)} ⊆
            (fun h : HA (AF F) σ J => h • ratTup (F := F) (AF F) x) '' U

def UnitaryStabilizerQuotient : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧
    (∀ (x : Fin 1 → Fin M → E) (β : F), β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
      ∃ (M' : ℕ) (J' : Matrix (Fin M') (Fin M') E) (Ψ : Hstab (AF F) σ J x ≃ₜ* HA (AF F) σ J'),
        M' + 1 = M ∧ IsHermND σ J' ∧
        ∀ u, u ∈ HstabFin (AF F) σ J x ↔ Ψ u ∈ HFinIn (AF F) σ J') ∧
    ∀ x : Fin 1 → Fin M → E, x 0 ≠ 0 → hE σ J (x 0) (x 0) = 0 → 3 ≤ M →
      (∀ μ' : Measure (Hstab (AF F) σ J x), μ'.IsHaarMeasure → μ'.IsMulRightInvariant) ∧
      ((∀ (J₁ : Matrix (Fin (M - 2)) (Fin (M - 2)) E), IsHermND σ J₁ → FinVolH σ J₁) → FinVolStab σ J x)

def OrbitUnfoldingFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (x : Fin 1 → Fin M → E) (X : Set (Fin 1 → Fin M → E)) (gy : (Fin 1 → Fin M → E) → HA (AF F) σ J),
      (∀ y, y ∈ X ↔ ∃ g ∈ HFinIn (AF F) σ J, g • ratTup (F := F) (AF F) x = ratTup (F := F) (AF F) y) →
      (∀ y ∈ X, gy y ∈ HFinIn (AF F) σ J ∧ gy y • ratTup (F := F) (AF F) y = ratTup (F := F) (AF F) x) →
    ∀ (μ : Measure (HA (AF F) σ J)) (μ' : Measure (Hstab (AF F) σ J x))
      (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) 𝓕 𝓕',
      μ.IsHaarMeasure → μ.IsMulRightInvariant → μ'.IsHaarMeasure → μ'.IsMulRightInvariant →
      IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → IsFundamentalDomain (HstabFin (AF F) σ J x) 𝓕' μ' →
      Formalism.MainNotions.StandardLattice.Carries F E σ M J x μ μ' ν →
      ∀ (s : (Fin 1 → Fin M → AF F ⊗[F] E) → HA (AF F) σ J),
        (∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) → s y • ratTup (F := F) (AF F) x = y) →
      ∀ φ : HA (AF F) σ J → ℝ≥0∞, Measurable φ →
        (∀ u ∈ HstabFin (AF F) σ J x, ∀ h, φ ((u : HA (AF F) σ J) * h) = φ h) →
        ∫⁻ h in 𝓕, ∑' y : X, φ (gy y * h) ∂μ =
          ∫⁻ y, ∫⁻ u in 𝓕', φ ((u : HA (AF F) σ J) * (s y)⁻¹) ∂μ' ∂ν

end PI.GramFibrationFormulas
