import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.AnisotropicOrbitSurjective

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsQFib (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v))
    (fq : Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsFibreFamily μ (fun X => qR (Fv F v) σ J (X 0)) id {X | X 0 ≠ 0} ν Set.univ fq

def IsQFibInf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F))
    (fq : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) : Prop :=
  IsFibreFamily μ (fun X => qR (Ainf F) σ J (X 0)) id {X | FreeT (F := F) (E := E) (Ainf F) X} ν Set.univ fq

def resCard (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)

def modF {v : HeightOneSpectrum (𝓞 F)} (ν : Measure (Fv F v)) (a : Fv F v) : ℝ≥0∞ :=
  ν ((fun t => a * t) '' (v.adicCompletionIntegers F : Set (Fv F v))) / ν (v.adicCompletionIntegers F)

def modT {d M n : ℕ} (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (a : Fv F v) : ℝ≥0∞ :=
  μ ((fun X => a • X) '' latV b v) / μ (latV b v)

def FstarT {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] (χ : R → ℂ) (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ)
    (b : R) : ℂ :=
  ∫ X, φ X * χ (b * qR R σ J (X 0)) ∂μ

def FiniteFibreMeasureFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → 2 ≤ M →
    SelfDual μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) → SelfDual ν (fun s t => psiV F ψ v (s * t)) →
    (∃ fq, IsQFib σ J v μ ν fq) ∧
    ∀ fq, IsQFib σ J v μ ν fq →
      (∀ φ, IsSB φ →
        Continuous (fun β => ∫ X, φ X ∂(fq β)) ∧
        IsContDensity μ (fun X => qR (Fv F v) σ J (X 0)) id ν φ (fun β => ∫ X, φ X ∂(fq β)) ∧
        (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ β, ∫⁻ X, ‖φ X‖ₑ ∂(fq β) ≤ C) ∧
        ∀ β, ∫ X, φ X ∂(fq β) =
          ∫ s, FstarT (psiV F ψ v) σ J μ φ s * psiV F ψ v (-(s * β)) ∂ν) ∧
      (∀ (a : Fv F v), a ≠ 0 → ∀ (φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φ → ∀ β,
        ∫⁻ X, φ (a • X) ∂(fq β) = modF ν a ^ 2 / modT b μ a * ∫⁻ X, φ X ∂(fq (a ^ 2 * β))) ∧
      (IsGoodV b σ J v (psiV F ψ v) → 3 ≤ M →
        (∀ β ∈ v.adicCompletionIntegers F,
          ‖∫ X, (latV (n := 1) (M := M) b v).indicator (fun _ => (1 : ℂ)) X ∂(fq β) - 1‖ ≤ 2 * (resCard v : ℝ) ^ (1 - (M : ℤ))) ∧
        ∀ β ∉ v.adicCompletionIntegers F, ∫ X, (latV (n := 1) (M := M) b v).indicator (fun _ => (1 : ℂ)) X ∂(fq β) = 0)

def ArchimedeanFibreFamily : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → 2 ≤ M →
    SelfDual μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) → SelfDual ν (fun s t => psiInf F ψ (s * t)) →
    (∃ fq, IsQFibInf σ J μ ν fq) ∧
    ∀ fq, IsQFibInf σ J μ ν fq →
      (∀ φ, Continuous φ → RapidDecay b φ →
        Continuous (fun β => ∫ X, φ X ∂(fq β)) ∧
        IsContDensity μ (fun X => qR (Ainf F) σ J (X 0)) id ν φ (fun β => ∫ X, φ X ∂(fq β)) ∧
        ∀ k : ℕ, ∃ C : ℝ, ∀ β : Ainf F, (1 + ‖β‖) ^ k * (∫⁻ X, ‖φ X‖ₑ ∂(fq β)).toReal ≤ C ∧
          ∫⁻ X, ‖φ X‖ₑ ∂(fq β) < ⊤) ∧
      ∀ (a a' : Ainf F), a * a' = 1 → ∀ (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞), Measurable φ → ∀ β,
        ∫⁻ X, φ (a • X) ∂(fq β) =
          ENNReal.ofReal (∏ w, ‖a w‖ ^ (2 - 2 * (M : ℝ))) * ∫⁻ X, φ X ∂(fq (a ^ 2 * β))

def GlobalDensityProductFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → 3 ≤ M →
    ∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F))
      (μv : ∀ v, Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (Fv F v)),
      SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) → SelfDual νi (fun s t => psiInf F ψ (s * t)) →
      (∀ v, SelfDual (μv v) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))) →
      (∀ v, SelfDual (νv v) (fun s t => psiV F ψ v (s * t))) →
    ∀ (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
      IsQFibInf σ J μi νi fi → (∀ v, IsQFib σ J v (μv v) (νv v) (fv v)) →
    ∀ β : F, ∃ ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E),
      (β ≠ 0 → Formalism.MainNotions.StandardLattice.IsDxDq F E σ M J ψ β ν) ∧
      (∀ g : HA (AF F) σ J, ν.map (fun X => g • X) = ν) ∧
      (∀ K, IsCompact K → ν K < ⊤) ∧
      (β = 0 → ν {X | ¬ (qR (AF F) σ J (X 0) = 0 ∧ FreeT (F := F) (E := E) (Ainf F) (projInf X) ∧
        (∀ v, FreeT (F := F) (E := E) (Fv F v) (projV v (projFin X))) ∧
        ∀ᶠ v in Filter.cofinite, projV v (projFin X) 0 ∈ X0int b σ J v)} = 0) ∧
      ∀ (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
        (Φv : ∀ v, (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞),
        Measurable Φi → (∀ v, Measurable (Φv v)) →
        (∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) →
        (∀ X, Φ X = Φi (projInf X) * ∏ᶠ v, Φv v (projV v (projFin X))) →
        ∫⁻ X, Φ X ∂ν = (∫⁻ X, Φi X ∂(fi (algebraMap F (Ainf F) β))) *
          ∏' v, ∫⁻ X, Φv v X ∂(fv v (algebraMap F (Fv F v) β))

def DensityEulerProductBound : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → 3 ≤ M →
    ∀ (μi : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (νi : Measure (Ainf F))
      (μv : ∀ v, Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (Fv F v)),
      SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) → SelfDual νi (fun s t => psiInf F ψ (s * t)) →
      (∀ v, SelfDual (μv v) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))) →
      (∀ v, SelfDual (νv v) (fun s t => psiV F ψ v (s * t))) →
    ∀ (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
      IsQFibInf σ J μi νi fi → (∀ v, IsQFib σ J v (μv v) (νv v) (fv v)) →
    ∀ (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) (Φv : ∀ v, (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φi → RapidDecay b Φi → (∀ v, IsSB (Φv v)) →
      (∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) →
      (∃ C : ℝ, ∀ s : Ainf F, ‖FstarT (psiInf F ψ) σ J μi Φi s‖ ≤ C * ∏ w, (max 1 ‖s w‖) ^ (-(M : ℝ))) →
      let Fst := fun y : AF F => FstarT (psiInf F ψ) σ J μi Φi (fstA F y) *
        ∏' v, FstarT (psiV F ψ v) σ J (μv v) (Φv v) (evalV F v (sndA F y))
      let Fd := fun β : F => (∫ X, Φi X ∂(fi (algebraMap F (Ainf F) β))) *
        ∏' v, ∫ X, Φv v X ∂(fv v (algebraMap F (Fv F v) β))
      ∀ y : AF F, Summable (fun c : F => ‖Fst (algebraMap F (AF F) c + y)‖) ∧
        Summable (fun β : F => ‖Fd β‖) ∧
        ∑' c : F, Fst (algebraMap F (AF F) c + y) = ∑' β : F, Fd β * ψ (algebraMap F (AF F) β * y)

end PI.GramFibrationFormulas
