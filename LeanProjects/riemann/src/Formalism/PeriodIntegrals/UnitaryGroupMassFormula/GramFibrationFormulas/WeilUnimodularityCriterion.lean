import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.AnisotropicOrbitSurjective

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def GeneralLinearUnimodular : Prop :=
  ∀ (K : Type) [NontriviallyNormedField K] [LocallyCompactSpace K] [SecondCountableTopology K] (M : ℕ),
    letI : MeasurableSpace (GL (Fin M) K) := borel _
    ∀ μ : Measure (GL (Fin M) K), μ.IsHaarMeasure → μ.IsMulRightInvariant

def WeilUnimodularityCriterion : Prop :=
  ∀ (L X : Type) [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L] [T2Space L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MulAction L X] [ContinuousSMul L X] (x : X),
    (∀ μ : Measure L, μ.IsHaarMeasure → μ.IsMulRightInvariant) →
    (∀ y : X, ∃ g : L, g • x = y) → IsOpenMap (fun g : L => g • x) →
    (∃ m : Measure X, m ≠ 0 ∧ (∀ K, IsCompact K → m K < ⊤) ∧ ∀ g : L, m.map (fun y => g • y) = m) →
    ∀ ν : Measure (MulAction.stabilizer L x), ν.IsHaarMeasure → ν.IsMulRightInvariant

def LocalUnitaryUnimodular : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (HA (Fv F v) σ J)), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧
    ∀ μ : Measure (HA (Ainf F) σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant

def AdelicUnitaryUnimodular : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant

def IsGramFibInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (ν : Measure (HermR (Ainf F) σ n)) (fib : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)) : Prop :=
  IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val {X | FreeT (F := F) (E := E) (Ainf F) X} ν Set.univ fib

def ArchimedeanGramFibreFamily : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → n ≤ M →
    SelfDual μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
    SelfDual ν (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S')) →
    (∃ fib, IsGramFibInf σ J μ ν fib ∧
      (∀ (S : HermR (Ainf F) σ n) (U : Set (Fin n → Fin M → Ainf F ⊗[F] E)), IsOpen U →
        (U ∩ XT (Ainf F) σ J S.1).Nonempty → 0 < fib S U) ∧
      ∀ S : HermR (Ainf F) σ n, IsUnit S.1.det → ∀ K, IsCompact K → fib S K < ⊤) ∧
    ∀ fib fib', IsGramFibInf σ J μ ν fib → IsGramFibInf σ J μ ν fib' → fib = fib'

def ArchimedeanHaarScaling : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → n ≤ M →
    SelfDual μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
    SelfDual ν (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S')) →
    ∀ fib, IsGramFibInf σ J μ ν fib →
    (∀ (g : GL (Fin n) (Ainf F ⊗[F] E)) (c c' : ℝ≥0∞),
      (∀ A, MeasurableSet A → μ ((fun X => tupMul (Ainf F) X (g⁻¹ : GL (Fin n) _).val) ⁻¹' A) = c * μ A) →
      (∀ A : Set (HermR (Ainf F) σ n), MeasurableSet A →
        ν {S | ∃ S' ∈ A, S.1 = starT (Ainf F) σ g.val * S'.1 * g.val} = c' * ν A) →
      c' ≠ 0 → c' ≠ ⊤ →
      ∀ (S S' : HermR (Ainf F) σ n), S'.1 = starT (Ainf F) σ g.val * S.1 * g.val →
        ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞, Measurable φ →
          ∫⁻ X, φ X ∂(fib S') = c / c' * ∫⁻ X, φ (tupMul (Ainf F) X g.val) ∂(fib S)) ∧
    ∀ (h : HA (Ainf F) σ J) (S : HermR (Ainf F) σ n), (fib S).map (fun X => h • X) = fib S

def RealGaussianAnyCharacter : Prop :=
  ∀ (M : ℕ) (η : Fin (2 * M) → ℝ) (α : ℝ), (∀ l, η l = 1 ∨ η l = -1) → α ≠ 0 →
    let q := fun u : Fin (2 * M) → ℝ => ∑ l, η l * u l ^ 2
    let qp := fun u : Fin (2 * M) → ℝ => ∑ l, u l ^ 2
    let B := fun u u' : Fin (2 * M) → ℝ => 2 * ∑ l, η l * u l * u' l
    let φ := fun (τ : ℂ) (u : Fin (2 * M) → ℝ) =>
      Complex.exp (2 * Real.pi * Complex.I * α * τ.re * q u - 2 * Real.pi * |α| * τ.im * qp u)
    ∀ τ : ℂ, 0 < τ.im → ∃ c : ℂ, c ≠ 0 ∧ ∀ u' : Fin (2 * M) → ℝ,
      ((2 * |α|) ^ M : ℝ) * ∫ u, φ τ u * Complex.exp (2 * Real.pi * Complex.I * α * B u u') = c * φ (-1 / τ) u'

end PI.GramFibrationFormulas
