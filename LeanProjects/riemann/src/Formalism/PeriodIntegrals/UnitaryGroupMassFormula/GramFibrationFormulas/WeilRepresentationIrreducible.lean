import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.IsGoodV

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas
section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def B1 (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin M → Fv F v ⊗[F] E) : Fv F v :=
  Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J x y)

def rhoH {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y : Fin M → Fv F v ⊗[F] E) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) : (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => χ (B1 σ J v u y + B1 σ J v x y / 2) * φ (u + x)

def opU {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Fv F v) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) : (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => χ (b * qR (Fv F v) σ J u) * φ u

def modW {d M : ℕ} (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (a : Fv F v) : ℝ≥0∞ :=
  μ ((fun u => a • u) '' latW b v) / μ (latW b v)

def opD {d M : ℕ} (b : Module.Basis (Fin d) F E) {v : HeightOneSpectrum (𝓞 F)}
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (a : Fv F v) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) :
    (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => (((modW b μ a).toReal ^ (1 / 2 : ℝ) : ℝ) : ℂ) * φ (a • u)

def opF {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) : (Fin M → Fv F v ⊗[F] E) → ℂ :=
  fun u => ∫ s, φ s * χ (B1 σ J v s u) ∂μ

def Fstar {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (φ : (Fin M → Fv F v ⊗[F] E) → ℂ) (b : Fv F v) : ℂ :=
  ∫ x, φ x * χ (b * qR (Fv F v) σ J x) ∂μ

def l2 {V : Type} [MeasurableSpace V] (μ : Measure V) (φ : V → ℂ) : ℝ := ∫ x, ‖φ x‖ ^ 2 ∂μ

def OmV {v : HeightOneSpectrum (𝓞 F)} (χ : Fv F v → ℂ) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) (g : Matrix (Fin 2) (Fin 2) (Fv F v)) :
    Set (((Fin M → Fv F v ⊗[F] E) → ℂ) →ₗ[ℂ] ((Fin M → Fv F v ⊗[F] E) → ℂ)) :=
  {T | (∀ φ, IsSB φ → IsSB (T φ) ∧ l2 μ (T φ) = l2 μ φ) ∧
    ∀ x y φ, IsSB φ → rhoH χ σ J x y (T φ) = T (rhoH χ σ J (g 0 0 • x + g 1 0 • y) (g 0 1 • x + g 1 1 • y) φ)}

def LocDataV (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ SelfDual μ (fun x y => psiV F ψ v (B1 σ J v x y))

def WeilRepresentationIrreducible : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    ∀ T : ((Fin M → Fv F v ⊗[F] E) → ℂ) →ₗ[ℂ] ((Fin M → Fv F v ⊗[F] E) → ℂ),
      (∀ φ, IsSB φ → IsSB (T φ)) →
      (∀ x y φ, IsSB φ → T (rhoH (psiV F ψ v) σ J x y φ) = rhoH (psiV F ψ v) σ J x y (T φ)) →
      ∃ c : ℂ, ∀ φ, IsSB φ → T φ = c • φ

def WeilOperatorsPreserveSchwartz : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    ∀ φ : (Fin M → Fv F v ⊗[F] E) → ℂ, IsSB φ →
      (∀ c : Fv F v, IsSB (opU χ σ J c φ) ∧ l2 μ (opU χ σ J c φ) = l2 μ φ ∧
        ∀ x y, rhoH χ σ J x y (opU χ σ J c φ) = opU χ σ J c (rhoH χ σ J x (y + c • x) φ)) ∧
      (∀ a : Fv F v, a ≠ 0 → IsSB (opD b μ a φ) ∧ l2 μ (opD b μ a φ) = l2 μ φ ∧
        ∀ x y, rhoH χ σ J x y (opD b μ a φ) = opD b μ a (rhoH χ σ J (a • x) (a⁻¹ • y) φ)) ∧
      (IsSB (opF χ σ J μ φ) ∧ l2 μ (opF χ σ J μ φ) = l2 μ φ ∧
        ∀ x y, rhoH χ σ J x y (opF χ σ J μ φ) = opF χ σ J μ (rhoH χ σ J (-y) x φ)) ∧
      ∀ h : HA (Fv F v) σ J, let hv := fun u => (HA.mat (Fv F v) σ J h : Matrix (Fin M) (Fin M) _).mulVec u
        (∀ c, opU χ σ J c (φ ∘ hv) = opU χ σ J c φ ∘ hv) ∧ (∀ a, opD b μ a (φ ∘ hv) = opD b μ a φ ∘ hv) ∧
        opF χ σ J μ (φ ∘ hv) = opF χ σ J μ φ ∘ hv

def MetaplecticOperatorClasses : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    (∀ g : Matrix (Fin 2) (Fin 2) (Fv F v), g.det = 1 → (OmV χ σ J μ g).Nonempty) ∧
    (∀ g g' T T', T ∈ OmV χ σ J μ g → T' ∈ OmV χ σ J μ g' → T.comp T' ∈ OmV χ σ J μ (g * g')) ∧
    (∀ g T T', T ∈ OmV χ σ J μ g → T' ∈ OmV χ σ J μ g → g.det = 1 →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ φ, IsSB φ → T' φ = c • T φ) ∧
    (∀ c : Fv F v, ∃ T ∈ OmV χ σ J μ !![1, c; 0, 1], ∀ φ, IsSB φ → T φ = opU χ σ J c φ) ∧
    (∀ a : Fv F v, a ≠ 0 → ∃ T ∈ OmV χ σ J μ !![a, 0; 0, a⁻¹], ∀ φ, IsSB φ → T φ = opD b μ a φ) ∧
    ∃ T ∈ OmV χ σ J μ !![0, 1; -1, 0], ∀ φ, IsSB φ → T φ = opF χ σ J μ φ

def WeilIndexFourierFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    let r := fun β : Fv F v => (modW b μ β).toReal ^ (-(1 / 2 : ℝ))
    ∃ γ : Fv F v → ℂ, (∀ β, β ≠ 0 → ‖γ β‖ = 1) ∧
      (∀ β : Fv F v, β ≠ 0 → ∀ φ, IsSB φ →
        Fstar χ σ J μ (opF χ σ J μ φ) β = γ β * (r β : ℂ) * Fstar χ σ J μ φ (-1 / β)) ∧
      (∀ φ, IsSB φ → ∃ C : ℝ, ∀ β : Fv F v, β ≠ 0 → ‖Fstar χ σ J μ φ β‖ ≤ C * min 1 (r β)) ∧
      (IsGoodV b σ J v χ →
        (∀ β ∈ v.adicCompletionIntegers F, Fstar χ σ J μ ((latW b v).indicator 1) β = 1) ∧
        (∀ β ∉ v.adicCompletionIntegers F, ‖Fstar χ σ J μ ((latW b v).indicator 1) β‖ = r β) ∧
        ∀ β : Fv F v, Valued.v β = 1 → γ β = 1)

def MaximalCompactFiniteness : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin M → Fv F v ⊗[F] E)), LocDataV F E σ M J ψ v μ →
    let χ := psiV F ψ v
    let K := {k : Matrix (Fin 2) (Fin 2) (Fv F v) | k.det = 1 ∧ ∀ i j, k i j ∈ v.adicCompletionIntegers F}
    (∀ φ, IsSB φ → ∃ (N : ℕ) (φs : Fin N → (Fin M → Fv F v ⊗[F] E) → ℂ), (∀ j, IsSB (φs j)) ∧
      ∀ k ∈ K, ∀ T ∈ OmV χ σ J μ k, ∃ j, ∃ c : ℂ, ‖c‖ = 1 ∧ T φ = c • φs j) ∧
    (IsGoodV b σ J v χ → ∀ k ∈ K, ∀ T ∈ OmV χ σ J μ k, ∃ c : ℂ, ‖c‖ = 1 ∧
      T ((latW b v).indicator 1) = c • (latW b v).indicator 1)

end Fin

def RealGaussianWeilIndex : Prop :=
  ∀ (M : ℕ) (η : Fin (2 * M) → ℝ) (ε : ℝ), (∀ l, η l = 1 ∨ η l = -1) → (ε = 1 ∨ ε = -1) →
    let q := fun u : Fin (2 * M) → ℝ => ∑ l, η l * u l ^ 2
    let qp := fun u : Fin (2 * M) → ℝ => ∑ l, u l ^ 2
    let B := fun u u' : Fin (2 * M) → ℝ => 2 * ∑ l, η l * u l * u' l
    let φ := fun (τ : ℂ) (u : Fin (2 * M) → ℝ) =>
      Complex.exp (2 * Real.pi * Complex.I * ε * τ.re * q u - 2 * Real.pi * τ.im * qp u)
    ∀ τ : ℂ, 0 < τ.im → ∃ c : ℂ, c ≠ 0 ∧ ∀ u' : Fin (2 * M) → ℝ,
      (2 : ℂ) ^ M * ∫ u, φ τ u * Complex.exp (2 * Real.pi * Complex.I * ε * B u u') = c * φ (-1 / τ) u'

end PI.GramFibrationFormulas
