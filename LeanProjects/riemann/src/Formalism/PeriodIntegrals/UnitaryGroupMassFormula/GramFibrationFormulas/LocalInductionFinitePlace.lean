import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.WeilUnimodularityCriterion
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.GlobalDensityProductFormula

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def IsotropicLatticeCount : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    3 ≤ M → ∀ L' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E),
    (∀ v, IsCompact (L' v) ∧ IsOpen (L' v) ∧ 0 ∈ L' v ∧ (∀ x ∈ L' v, ∀ y ∈ L' v, x + y ∈ L' v) ∧
      ∀ x ∈ L' v, -x ∈ L' v) →
    (∀ᶠ v in Filter.cofinite, L' v = latV b v) →
    ∀ (μ : Measure (HA (AF F) σ J)) 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
      let N := fun R : ℝ => ∫⁻ h in 𝓕, ∑' x : (Fin 1 → Fin M → E),
        {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧
          (∀ v, projV v (projFin (h⁻¹ • ratTup (F := F) (AF F) x)) ∈ L' v) ∧
          sizeTup b (projInf (h⁻¹ • ratTup (F := F) (AF F) x)) ≤ R}.indicator 1 x ∂μ
      let dF := Module.finrank ℚ F
      (∀ R, N R < ⊤) ∧
      (∀ r R : ℝ, 0 < r → r ≤ R → N R ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * M * dF)) * (μ 𝓕 + N r)) ∧
      ∃ r₀ C : ℝ, 0 < r₀ ∧ ∀ R : ℝ, 0 < R → R ≤ r₀ → N R ≤ ENNReal.ofReal (C * R ^ ((2 * M - 2) * dF))

def HermitianDilationFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ β : F, β ≠ 0 →
    ∀ ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E), Formalism.MainNotions.StandardLattice.IsDxDq F E σ M J ψ β ν →
    ∀ (μ : Measure (HA (AF F) σ J)) 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
    ∀ Ψ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Ψ →
      meanL μ 𝓕 (fun h => ∑' x : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β},
        Ψ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))) = ∫⁻ y, Ψ y ∂ν

def HermitianDiagonalization : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ a c, σ (T c a) = T a c) → T.det ≠ 0 →
    ∃ (g : GL (Fin n) E) (t : Fin n → F), (∀ i, t i ≠ 0) ∧
      ((g : Matrix (Fin n) (Fin n) E).map σ).transpose * T * (g : Matrix (Fin n) (Fin n) E) =
        Matrix.diagonal (fun i => algebraMap F E (t i))

def LocalInductionFinitePlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M M' n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)),
    IsCMExt F E σ → IsHermND σ J → IsCharAF F ψ → M' + 1 = M → n + 1 ≤ M →
    ∀ (x₀ : Fin M → E) (t₁ : F) (P₀ : Matrix (Fin M) (Fin M') E), t₁ ≠ 0 →
      hE σ J x₀ x₀ = algebraMap F E t₁ → (∀ j, hE σ J x₀ (fun i => P₀ i j) = 0) →
      LinearIndependent E (fun j i => P₀ i j) →
    let J' := (P₀.map σ).transpose * J * P₀
    let P₀v := P₀.map (inclR (F := F) (Fv F v))
    ∀ (μ : Measure (Fin (n + 1) → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (n + 1)))
      (μ' : Measure (Fin n → Fin M' → Fv F v ⊗[F] E)) (ν' : Measure (HermR (Fv F v) σ n))
      (μ₁ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν₁ : Measure (Fv F v)),
      LocData F E σ M (n + 1) J ψ v μ ν → LocData F E σ M' n J' ψ v μ' ν' →
      SelfDual μ₁ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) → SelfDual ν₁ (fun s t => psiV F ψ v (s * t)) →
    ∀ fib fib' fq, IsGramFib σ J v μ ν fib → IsGramFib σ J' v μ' ν' fib' → IsQFib σ J v μ₁ ν₁ fq →
    ∀ s : (Fin 1 → Fin M → Fv F v ⊗[F] E) → HA (Fv F v) σ J, Measurable s →
      (∀ x, qR (Fv F v) σ J (x 0) = algebraMap F (Fv F v) t₁ →
        s x • (fun _ i => inclR (F := F) (Fv F v) (x₀ i)) = x) →
    ∀ (T : HermR (Fv F v) σ (n + 1)) (T' : HermR (Fv F v) σ n),
      (∀ a b : Fin n, T.1 a.succ b.succ = T'.1 a b) → T.1 0 0 = inclR (F := F) (Fv F v) (algebraMap F E t₁) →
      (∀ a : Fin n, T.1 0 a.succ = 0) →
    ∀ φ : (Fin (n + 1) → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞, Measurable φ →
      ∫⁻ X, φ X ∂(fib T) = (modF ν₁ (algebraMap F (Fv F v) t₁))⁻¹ ^ n *
        ∫⁻ x, ∫⁻ Y, φ (Fin.cons (x 0) (fun a =>
          (HA.mat (Fv F v) σ J (s x) : Matrix (Fin M) (Fin M) _).mulVec (P₀v.mulVec (Y a)))) ∂(fib' T') ∂(fq (algebraMap F (Fv F v) t₁))

def IsPureL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (Φv : ∀ v, (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞) : Prop :=
  Measurable Φi ∧ (∀ v, Measurable (Φv v)) ∧ (∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) ∧
    ∀ X, Φ X = Φi (projInf X) * ∏ᶠ v, Φv v (projV v (projFin X))

def SiegelWeilPureFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M n : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), T.det ≠ 0 →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∀ (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (νi : Measure (HermR (Ainf F) σ n))
      (μv : ∀ v, Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (HermR (Fv F v) σ n)),
      SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
      SelfDual νi (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S')) →
      (∀ v, LocData F E σ M n J ψ v (μv v) (νv v)) →
    ∀ (fi : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (fv : ∀ v, HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibInf σ J μi νi fi → (∀ v, IsGramFib σ J v (μv v) (νv v) (fv v)) →
    ∀ (μ : Measure (HA (AF F) σ J)) 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ →
    ∀ Φ Φi Φv, IsPureL b Φ Φi Φv →
      meanL μ 𝓕 (fun h => ∑' X : {X : Fin n → Fin M → E | gramE σ J X = T},
        Φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin n → Fin M → E))) =
        (∫⁻ X, Φi X ∂(fi (hermOf (Ainf F) σ T hT))) * ∏' v, ∫⁻ X, Φv v X ∂(fv v (hermOf (Fv F v) σ T hT))

def SchwartzBruhatConvergence : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M n : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    n ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), T.det ≠ 0 →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
    ∀ (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (νi : Measure (HermR (Ainf F) σ n))
      (μv : ∀ v, Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : ∀ v, Measure (HermR (Fv F v) σ n)),
      SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y)) →
      SelfDual νi (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S')) →
      (∀ v, LocData F E σ M n J ψ v (μv v) (νv v)) →
    ∀ (fi : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (fv : ∀ v, HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibInf σ J μi νi fi → (∀ v, IsGramFib σ J v (μv v) (νv v) (fv v)) →
    ∀ (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φv : ∀ v, (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φi → RapidDecay b Φi → (∀ v, IsSB (Φv v)) →
      (∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) →
      IsContDensityOn μi (gramR (Ainf F) σ J) Subtype.val νi
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φi (fun S => ∫ X, Φi X ∂(fi S)) ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (fun S => ∫ X, Φv v X ∂(fv v S))) ∧
      ∫⁻ X, ‖Φi X‖ₑ ∂(fi (hermOf (Ainf F) σ T hT)) < ⊤ ∧
      (∀ v, ∫⁻ X, ‖Φv v X‖ₑ ∂(fv v (hermOf (Fv F v) σ T hT)) < ⊤) ∧
      ∏' v, ∫⁻ X, ‖Φv v X‖ₑ ∂(fv v (hermOf (Fv F v) σ T hT)) < ⊤ ∧
      Multipliable (fun v => ∫ X, Φv v X ∂(fv v (hermOf (Fv F v) σ T hT)))

end PI.GramFibrationFormulas
