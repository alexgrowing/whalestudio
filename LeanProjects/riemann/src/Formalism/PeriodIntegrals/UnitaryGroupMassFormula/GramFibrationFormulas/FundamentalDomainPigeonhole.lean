import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.IsGoodV

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def LocData (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) : Prop :=
  IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧
  SelfDual μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) ∧
  SelfDual ν (fun S S' => psiV F ψ v (pairHerm (Fv F v) σ n S S'))

def IsGramFib {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n))
    (fib : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)) : Prop :=
  IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | FreeT (F := F) (E := E) (Fv F v) X} ν Set.univ fib

def FreeFramesOpenConull : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (M n : ℕ), n ≤ M →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure →
      IsOpen {X : Fin n → Fin M → Fv F v ⊗[F] E | FreeT (F := F) (E := E) (Fv F v) X} ∧ μ {X | ¬ FreeT (F := F) (E := E) (Fv F v) X} = 0) ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      IsOpen {X : Fin n → Fin M → Ainf F ⊗[F] E | FreeT (F := F) (E := E) (Ainf F) X} ∧ μ {X | ¬ FreeT (F := F) (E := E) (Ainf F) X} = 0

def GramMapFibreFamily : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)),
    LocData F E σ M n J ψ v μ ν → n ≤ M →
    ∃ fib, IsGramFib σ J v μ ν fib ∧
      (∀ (S : HermR (Fv F v) σ n) (U : Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsOpen U →
        (U ∩ XT (Fv F v) σ J S.1).Nonempty → 0 < fib S U) ∧
      ∀ S : HermR (Fv F v) σ n, IsUnit S.1.det →
        ∀ K, IsCompact K → fib S K < ⊤

def GramFibreFamilyUnique : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)),
    LocData F E σ M n J ψ v μ ν → n ≤ M →
    ∀ fib fib', IsGramFib σ J v μ ν fib → IsGramFib σ J v μ ν fib' → fib = fib'

def HaarScalingGramMap : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)),
    LocData F E σ M n J ψ v μ ν → n ≤ M → ∀ fib, IsGramFib σ J v μ ν fib →
    (∀ (g : GL (Fin n) (Fv F v ⊗[F] E)) (c c' : ℝ≥0∞),
      (∀ A, MeasurableSet A → μ ((fun X => tupMul (Fv F v) X (g⁻¹ : GL (Fin n) _).val) ⁻¹' A) = c * μ A) →
      (∀ A : Set (HermR (Fv F v) σ n), MeasurableSet A →
        ν {S | ∃ S' ∈ A, S.1 = starT (Fv F v) σ g.val * S'.1 * g.val} = c' * ν A) →
      c' ≠ 0 → c' ≠ ⊤ →
      ∀ (S S' : HermR (Fv F v) σ n), S'.1 = starT (Fv F v) σ g.val * S.1 * g.val →
        ∀ φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞, Measurable φ →
          ∫⁻ X, φ X ∂(fib S') = c / c' * ∫⁻ X, φ (tupMul (Fv F v) X g.val) ∂(fib S)) ∧
    ∀ (h : HA (Fv F v) σ J) (S : HermR (Fv F v) σ n), (fib S).map (fun X => h • X) = fib S

def WittTransitivityFreeFrames : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    (∀ X X' : Fin n → Fin M → E, LinearIndependent E X → LinearIndependent E X' →
      gramE σ J X = gramE σ J X' →
      ∃ g : GL (Fin M) E, g ∈ Formalism.UG.UJ (σ : E →+* E) J ∧ ∀ a, (g : Matrix (Fin M) (Fin M) E).mulVec (X a) = X' a) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (X X' : Fin n → Fin M → Fv F v ⊗[F] E), FreeT (F := F) (E := E) (Fv F v) X →
      FreeT (F := F) (E := E) (Fv F v) X' → gramR (Fv F v) σ J X = gramR (Fv F v) σ J X' →
      ∃ h : HA (Fv F v) σ J, h • X = X'

def GoodPlaceOrthonormalLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), IsGoodV b σ J v (psiV F ψ v) →
    (∃ e : Fin M → Fin M → Fv F v ⊗[F] E, (∀ i, e i ∈ latW b v) ∧
      (∀ i j, hR (Fv F v) σ J (e i) (e j) = if i = j then 1 else 0) ∧
      ∀ y ∈ latW (M := M) b v, ∃ c : Fin M → Fv F v ⊗[F] E, (∀ i, c i ∈ latE b v) ∧ y = ∑ i, c i • e i) ∧
    (∀ x ∈ latW (M := M) b v, (Valued.v (qR (Fv F v) σ J x)) = 1 →
      ∃ y ∈ latW (M := M) b v, hR (Fv F v) σ J x y = 1) ∧
    ∀ β : Fv F v, (Valued.v β = 1 ∨ β = 0) →
      ∀ x ∈ latW (M := M) b v, ∀ x' ∈ latW (M := M) b v,
        (∃ y ∈ latW (M := M) b v, hR (Fv F v) σ J x y = 1) → (∃ y ∈ latW (M := M) b v, hR (Fv F v) σ J x' y = 1) →
        qR (Fv F v) σ J x = β → qR (Fv F v) σ J x' = β →
        ∃ h : HA (Fv F v) σ J, (∀ y, y ∈ latW (M := M) b v ↔ (HA.mat (Fv F v) σ J h : Matrix (Fin M) (Fin M) _).mulVec y ∈ latW b v) ∧
          (HA.mat (Fv F v) σ J h : Matrix (Fin M) (Fin M) _).mulVec x = x'

def FundamentalDomainPigeonhole : Prop :=
  ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    (Λ : AddSubgroup G) [Countable Λ] (D : Set G), IsAddFundamentalDomain Λ D μ → μ D = 1 →
    ∀ Ω₀ : Set G, MeasurableSet Ω₀ → 1 < μ Ω₀ → ∃ l ∈ Λ, l ≠ 0 ∧ ∃ x ∈ Ω₀, ∃ y ∈ Ω₀, l = x - y

end PI.GramFibrationFormulas
