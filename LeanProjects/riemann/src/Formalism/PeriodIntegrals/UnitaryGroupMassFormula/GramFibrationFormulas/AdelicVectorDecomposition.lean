import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.IsGoodV

open scoped TensorProduct ENNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace PI.GramFibrationFormulas

def LocalFieldInstances : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Module.finrank F E = 2 → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    (∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (Fv F v) ∧ SecondCountableTopology (Fv F v) ∧
      IsTopologicalRing (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧
      LocallyCompactSpace (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧
      BorelSpace (Fv F v ⊗[F] E)) ∧
    (IsTopologicalRing (Ainf F ⊗[F] E) ∧ T2Space (Ainf F ⊗[F] E) ∧ LocallyCompactSpace (Ainf F ⊗[F] E) ∧
      SecondCountableTopology (Ainf F ⊗[F] E) ∧ BorelSpace (Ainf F ⊗[F] E)) ∧
    (IsTopologicalRing (AF F ⊗[F] E) ∧ T2Space (AF F ⊗[F] E) ∧ LocallyCompactSpace (AF F ⊗[F] E) ∧
      SecondCountableTopology (AF F ⊗[F] E) ∧ BorelSpace (AF F ⊗[F] E)) ∧
    (IsTopologicalGroup (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) ∧ LocallyCompactSpace (HA (AF F) σ J) ∧
      SecondCountableTopology (HA (AF F) σ J) ∧ BorelSpace (HA (AF F) σ J))

def AdelicVectorDecomposition : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (d M n : ℕ) (b : Module.Basis (Fin d) F E),
    IsHomeomorph (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    (∀ X : Fin n → Fin M → Af F ⊗[F] E, ∀ᶠ v in Filter.cofinite, projV v X ∈ latV b v) ∧
    Function.Injective (fun (X : Fin n → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)) => projV v X) ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v, Set (Fin n → Fin M → Fv F v ⊗[F] E)),
      let P := {X : Fin n → Fin M → Af F ⊗[F] E |
        ∀ v, (v ∈ S → projV v X ∈ U v) ∧ (v ∉ S → projV v X ∈ latV b v)}
      ((∀ v ∈ S, IsOpen (U v)) → IsOpen P) ∧ ((∀ v ∈ S, IsCompact (U v)) → IsCompact P)

def RationalPointsLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    Countable (HFinIn (AF F) σ J) ∧ DiscreteTopology (HFinIn (AF F) σ J) ∧
    (∀ n : ℕ, DiscreteTopology (Set.range (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _)) ∧
      ∃ K : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact K ∧
        ∀ Y, ∃ X : Fin n → Fin M → E, Y - ratTup (F := F) (AF F) X ∈ K) ∧
    (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure) ∧
    ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ

def GoodPlacesCofinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
      Set.Finite {v : HeightOneSpectrum (𝓞 F) | ¬ IsGoodV b σ J v (psiV F ψ v)}

def AdelicCharacterExistence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ) ∧
    (∀ ψ ψ' : AddChar (AF F) ℂ, IsCharAF F ψ → IsCharAF F ψ' →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x)) ∧
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ y : AF F,
      (∀ a : F, ψ (algebraMap F (AF F) a * y) = 1) → ∃ c : F, y = algebraMap F (AF F) c

def SelfDualMeasuresExist : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d M : ℕ) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ,
    (∃ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), SelfDual μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y))) ∧
    (∃ ν : Measure (HermR (Ainf F) σ n), SelfDual ν (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S'))) ∧
    (∃ ν : Measure (Ainf F), SelfDual ν (fun s t => psiInf F ψ (s * t))) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∃ μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E), SelfDual μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) ∧
        (IsGoodV b σ J v (psiV F ψ v) → μ (latV b v) = 1)) ∧
      (∃ ν : Measure (HermR (Fv F v) σ n), SelfDual ν (fun S S' => psiV F ψ v (pairHerm (Fv F v) σ n S S')) ∧
        (IsGoodV b σ J v (psiV F ψ v) →
          ν {S | ∀ a c, (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈ latE b v} = 1)) ∧
      (∃ ν : Measure (Fv F v), SelfDual ν (fun s t => psiV F ψ v (s * t)) ∧
        (IsGoodV b σ J v (psiV F ψ v) → ν (v.adicCompletionIntegers F) = 1))

end PI.GramFibrationFormulas
