import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Defs

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

def Near (r : ValueGroupWithZero E) (s : Fin n → Eˣ) : Prop := ∀ i, valuation E ((s i : E) - 1) ≤ r

def elemSet (r : ValueGroupWithZero E) (A : Set (Fin n → Eˣ)) : Set (GL (Fin n) E) :=
  {g | ∃ a ∈ ball n r, ∃ b ∈ ball n r, ∃ s ∈ A, g = a * diagT E (Fin n) s * b}

def sgT (σ : E ≃+* E) (u : Fin n → Eˣ) : Fin n → Eˣ := fun i => Units.map (σ : E →* E) (u i)

def Rel (σ : E ≃+* E) (r : ValueGroupWithZero E) (u ρ : Fin n → Eˣ) : Prop := ∃ p s, sgT σ p = p ∧ Near r s ∧ u = ρ * p * s

variable (k : Type) [Field k] [Algebra k E]

def nrmT (t : Fin n → Eˣ) : Fin n → kˣ := fun i => Units.map (Algebra.norm k : E →* k) (t i)

def nrmSet (r : ValueGroupWithZero E) (t : Fin n → Eˣ) : Set (Fin n → kˣ) := {x | ∃ u, Near r u ∧ x = nrmT k (t * u)}

end Defs

def SuppE : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q →
    ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∀ A : Set (Fin n → Eˣ), (∀ t ∈ A, Strict t) →
    (∀ δ g : GL (Fin n) E, g⁻¹ * δ * sg σ g ∈ elemSet r A → ∃ y, ∃ t ∈ A, ∃ s, Near r s ∧ Strict (t * s) ∧
      y⁻¹ * δ * sg σ y = diagT E (Fin n) (t * s)) ∧
    ∀ (δ y : GL (Fin n) E) (d : Fin n → Eˣ), Strict d → y⁻¹ * δ * sg σ y = diagT E (Fin n) d → ∀ g,
      g⁻¹ * δ * sg σ g ∈ elemSet r A ↔ ∃ u, (∃ t ∈ A, Near r (d * sgT σ u / u / t)) ∧ ∃ κ ∈ ball n r, g = y * diagT E (Fin n) u * κ

def CosetSum : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K H : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
    IsClosed (H : Set G) → (∀ a ∈ H, ∀ b ∈ H, Commute a b) → ∀ ν : Measure H, ν.IsHaarMeasure →
    ∀ (ι : Type) (R : Finset ι) (x : ι → G) (V : Set H) (S : Set G), (∀ i ∈ R, ∀ h : H, h ∈ V ↔ (x i)⁻¹ * h * x i ∈ K) →
      (∀ g, g ∈ S ↔ ∃ i ∈ R, ∃ h ∈ H, ∃ κ ∈ K, g = h * x i * κ) →
      (∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ κ ∈ K, x i = h * x j * κ) → i = j) →
      quotIntegral μ H ν (S.indicator 1) = (((R.card : ℝ) * μ.real K / ν.real V : ℝ) : ℂ)

def OneField : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q →
    ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μ : Measure (GL (Fin n) E)), μ.IsHaarMeasure →
    ∀ A : Set (Fin n → Eˣ), (∀ t ∈ A, Strict t) → ∀ (δ y : GL (Fin n) E) (d : Fin n → Eˣ), Strict d →
      y⁻¹ * δ * sg σ y = diagT E (Fin n) d → ∀ H : Subgroup (GL (Fin n) E), (∀ c, c ∈ H ↔ c⁻¹ * δ * sg σ c = δ) →
    ∀ ν : Measure H, ν.IsHaarMeasure → ∀ R : Finset (Fin n → Eˣ),
      (∀ u, (∃ t ∈ A, Near r (d * sgT σ u / u / t)) ↔ ∃ ρ ∈ R, Rel σ r u ρ) → (∀ ρ ∈ R, ∀ ρ' ∈ R, Rel σ r ρ ρ' → ρ = ρ') →
      quotIntegral μ H ν (fun g => (elemSet r A).indicator 1 (g⁻¹ * δ * sg σ g)) =
        (((R.card : ℝ) * μ.real (ball n r) / ν.real {h : H | y⁻¹ * h * y ∈ ball n r} : ℝ) : ℂ)

def Reps : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q →
    ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∃ R : Finset (Fin n → Eˣ), R.Nonempty ∧ (∀ u, Near r (sgT σ u / u) ↔ ∃ ρ ∈ R, Rel σ r u ρ) ∧
      (∀ ρ ∈ R, ∀ ρ' ∈ R, Rel σ r ρ ρ' → ρ = ρ') ∧ (∀ a b : Fin n → Eˣ, Near r a → Near r b → Near r (a * b) ∧ Near r a⁻¹) ∧
      ∀ z u ρ : Fin n → Eˣ, Rel σ r (z * u) (z * ρ) ↔ Rel σ r u ρ

def NormOpen : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∃ r₀ : ValueGroupWithZero k, 0 < r₀ ∧ r₀ < 1 ∧
      ∀ x : kˣ, valuation k ((x : k) - 1) ≤ r₀ → valuation E (algebraMap k E x - 1) ≤ r ∧
        ∃ u : Eˣ, valuation E ((u : E) - 1) ≤ r ∧ (x : k) = Algebra.norm k (u : E)

def NormDiag : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, (∀ d : Fin n → Eˣ, normGL σ (diagT E (Fin n) d) = incl (diagT k (Fin n) (nrmT k d)) ∧ (Strict d → Strict (nrmT k d)) ∧
        (Strict d → IsRegSemisimple (diagT k (Fin n) (nrmT k d)))) ∧
      (∀ (r : ValueGroupWithZero E) (d t : Fin n → Eˣ),
        (∃ u, Near r (d * sgT (σ : E ≃+* E) u / u / t)) ↔ nrmT k d ∈ nrmSet k r t) ∧
      ∀ r : ValueGroupWithZero E, r < 1 → ∀ t : Fin n → Eˣ, Strict t → (∀ x ∈ nrmSet k r t, Strict x) ∧ IsCompact (nrmSet k r t)

def Align : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (δ h y : GL (Fin n) E) (γ : GL (Fin n) k) (d : Fin n → Eˣ), Strict d → normGL σ δ = h * incl γ * h⁻¹ →
      y⁻¹ * δ * sigmaGL σ y = diagT E (Fin n) d → ∃ y' : GL (Fin n) k, y'⁻¹ * γ * y' = diagT k (Fin n) (nrmT k d) ∧
        ∀ t ∈ Subgroup.centralizer {γ}, y⁻¹ * (h * incl t * h⁻¹) * y = incl (y'⁻¹ * t * y')

def VolRatio : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (r : ValueGroupWithZero E) (r' : ValueGroupWithZero k),
      0 < r → r < 1 → 0 < r' → r' < 1 → (∀ x : kˣ, valuation k ((x : k) - 1) ≤ r' → valuation E (algebraMap k E x - 1) ≤ r) →
      ∃ j : ℝ, 0 < j ∧ ∀ (γ y : GL (Fin n) k) (x : Fin n → kˣ), Strict x → y⁻¹ * γ * y = diagT k (Fin n) x →
        ∀ ν : Measure (Subgroup.centralizer {γ}), ν.IsHaarMeasure →
          ν.real {t | (incl (y⁻¹ * (t : GL (Fin n) k) * y) : GL (Fin n) E) ∈ ball n r} =
            j * ν.real {t | y⁻¹ * (t : GL (Fin n) k) * y ∈ ball n r'}

def ElemTest : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (r : ValueGroupWithZero E),
    0 < r → r < 1 → ∀ A : Set (Fin n → Eˣ), IsCompact A → IsOpen (elemSet r A) ∧ IsCompact (elemSet r A) ∧
      UpperTheory.ConvolutionTheory.C.Test ((elemSet r A).indicator (1 : GL (Fin n) E → ℂ)) ∧
      (elemSet r A).indicator (1 : GL (Fin n) E → ℂ) ∈ SB (GL (Fin n) E) ∧
      ∀ g ∈ elemSet r A, ∃ t ∈ A, ∃ x : Eˣ, valuation E ((x : E) - 1) ≤ r ∧ GeneralLinearGroup.det g = (∏ i, t i) * x

def ElemLoc : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure →
    ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∃ r₀ : ValueGroupWithZero k, 0 < r₀ ∧ r₀ < 1 ∧ ∀ r' ≤ r₀, 0 < r' →
      (∀ x : kˣ, valuation k ((x : k) - 1) ≤ r' → ∃ u : Eˣ, valuation E ((u : E) - 1) ≤ r ∧ (x : k) = Algebra.norm k (u : E)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t : Fin n → Eˣ, Strict t →
        Match σ μE μk ((elemSet r {t}).indicator 1) ((c : ℂ) • (elemSet r' (nrmSet k r t)).indicator 1)

def NormLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime →
    ∀ (v : UpperTheory.ConvolutionTheory.Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)] [ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E)]
      [FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E)] [IsGalois (v.adicCompletion F) (w.1.adicCompletion E)],
      (∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x) →
      ∀ η : Formalism.L2.Host.HChar F, IsNormChar E η → ∀ u : (w.1.adicCompletion E)ˣ,
        η.loc v (Units.map (Algebra.norm (v.adicCompletion F) : w.1.adicCompletion E →* v.adicCompletion F) u) = 1

def MatchSmul : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (v : UpperTheory.ConvolutionTheory.Pl F) (c : ℂ),
    c ≠ 0 → ∀ (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ),
      UpperTheory.ConvolutionTheory.GM.MatchAt σ v 1 φ (c • f) → UpperTheory.ConvolutionTheory.GM.MatchAt σ v c φ f

def ElemPair : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime →
    ∀ (v : UpperTheory.ConvolutionTheory.Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)] [ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E)]
      [FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E)] [IsGalois (v.adicCompletion F) (w.1.adicCompletion E)],
      (∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x) →
    ∀ (n : ℕ) (r : ValueGroupWithZero (w.1.adicCompletion E)), 0 < r → r < 1 →
      ∃ r₀ : ValueGroupWithZero (v.adicCompletion F), 0 < r₀ ∧ r₀ < 1 ∧ ∀ r' ≤ r₀, 0 < r' →
      (∀ x : (v.adicCompletion F)ˣ, valuation _ ((x : v.adicCompletion F) - 1) ≤ r' → ∃ u : (w.1.adicCompletion E)ˣ,
        valuation _ ((u : w.1.adicCompletion E) - 1) ≤ r ∧ (x : v.adicCompletion F) = Algebra.norm _ (u : w.1.adicCompletion E)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t : Fin n → (w.1.adicCompletion E)ˣ, Strict t →
        UpperTheory.ConvolutionTheory.C.Test ((elemSet r {t}).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ)) ∧
        UpperTheory.ConvolutionTheory.C.Test ((elemSet r' (nrmSet (v.adicCompletion F) r t)).indicator (1 : GL (Fin n) (v.adicCompletion F) → ℂ)) ∧
        UpperTheory.ConvolutionTheory.GM.MatchAt σ v c (fun g => (elemSet r {t}).indicator 1 (UpperTheory.ConvolutionTheory.GM.cmp w g))
          ((elemSet r' (nrmSet (v.adicCompletion F) r t)).indicator 1) ∧
        ∀ g ∈ elemSet r' (nrmSet (v.adicCompletion F) r t), g ∈ G.normSet E n v

end UpperTheory.Gal.InertialTypesAlt.L
