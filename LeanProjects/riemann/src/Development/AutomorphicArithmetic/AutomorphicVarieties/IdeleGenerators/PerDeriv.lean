import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep

namespace UpperTheory.V.Sd.Eis

abbrev NA (F : Type) [Field F] [NumberField F] : Type := BlockIx 2 1 → Ad F

def cterm {F : Type} [Field F] [NumberField F] [MeasurableSpace (NA F)] (μ : Measure (NA F)) (D : Set (NA F)) (φ : GA F 2 → ℂ)
    (g : GA F 2) : ℂ := ∫ x in D, φ (unip x * g) ∂μ

def Cocpt {A : Type} [AddCommGroup A] [TopologicalSpace A] (Γ : AddSubgroup A) : Prop :=
  ∃ C : Set A, IsCompact C ∧ ∀ x, ∃ γ ∈ Γ, x - γ ∈ C

def SmCont : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a), IsOpen {k | TR.finRep F a k φ = φ} → Continuous φ.1

def PerMean : Prop :=
  ∀ (A : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A) [Countable Γ], Cocpt Γ → ∀ (μ : Measure A) [μ.IsAddHaarMeasure] (D : Set A),
    IsAddFundamentalDomain Γ D μ → μ D ≠ ⊤ ∧ ∀ f : A → ℂ, (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) →
      (Continuous f → IntegrableOn f D μ) ∧ (∀ y, ∫ x in D, f (x + y) ∂μ = ∫ x in D, f x ∂μ) ∧
      ∀ e : A ≃ₜ+ A, (∀ x, e x ∈ Γ ↔ x ∈ Γ) → ∫ x in D, f (e x) ∂μ = ∫ x in D, f x ∂μ

def PerDeriv : Prop :=
  ∀ (A : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] (Γ : AddSubgroup A), Cocpt Γ → ∀ (μ : Measure A) (D : Set A), μ D ≠ ⊤ →
    ∀ f f' : A → ℝ → ℂ, Continuous (Function.uncurry f) → Continuous (Function.uncurry f') → (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) →
      (∀ γ ∈ Γ, ∀ x, f' (γ + x) = f' x) → (∀ x t, HasDerivAt (f x) (f' x t) t) →
      HasDerivAt (fun t => ∫ x in D, f x t ∂μ) (∫ x in D, f' x 0 ∂μ) 0

def BlockTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], LocallyCompactSpace (NA F) ∧ SecondCountableTopology (NA F) ∧ T2Space (NA F) ∧
    Countable (ratN F 2 1) ∧ Cocpt (ratN F 2 1) ∧ Continuous (fun x : NA F => (unip x : GA F 2)) ∧
    ∀ x : NA F, unip x = aff 1 (x ⟨(0, 1), by decide⟩)

def CtBasic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F)) [μ.IsAddHaarMeasure]
    (D : Set (NA F)), IsAddFundamentalDomain (ratN F 2 1) D μ → ∀ φ : GA F 2 → ℂ, Continuous φ → (∀ γ g, φ (ratGL F 2 γ * g) = φ g) →
    (∀ g, IntegrableOn (fun x : NA F => φ (unip x * g)) D μ) ∧ (∀ (x : Ad F) g, cterm μ D φ (aff 1 x * g) = cterm μ D φ g) ∧
    ∀ (a : Fˣ) g, cterm μ D φ (aff (diagUnits F a) 0 * g) = cterm μ D φ g

def CtLie : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F))
    [μ.IsAddHaarMeasure] (D : Set (NA F)), IsAddFundamentalDomain (ratN F 2 1) D μ → ∀ φ : TR.Sm F 2,
    (∀ γ g, φ.1 (ratGL F 2 γ * g) = φ.1 g) → IsOpen {k | TR.finRep F 2 k φ = φ} → ∀ X : TR.Lie F 2,
    ((∀ γ g, (TR.lie F 2 X φ).1 (ratGL F 2 γ * g) = (TR.lie F 2 X φ).1 g) ∧ Continuous (TR.lie F 2 X φ).1) ∧
    ∀ (c : ℝ → GL (Fin 2) (TR.Rinf F)), Continuous c → (∀ s t, c (s + t) = c s * c t) →
      HasDerivAt (fun t => TR.toL (c t).val) X 0 → ∀ g,
      HasDerivAt (fun t => cterm μ D φ.1 (g * TR.infGL F 2 (c t))) (cterm μ D (TR.lie F 2 X φ).1 g) 0

def LieAlg : Prop :=
  ∀ (h : GL (Fin 2) ℝ) (p : Fin 2 → Fin 2 → ℂ) (κ : ℂ), p 0 0 + p 1 1 = 0 → p 0 1 - p 1 0 = Complex.I * κ →
    p 0 0 - p 1 1 = Complex.I * (p 0 1 + p 1 0) →
    ∑ i, ∑ j, (((h⁻¹).val * Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℝ) * h.val) i j : ℝ) * p i j = 0 →
    ∑ i, ∑ j, (((h⁻¹).val * Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℝ) * h.val) i j : ℝ) * p i j = κ / 2

def CentLie : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F), IsOfFinOrder ω →
    ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0

def CtLeft : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F))
    [μ.IsAddHaarMeasure] (D : Set (NA F)), IsAddFundamentalDomain (ratN F 2 1) D μ → ∀ (k : ℕ) (c : Pl F → ℕ) (ω : HChar F),
    IsOfFinOrder ω → ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ),
    (∀ t v, (y t).val v = Real.exp (t * u v)) → ∀ g,
    HasDerivAt (fun t => cterm μ D φ.1 (TR.infGL F 2 (aff (y t) 0) * g)) ((k : ℂ) / 2 * ((∑ v, u v : ℝ) : ℂ) * cterm μ D φ.1 g) 0

def RayFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (H : Subgroup (Ideles F)), (∀ a : Fˣ, diagUnits F a ∈ H) →
    (∀ y : (TR.Rinf F)ˣ, (∀ v, 0 < y.val v) → TR.infId F y ∈ H) → {u : (Af F)ˣ | finId F u ∈ H} ∈ 𝓝 1 →
    IsOpen (H : Set (Ideles F)) ∧ H.FiniteIndex

def CharPick : Prop :=
  ∀ (T : Type) [CommGroup T] (U₀ : Subgroup T), U₀.FiniteIndex → ∀ f₀ : T → ℂ, f₀ ≠ 0 → (∀ t, ∀ u ∈ U₀, f₀ (t * u) = f₀ t) →
    ∃ (χ : T →* ℂˣ) (L : (T → ℂ) →ₗ[ℂ] ℂ), (∀ u ∈ U₀, χ u = 1) ∧ L f₀ ≠ 0 ∧
      ∀ (U : Subgroup T), U.FiniteIndex → ∀ f : T → ℂ, (∀ t, ∀ u ∈ U, f (t * u) = f t) → ∀ s, L (fun t => f (t * s)) = (χ s : ℂ) * L f

def AbsPow : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℝ), ∃ ν : HChar F,
    (∀ y : (TR.Rinf F)ˣ, (∀ v, 0 < y.val v) → ((ν.1 (TR.infId F y) : ℂˣ) : ℂ) = (((∏ v, y.val v) ^ s : ℝ) : ℂ)) ∧
    ∀ w, ν.UnrAt w ∧ ((ν.val w : ℂˣ) : ℂ) = (((Formalism.ConjugateSelfDual.normV w : ℝ) ^ (-s) : ℝ) : ℂ)

end UpperTheory.V.Sd.Eis
