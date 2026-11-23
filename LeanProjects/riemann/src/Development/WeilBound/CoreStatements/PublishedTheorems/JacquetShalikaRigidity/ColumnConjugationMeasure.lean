import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

def ForG (P : ∀ (G : Type) [Group G] [MeasurableSpace G], Measure G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure], P G μ

def ForMu (P : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ), Measure (GA E k) → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ) (μ : Measure (GA E k)) [μ.IsHaarMeasure], P E k μ

def Q1 : Prop := ForG fun G _ _ μ => ∀ (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G) (β β₁ : G → ℝ≥0∞),
  Measure.map (fun h => h⁻¹) ν = ν → (∀ᵐ h ∂ν, h ∈ H) → IsWt ν β → Measurable β₁ →
    (∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1) → ∀ Φ : G → ℝ≥0∞, Measurable Φ → (∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) →
      ∫⁻ g, Φ g ∂μ.withDensity β = ∫⁻ g, ∫⁻ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁

def Q2 : Prop := ForG fun G _ _ μ => ∀ (ν ρ : Measure G) [SFinite ν] [SFinite ρ] (H : Set G) (β β₁ : G → ℝ≥0∞),
  Measure.map (fun h => h⁻¹) ν = ν → (∀ᵐ h ∂ν, h ∈ H) → IsWt ν β → Measurable β₁ →
    (∀ g, ∫⁻ r, ∫⁻ h, β₁ (r⁻¹ * h * g) ∂ν ∂ρ = 1) → ∀ Φ : G → ℂ, Measurable Φ → (∀ h ∈ H, ∀ g, Φ (h * g) = Φ g) →
      Integrable Φ (μ.withDensity β) → Integrable (fun g => ∫ r, Φ (r * g) ∂ρ) (μ.withDensity β₁) ∧
        ∫ g, Φ g ∂μ.withDensity β = ∫ g, ∫ r, Φ (r * g) ∂ρ ∂μ.withDensity β₁

def D0 : Prop := ForE fun E _ _ _ k =>
  (∀ g : GA E k, 0 < Dt g) ∧ (∀ g h : GA E k, Dt (g * h) = Dt g * Dt h) ∧ Continuous (Dt : GA E k → ℝ) ∧
  (∀ γ, Dt (ratGL E k γ) = 1) ∧ (∀ j (u : GA E k), UU j u → Dt u = 1) ∧ (∀ g : GA E k, Dt (invT g) = (Dt g)⁻¹) ∧
  (∀ t, Dt (splitCentre E k t) = Real.exp (k * Module.finrank ℚ E * t)) ∧
  (∀ t (g : GA E k), splitCentre E k t * g = g * splitCentre E k t) ∧
  (∀ s t, splitCentre E k (s + t) = splitCentre E k s * splitCentre E k t) ∧
  (∀ (w : Pl E) (l : Fin k → ℤ), Dt (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l)) =
    (Ideal.absNorm w.asIdeal : ℝ) ^ (-∑ i, l i)) ∧
  ∀ κ : GA E k, cInf κ = 1 → (∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) → Dt κ = 1

def AdelicLinearChange : Prop := ForE fun E _ _ _ k => ∀ (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞), Measurable F →
  ∫⁻ x, F (g.val *ᵥ x) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) ∧
  ∫⁻ x, F (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k)

def ColumnConjugationMeasure : Prop := ForE fun E _ _ _ k => ∀ j < k, ∀ g : GA E k, GlobalTheory j g → ∀ F : GA E k → ℝ≥0∞, Measurable F →
  ∫⁻ x : UnipotentBlockColumnIndex k j j → Ad E, F (g * blkU x * g⁻¹) ∂vecMeasure E _ =
    ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x : UnipotentBlockColumnIndex k j j → Ad E, F (blkU x) ∂vecMeasure E _

def N0 : Prop := ForE fun E _ _ _ k => ∀ j, 1 ≤ j → j ≤ k →
  (∀ ξ : RowT E k j, GlobalTheory j (gam ξ) ∧ ∀ i c : Fin k, (i : ℕ) + 1 = j → (gam ξ).val i c = ξ.1 c) ∧
  (∀ γ : GL (Fin k) E, GlobalTheory j γ → ∃! p : RowT E k j × GL (Fin k) E, IsMir (j - 1) p.2 ∧ γ = p.2 * gam p.1) ∧
  (∀ γ γ' : GL (Fin k) E, GlobalTheory j γ → GlobalTheory j γ' → GlobalTheory j (γ * γ')) ∧ (∀ γ : GL (Fin k) E, GlobalTheory j γ → GlobalTheory j γ⁻¹) ∧
  (∀ γ γ' : GL (Fin k) E, IsMir (j - 1) γ → IsMir (j - 1) γ' → IsMir (j - 1) (γ * γ')) ∧
  (∀ γ : GL (Fin k) E, IsMir (j - 1) γ → IsMir (j - 1) γ⁻¹ ∧ GlobalTheory j γ) ∧ Countable (RowT E k j) ∧
  (∀ γ : GL (Fin k) E, GlobalTheory k γ) ∧
  (∀ γ : GL (Fin k) E, ∃ e : RowT E k k ≃ RowT E k k, ∀ ξ, ∃ p, IsMir (k - 1) p ∧ gam ξ * γ = p * gam (e ξ)) ∧
  ∀ (ξ : RowT E k k) (g : GA E k), lastRow (ratGL E k (gam ξ) * g) = (fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val

def N1 : Prop := ForE fun E _ _ _ k => ∀ d ≤ k, SFinite (nuD E k d) ∧ (∀ᵐ u ∂nuD E k d, UU (k - d) u) ∧
  Measure.map (fun h => h⁻¹) (nuD E k d) = nuD E k d ∧
  (∀ u : GA E k, UU (k - d) u → Measure.map (fun h => u * h) (nuD E k d) = nuD E k d) ∧
  ∀ g : GA E k, GlobalTheory (k - d) g → ∀ F : GA E k → ℝ≥0∞, Measurable F →
    ∫⁻ h, F (g * h * g⁻¹) ∂nuD E k d = ENNReal.ofReal (Dt g)⁻¹ ^ d * ∫⁻ h, F h ∂nuD E k d

def N2 : Prop := ForE fun E _ _ _ k => ∀ (w : Pl E) (l : Fin k → ℤ) (F : GA E k → ℝ≥0∞), Measurable F →
  ∫⁻ h, F (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l) * h * (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l))⁻¹)
      ∂nuP E k 0 = ENNReal.ofReal ((Ideal.absNorm w.asIdeal : ℝ) ^ rhoPair l) * ∫⁻ h, F h ∂nuP E k 0

def N3 : Prop := ForE fun E _ _ _ k =>
  (∀ m < k, SFinite (nuP E k m) ∧ Measure.map (fun h => h⁻¹) (nuP E k m) = nuP E k m ∧
    ∀ᵐ h ∂nuP E k m, ∃ γ u, IsMir m γ ∧ UU (m + 1) u ∧ h = ratGL E k γ * u) ∧
  (∀ j ≤ k, SFinite (nuB E k j) ∧ Measure.map (fun h => h⁻¹) (nuB E k j) = nuB E k j ∧
    ∀ᵐ h ∂nuB E k j, ∃ γ u, GlobalTheory j γ ∧ UU j u ∧ h = ratGL E k γ * u) ∧
  (∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F h ∂nuB E k k = ∑' γ : GL (Fin k) E, F (ratGL E k γ)) ∧
  (1 ≤ k → (∀ᵐ h ∂nuP E k 0, UU 0 h) ∧ nuP E k 0 ≠ 0)

def CosetIntegralParabolic : Prop := ForE fun E _ _ _ k => ∀ j, 1 ≤ j → j ≤ k → ∀ F : GA E k → ℝ≥0∞, Measurable F →
  ∫⁻ h, F h ∂nuB E k j = ∑' ξ : RowT E k j, ∫⁻ h, F ((ratGL E k (gam ξ))⁻¹ * h) ∂nuP E k (j - 1)

def OneMoreAdelicColumn : Prop := ForE fun E _ _ _ k => ∀ m < k, ∀ F : GA E k → ℝ≥0∞, Measurable F →
  ∫⁻ h, F h ∂nuB E k m =
    ∫⁻ x in vecDomain E (UnipotentBlockColumnIndex k m m), ∫⁻ h, F ((blkU x)⁻¹ * h) ∂nuP E k m ∂vecMeasure E (UnipotentBlockColumnIndex k m m)

def W0 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → (∃ β, IsWt (nuB E k k) β) ∧
  ∀ β, IsWt (nuB E k k) β → μ.withDensity β (band E k) < ∞

def V1 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuB E k k) β →
  (∀ (t : ℝ) (Φ : GA E k → ℝ≥0∞), Measurable Φ → RatInv Φ →
    ∫⁻ g, Φ (splitCentre E k t * g) ∂μ.withDensity β = ∫⁻ g, Φ g ∂μ.withDensity β) ∧
  (∀ (t : ℝ) (Φ : GA E k → ℂ), Measurable Φ → RatInv Φ → Integrable Φ (μ.withDensity β) →
    ∫ g, Φ (splitCentre E k t * g) ∂μ.withDensity β = ∫ g, Φ g ∂μ.withDensity β) ∧
  ∀ ε : ℝ, 0 < ε → Integrable (fun g => min (Dt g) (Dt g)⁻¹ ^ ε) (μ.withDensity β)

def P0 : Prop := ∀ (E : Type) [Field E] [NumberField E] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (ι : Type) [Fintype ι],
  (∀ f : (ι → Ad E) → ℂ, Per (ratV E ι) f → avg (ratV E ι) f = ∫ x in vecDomain E ι, f x ∂vecMeasure E ι) ∧
  (∀ f g : (ι → Ad E) → ℂ, Per (ratV E ι) f → Per (ratV E ι) g →
    HasSum (fun ξ : ι → E => avg (ratV E ι) (fun x => ψ (-dot ξ x) * f x) * conj (avg (ratV E ι) fun x => ψ (-dot ξ x) * g x))
      (avg (ratV E ι) fun x => f x * conj (g x))) ∧
  ∀ f : (ι → Ad E) → ℂ, Per (ratV E ι) f → {ξ : ι → E | avg (ratV E ι) (fun x => ψ (-dot ξ x) * f x) ≠ 0}.Finite →
    HasSum (fun ξ : ι → E => avg (ratV E ι) fun x => ψ (-dot ξ x) * f x) (f 0)

def P1 : Prop := ForE fun E _ _ _ k => ∀ ψ, StdPsi ψ → ∀ m, 1 ≤ m → m < k → ∀ f : GA E k → ℂ, Pre ψ m f →
  Pre ψ (m - 1) (colT ψ m f) ∧ (∀ (ξ : RowT E k m) g, coefF ψ m (fun t => ξ.1 t.1.1) f g = colT ψ m f (ratGL E k (gam ξ) * g)) ∧
  (∀ χ : GA E k → ℂ, (∀ (x : UnipotentBlockColumnIndex k m m → Ad E) g, χ (blkU x * g) = χ g) →
    colT ψ m (fun g => χ g * f g) = fun g => χ g * colT ψ m f g) ∧
  ∃ e : RowT E k m ≃ {ξ : UnipotentBlockColumnIndex k m m → E // ξ ≠ 0}, ∀ ξ t, (e ξ).1 t = ξ.1 t.1.1

def P2 : Prop := ForE fun E _ _ _ k => ∀ ψ, StdPsi ψ →
  (∀ m (f : GA E k → ℂ), Pre ψ m f → ∀ u, UU (m + 1) u → ∀ g, f (u * g) = psN ψ u * f g) ∧
  (∀ u : GA E k, ‖psN ψ u‖ = 1) ∧ (∀ u : GA E k, UU 0 u → UU 1 u) ∧
  (∀ m, m < k → ∀ f : GA E k → ℂ, Pre ψ m f → Pre ψ 0 (whit ψ m f)) ∧
  (∀ m, m < k → ∀ f χ : GA E k → ℂ, Pre ψ m f → Continuous χ → (∀ u, UU 0 u → ∀ g, χ (u * g) = χ g) →
    (∀ γ, IsMir m γ → ∀ g, χ (ratGL E k γ * g) = χ g) →
    Pre ψ m (fun g => χ g * f g) ∧ (whit ψ m (fun g => χ g * f g) = fun g => χ g * whit ψ m f g) ∧
      (Good ψ m f → Good ψ m fun g => χ g * f g)) ∧
  (∀ m (f : GA E k → ℂ), Good ψ m f → Pre ψ m f) ∧
  (∀ (u g : GA E k), UU 0 u → lastRow (u * g) = lastRow g) ∧
  (∀ γ (g : GA E k), IsMir (k - 1) γ → lastRow (ratGL E k γ * g) = lastRow g) ∧ Continuous (lastRow : GA E k → _) ∧
  ∀ m, m < k → ∀ (f : GA E k → ℂ) (C : Set (Fin k → Ad E)), (∀ g, f g ≠ 0 → lastRow g ∈ C) →
    ∀ g, whit ψ m f g ≠ 0 → lastRow g ∈ C

def P3 : Prop := ForE fun E _ _ _ k => ∀ (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f f' : GA E k → ℂ) (g g' : GA E k) (c : ℂ),
  (∀ u, UU 0 u → f (u * g) = c * f' (u * g')) → whit ψ m f g = c * whit ψ m f' g'

def U1 : Prop := ForMu fun E _ _ _ k μ => ∀ ψ, StdPsi ψ → ∀ m, 1 ≤ m → m < k → ∀ β, IsWt (nuP E k m) β →
  ∃ β', IsWt (nuP E k (m - 1)) β' ∧
    (∀ f, Pre ψ m f → ∫⁻ g, ‖colT ψ m f g‖ₑ ^ 2 ∂μ.withDensity β' ≤ ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β) ∧
    ∀ f φ, Pre ψ m f → Good ψ m φ → ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β < ∞ → ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
      ∫ g, f g * conj (φ g) ∂μ.withDensity β = ∫ g, colT ψ m f g * conj (colT ψ m φ g) ∂μ.withDensity β'

def U2 : Prop := ForMu fun E _ _ _ k μ => ∀ ψ, StdPsi ψ → ∀ m, m < k → ∀ β, IsWt (nuP E k m) β →
  ∃ β', IsWt (nuP E k 0) β' ∧
    ∀ f φ, Pre ψ m f → Good ψ m φ → ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β < ∞ → ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
      Integrable (fun g => whit ψ m f g * conj (whit ψ m φ g)) (μ.withDensity β') ∧
      ∫ g, f g * conj (φ g) ∂μ.withDensity β = ∫ g, whit ψ m f g * conj (whit ψ m φ g) ∂μ.withDensity β'

def U0 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuB E k k) β → ∃ β', IsWt (nuP E k (k - 1)) β' ∧
  (∀ Φ : GA E k → ℝ≥0∞, Measurable Φ → (∀ γ, IsMir (k - 1) γ → ∀ g, Φ (ratGL E k γ * g) = Φ g) →
    ∫⁻ g, Φ g ∂μ.withDensity β' = ∫⁻ g, ∑' ξ : RowT E k k, Φ (ratGL E k (gam ξ) * g) ∂μ.withDensity β) ∧
  ∀ Φ : GA E k → ℂ, Measurable Φ → (∀ γ, IsMir (k - 1) γ → ∀ g, Φ (ratGL E k γ * g) = Φ g) →
    Integrable Φ (μ.withDensity β') → ∫ g, Φ g ∂μ.withDensity β' = ∫ g, sumF Φ g ∂μ.withDensity β

def H0 : Prop := ForE fun E _ _ _ k =>
  (∀ (g : GA E k) ξ, ξ ≠ 0 → 0 < ht g ξ) ∧ (∀ γ (g : GA E k) ξ, ht (ratGL E k γ * g) ξ = ht g (ξ ᵥ* γ.val)) ∧
  (∀ t (g : GA E k) ξ, ξ ≠ 0 → ht (splitCentre E k t * g) ξ = ht g ξ) ∧
  (∀ C : Set (GA E k), IsCompact C → ∃ B : ℝ, ∀ c ∈ C, ∀ g ξ, ξ ≠ 0 → ht (g * c) ξ ≤ B * ht g ξ) ∧
  (∀ C : Set (Fin k → Ad E), IsCompact C → ∃ B : ℝ, ∀ (g : GA E k) ξ, ξ ≠ 0 →
    (fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val ∈ C → height g ξ ≤ B) ∧
  (∃ (B : ℝ) (N : ℕ), 0 ≤ B ∧ ∀ (x : GL (Fin k) (Cinf E)) (g : GA E k) ξ, ξ ≠ 0 → ht g ξ ≤ B *
    (1 + ‖(Matrix.of.symm x.val : LieI (InfinitePlace E) k)‖ + ‖(Matrix.of.symm x⁻¹.val : LieI (InfinitePlace E) k)‖) ^ N *
      ht (g * infGL E k x) ξ) ∧
  ∀ (g h : GA E k), invT (g * h) = invT g * invT h ∧ invT (invT g) = g

def CuspDecayShortRowColumn : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ π : CuspSub E k, IsNormalised π → ∀ φ ∈ π.V, ∀ h : GA E k,
  Dec (fun g => φ.1 (g * h)) ∧ Dec fun g => φ.1 (invT g * h)

def MinkowskiBoundAlt : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∃ C : ℝ, ∀ g : GA E k, ∃ ξ, ξ ≠ 0 ∧ ht g ξ ≤ C

def ThetaSeriesBound : Prop := ForE fun E _ _ _ k => ∀ Cf : Set (Fin k → Af E), IsCompact Cf → ∀ a : ℕ, k ≤ a → ∃ (M : ℕ) (C : ℝ),
  ∀ (g : GA E k) (r : ℝ), 0 < r → (∀ ξ, ξ ≠ 0 → r ≤ height g ξ) →
    ∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)) ≤ ENNReal.ofReal (C * (r ^ a)⁻¹)

def ThetaDecaying : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ φ : GA E k → ℂ, Dec φ →
  (∀ Cf : Set (Fin k → Af E), IsCompact Cf → ∀ a : ℕ, k ≤ a → ∃ (M : ℕ) (C : ℝ), ∀ g : GA E k,
    (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ ≤
        ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k))) ∧
  ∀ C₀ : Set (Fin k → Ad E), IsCompact C₀ → ∀ a : ℕ, k ≤ a → ∃ C : ℝ, ∀ g : GA E k,
    (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) * ‖φ g‖ₑ ≤
      ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k))

def RowsInCompactSet : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ C₀ : Set (Fin k → Ad E), IsCompact C₀ →
  (∀ g : GA E k, {ξ : RowT E k k | lastRow (ratGL E k (gam ξ) * g) ∈ C₀}.Finite) ∧ ∀ a : ℕ, k ≤ a → ∃ C : ℝ, ∀ g : GA E k,
    (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) * ENNReal.ofReal (wt a g) ≤
      ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k))

def C0 : Prop := ForE fun E _ _ _ k => ∀ S : Finset (Pl E), IsOpen (G0 (k := k) S) ∧ (1 : GA E k) ∈ G0 S ∧
  (∀ u g : GA E k, UU 0 u → (u * g ∈ G0 S ↔ g ∈ G0 S)) ∧
  (∀ g ∈ G0 (k := k) S, ∃ n g₀ κ : GA E k, UU 0 n ∧ InS S g₀ ∧ cInf κ = 1 ∧ (∀ w ∈ S, cLoc w κ = 1) ∧
    (∀ w, cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) ∧ g = n * g₀ * κ) ∧
  (∀ g : GA E k, {w | Iwasawa.iwasawaExponent _ k (cLoc w g) ≠ 0}.Finite) ∧
  (∀ (w : Pl E) (l : Fin k → ℤ), IsClopen {g : GA E k | Iwasawa.iwasawaExponent _ k (cLoc w g) = l}) ∧
  ∀ (w : Pl E) (g : GA E k), ∃ g' : GA E k, cLoc w g' = 1 ∧ g = g' * fl k w (cLoc w g) ∧ cInf g' = cInf g ∧
    ∀ v, v ≠ w → cLoc v g' = cLoc v g

def C1 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuP E k 0) β → ∀ (w : Pl E) (l : Fin k → ℤ) (Φ : GA E k → ℂ),
  Measurable Φ → (∀ u, UU 0 u → ∀ g, Φ (u * g) = Φ g) → Integrable Φ (μ.withDensity β) →
    Integrable (fun g => Φ (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l) * g)) (μ.withDensity β) ∧
    ∫ g, Φ g ∂μ.withDensity β = (Ideal.absNorm w.asIdeal : ℂ) ^ rhoPair l *
      ∫ g, Φ (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l) * g) ∂μ.withDensity β

def C2 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuP E k 0) β → ∀ (S : Finset (Pl E)) (Φ : GA E k → ℂ)
  (a : Off E S → (Fin k → ℤ) → ℂ), Measurable Φ → (∀ u, UU 0 u → ∀ g, Φ (u * g) = Φ g) → LawOff S Φ a → (∀ w, a w 0 = 1) →
    Integrable Φ (μ.withDensity β) →
    HasSum (fun l : Off E S →₀ (Fin k → ℤ) => (∏ w ∈ l.support, (nq w : ℂ) ^ rhoPair (l w) * a w (l w)) *
      ∫ g in G0 S, Φ g ∂μ.withDensity β) (∫ g, Φ g ∂μ.withDensity β)

def D1 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuP E k 0) β → ∀ (S : Finset (Pl E)) (P : GA E k → ℂ) (u : ℝ)
  (z₀ : ℂ), Continuous P → (∀ n, UU 0 n → ∀ g, P (n * g) = P g) → 0 < (P 1).re →
    (∃ a b : ℝ, 0 < a ∧ ∀ g ∈ G0 S, P g ≠ 0 → a ≤ Dt g ∧ Dt g ≤ b ∧ 0 ≤ (P g * (Dt g : ℂ) ^ ((u : ℂ) * Complex.I)).re) →
    Integrable (fun g => P g * (Dt g : ℂ) ^ z₀) (μ.withDensity β) →
    Differentiable ℂ (fun z : ℂ => ∫ g in G0 S, P g * (Dt g : ℂ) ^ z ∂μ.withDensity β) ∧
      ∀ σ : ℝ, ∫ g in G0 S, P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I) ∂μ.withDensity β ≠ 0

def E1 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuB E k k) β → ∀ H₀ : GA E k → ℂ, Measurable H₀ → RatInv H₀ →
  (∀ t g, H₀ (splitCentre E k t * g) = H₀ g) → (∃ C : ℝ, ∀ g, ‖H₀ g‖ ≤ C) → ∀ z : ℂ, 0 < z.re →
    z * ∫ g in {g | Dt g < 1}, H₀ g * (Dt g : ℂ) ^ z ∂μ.withDensity β =
      ((k : ℂ) * Module.finrank ℚ E)⁻¹ * ∫ g in band E k, H₀ g ∂μ.withDensity β

def E2 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuB E k k) β → ∀ H H₀ : GA E k → ℂ, Grow H H₀ →
  ∃ Z : ℂ → ℂ, DifferentiableOn ℂ Z {s | 0 < s.re} ∧
    (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∫ g, H g * (Dt g : ℂ) ^ s ∂μ.withDensity β) ∧
    (∫ g in band E k, H₀ g ∂μ.withDensity β = 0 → Z 1 = 0)

def M0 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuB E k k) β → ∀ ψ, StdPsi ψ →
  ∀ (S : Finset (Pl E)) (m : ℕ) (α : Off E S → Fin m → ℂˣ) (α' : Off E S → Fin k → ℂˣ) (u : ℝ) (f φ : GA E k → ℂ),
    Dat ψ S α α' u f φ → ∃ (β' : GA E k → ℝ≥0∞) (σ₀ : ℝ), IsWt (nuP E k 0) β' ∧ ∀ z : ℂ, σ₀ < z.re →
      Integrable (fun g => PW ψ f φ g * (Dt g : ℂ) ^ z) (μ.withDensity β') ∧
      ∫ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ z ∂μ.withDensity β = ∫ g, PW ψ f φ g * (Dt g : ℂ) ^ z ∂μ.withDensity β'

def M1 : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuB E k k) β → ∀ ψ, StdPsi ψ →
  ∀ (S : Finset (Pl E)) (m : ℕ) (α : Off E S → Fin m → ℂˣ) (α' : Off E S → Fin k → ℂˣ) (u : ℝ) (f φ : GA E k → ℂ),
    k ≤ m → (∀ w a, ‖(α w a : ℂ)‖ ≤ Real.sqrt (nq w)) → (∀ w b, ‖(α' w b : ℂ)‖ ≤ Real.sqrt (nq w)) →
    Dat ψ S α α' u f φ → ∃ (ZS : ℂ → ℂ) (σ₀ : ℝ), Differentiable ℂ ZS ∧ (∀ σ : ℝ, ZS (σ + u * Complex.I) ≠ 0) ∧
      ∀ s : ℂ, σ₀ < s.re → ∫ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2)) * (Dt g : ℂ) ^ s
        ∂μ.withDensity β = ZS s * LS S α α' s

def K1 : Prop := ForE fun E _ _ _ k => 1 ≤ k → Continuous (dmin : GA E k → ℝ) ∧ (∀ g : GA E k, 0 < dmin g) ∧
  (∀ (g : GA E k) ξ, ξ ≠ 0 → dmin g ≤ ht g ξ) ∧ RatInv (dmin : GA E k → ℝ) ∧
  (∀ C : Set (GA E k), IsCompact C → ∃ B : ℝ, 1 ≤ B ∧ ∀ c ∈ C, ∀ g, dmin (g * c) ≤ B * dmin g) ∧
  ∀ f : GA E k → ℂ, Dec f → ∀ M, ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C * wt M g

def K2 : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ M, ∃ ρ J, WRep (E := E) (k := k) (wt M) ρ J ∧
  ∀ x, SmV (ρ.comp (infGL E k)) x → SmV (repI E k) (J x)

def K3 : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ M ρ J, WRep (E := E) (k := k) (wt M) ρ J →
  ∀ π : CuspSub E k, IsNormalised π → ∀ φ ∈ π.V, ∃ x, (J x : GA E k → ℂ) = φ.1 ∧ SmV (ρ.comp (infGL E k)) x

def K7 : Prop := ForE fun E _ _ _ k => ∀ ψ, StdPsi ψ → ∀ w, Cond ψ w → ∃ χ : AddChar (w.adicCompletion E) ℂ,
  PositivityTheory.JacquetShalikaLocal.PsiOK χ ∧ (∀ y, χ y = ψ (sFin E (sLoc E w y))) ∧ ∀ (z : Fin k → ℂˣ) (φ : XB E k), Good ψ (k - 1) φ →
    SatFn w (Finset.univ.val.map z) φ → ∀ g, cLoc w g = 1 → ∀ x,
      Wh ψ φ (g * fl k w x) = Wh ψ φ g * sphericalWhittaker χ z x

def K8 : Prop := ForE fun E _ _ _ k => ∀ ψ, StdPsi ψ → ∀ S : Finset (Pl E), (∀ w, w ∉ S → Cond ψ w) →
  ∀ (α : Off E S → Fin k → ℂˣ) (φ : XB E k), Good ψ (k - 1) φ → (∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) φ) →
    SphOff S (φ : GA E k → ℂ) ∧ SphOff S (Wh ψ φ) ∧ ∀ g, Wh ψ φ g ≠ 0 →
      (∀ g₀ : GA E k, cInf g₀ = cInf g → (∀ w ∈ S, cLoc w g₀ = cLoc w g) → InS S g₀ → Wh ψ φ g₀ ≠ 0) ∧
      ∀ w, w ∉ S → Antitone (Iwasawa.iwasawaExponent _ k (cLoc w g))

def InfinitePlaceStep : Prop := ForE fun E _ _ _ k => ∀ w ρ J, WRep (E := E) (k := k) w ρ J → ∀ ψ, StdPsi ψ →
  ∀ (S : Finset (Pl E)) (Y : Submodule ℂ (XB E k)), YOK ψ S Y → ∀ n m, n + 1 < k → (∀ v, v ∉ S → m v = 0) →
    ∀ U ∈ 𝓝 (1 : GA E k), ∀ x C, J x ∈ Y → SmV (ρ.comp (infGL E k)) x → Lev S (J x) → Bump ψ S (Om n m) C (Wh ψ (J x)) →
      ∃ x' C₀, C₀ ⊆ U ∧ J x' ∈ Y ∧ SmV (ρ.comp (infGL E k)) x' ∧ Lev S (J x') ∧ (∀ c ∈ C₀, GlobalTheory (n + 1) c) ∧
        Bump ψ S (Om (n + 1) m) (Set.image2 (· * ·) C C₀) (Wh ψ (J x'))

open Classical in

def FinitePlaceStep : Prop := ForE fun E _ _ _ k => ∀ w ρ J, WRep (E := E) (k := k) w ρ J → ∀ ψ, StdPsi ψ →
  ∀ (S : Finset (Pl E)) (Y : Submodule ℂ (XB E k)), YOK ψ S Y → ∀ n m, ∀ v ∈ S, m v + 1 < k → (∀ v, v ∉ S → m v = 0) →
    ∀ U ∈ 𝓝 (1 : GA E k), ∀ x C, J x ∈ Y → SmV (ρ.comp (infGL E k)) x → Lev S (J x) → Bump ψ S (Om n m) C (Wh ψ (J x)) →
      ∃ x' C₀, C₀ ⊆ U ∧ J x' ∈ Y ∧ SmV (ρ.comp (infGL E k)) x' ∧ Lev S (J x') ∧ (∀ c ∈ C₀, GlobalTheory (m v + 1) c) ∧
        Bump ψ S (Om n (Function.update m v (m v + 1))) (Set.image2 (· * ·) C C₀) (Wh ψ (J x'))

def K4 : Prop := ForE fun E _ _ _ k => ∀ w ρ J, WRep (E := E) (k := k) w ρ J → ∀ ψ, StdPsi ψ →
  ∀ (S : Finset (Pl E)) (Y : Submodule ℂ (XB E k)), YOK ψ S Y → ∀ j < k, ∀ U ∈ 𝓝 (1 : GA E k),
    ∀ x, J x ∈ Y → SmV (ρ.comp (infGL E k)) x → Lev S (J x) → Wh ψ (J x) 1 = 1 →
      ∃ x' C, C ⊆ U ∧ J x' ∈ Y ∧ SmV (ρ.comp (infGL E k)) x' ∧ Lev S (J x') ∧ (∀ c ∈ C, GlobalTheory j c) ∧
        Bump ψ S (fun g => InS S g ∧ Mir j g) C (Wh ψ (J x'))

def K9 : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ ψ, StdPsi ψ → (∀ᶠ w in cofinite, Cond ψ w) →
  ∀ π : CuspSub E k, IsNormalised π → ∃ S₀ : Finset (Pl E), ∀ S, S₀ ⊆ S → (∀ w, w ∉ S → Cond ψ w) ∧
    ∀ α : Off E S → Fin k → ℂˣ, SatOff (CG.mk π) S α → ∃ φ ∈ π.V, ∃ (h : GA E k) (x : XB E k), InS S h ∧
      (x : GA E k → ℂ) = φ.1 ∧ (∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) x) ∧ Lev S x ∧ Wh ψ (Rt E k h x) 1 = 1

structure Prep {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} (ψ : AddChar (Ad E) ℂ) (S : Finset (Pl E))
    (α : Off E S → Fin k → ℂˣ) (M j : ℕ) (U : Set (GA E k)) (φ : XB E k) : Prop where
  good : Good ψ (k - 1) φ
  inv : RatInv (φ : GA E k → ℂ)
  sat : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) φ
  smooth : SmV (repI E k) φ
  lev : Lev S φ
  dec : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * wt M g
  bump : ∃ C, C ⊆ U ∧ (∀ c ∈ C, GlobalTheory j c) ∧ Bump ψ S (fun g => InS S g ∧ Mir j g) C (Wh ψ φ)

def KIR : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ ψ, StdPsi ψ → (∀ᶠ w in cofinite, Cond ψ w) →
  ∀ π : CuspSub E k, IsNormalised π → ∃ S₀ : Finset (Pl E), ∀ S, S₀ ⊆ S → ∀ α : Off E S → Fin k → ℂˣ,
    SatOff (CG.mk π) S α → ∀ M, ∀ j < k, ∀ U ∈ 𝓝 (1 : GA E k), ∀ Y : Submodule ℂ (XB E k), IsClosed (Y : Set (XB E k)) →
      (∀ g, ∀ x ∈ Y, Rt E k g x ∈ Y) → (∀ x : XB E k, (∃ φ ∈ π.V, (x : GA E k → ℂ) = φ.1) → x ∈ Y) →
      ∃ φ ∈ Y, Prep ψ S α M j U φ

structure Sec {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} (ψ : AddChar (Ad E) ℂ) (S : Finset (Pl E))
    (α : Off E S → Fin k → ℂˣ) (φ : XB E k) : Prop where
  good : Good ψ (k - 1) φ
  inv : RatInv (φ : GA E k → ℂ)
  cen : ∀ t g, φ (splitCentre E k t * g) = φ g
  sat : ∀ w : Off E S, SatFn w.1 (Finset.univ.val.map (α w)) φ
  dec : Dec φ
  dec' : Dec fun g => φ (invT g)
  one : Wh ψ φ 1 = 1

def KSec : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ ψ, StdPsi ψ → (∀ᶠ w in cofinite, Cond ψ w) →
  ∀ π : CuspSub E k, IsNormalised π → ∃ S₀ : Finset (Pl E), ∀ S, S₀ ⊆ S → (∀ w, w ∉ S → Cond ψ w) ∧
    ∀ α : Off E S → Fin k → ℂˣ, SatOff (CG.mk π) S α →
      ∃ φ₀ ∈ π.V, ∃ (h : GA E k) (φ : XB E k), (∀ g, φ g = φ₀.1 (g * h)) ∧ Sec ψ S α φ

def CornerEmbedding : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m k : ℕ), k ≤ m →
  (∀ (R : Type) [CommRing R], ∃ ι : GL (Fin k) R →* GL (Fin m) R, IsEmb ι) ∧ ∀ ι : GA E k →* GA E m, IsEmb ι →
    Continuous ι ∧ (∀ g, GlobalTheory k (ι g)) ∧ (∀ x : GA E m, GlobalTheory k x → ∃ g, x = ι g) ∧ (∀ g, Dt (ι g) = Dt g) ∧
    (∀ U ∈ 𝓝 (1 : GA E k), ∃ U' ∈ 𝓝 (1 : GA E m), ∀ g, ι g ∈ U' → g ∈ U) ∧
    (∀ C : Set (GA E m), IsCompact C → IsCompact (ι ⁻¹' C)) ∧
    (∀ ιE : GL (Fin k) E →* GL (Fin m) E, IsEmb ιE → ∀ γ, ι (ratGL E k γ) = ratGL E m (ιE γ)) ∧
    (∀ (w : Pl E) (ιw : GL (Fin k) (w.adicCompletion E) →* GL (Fin m) (w.adicCompletion E)), IsEmb ιw →
      (∀ x, ι (fl k w x) = fl m w (ιw x)) ∧ (∀ g, cLoc w (ι g) = ιw (cLoc w g)) ∧
      (∀ n ∈ Iwasawa.unipotent _ k, ιw n ∈ Iwasawa.unipotent _ m) ∧
      (∀ κ ∈ GLnLocal.integralGL _ k, ιw κ ∈ GLnLocal.integralGL _ m) ∧
      ∀ l, ιw (Iwasawa.torusPow _ k l) = Iwasawa.torusPow _ m (pad m l)) ∧
    (∀ κ : GA E k, jumpWindows.cInf κ = 1 → jumpWindows.cInf (ι κ) = 1) ∧ (∀ n, UU 0 (ι n) ↔ UU 0 n) ∧ ∀ ψ n, psN ψ (ι n) = psN ψ n

def TransformsEmbedding : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m k : ℕ), 1 ≤ k → k < m →
  ∀ ψ, StdPsi ψ → ∀ ι : GA E k →* GA E m, IsEmb ι → ∀ φ : GA E m → ℂ, Good ψ (m - 1) φ →
    Good ψ k (pT ψ (k + 1) (m - (k + 1)) φ) ∧ pT ψ k (m - k) φ = colT ψ k (pT ψ (k + 1) (m - (k + 1)) φ) ∧
    Pre ψ (k - 1) (fun g => pT ψ k (m - k) φ (ι g)) ∧
    (∀ g, whit ψ (k - 1) (fun g => pT ψ k (m - k) φ (ι g)) g = whit ψ (m - 1) φ (ι g)) ∧
    (∀ g, pT ψ k (m - k) φ (ι g) ≠ 0 → ∃ p : GA E k, Mir (k - 1) p ∧ whit ψ (m - 1) φ (ι (p * g)) ≠ 0) ∧
    ∀ (j : ℕ) (x : GA E m) (B : ℝ), 1 ≤ j → j ≤ m → (∀ u, UU j u → ‖φ (u * x)‖ ≤ B) → ‖pT ψ j (m - j) φ x‖ ≤ B

def FourierSeriesColumn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m k : ℕ), 1 ≤ k → k < m →
  ∀ ψ, StdPsi ψ → ∀ ι : GA E k →* GA E m, IsEmb ι → ∀ F : GA E m → ℂ, Good ψ k F → ∀ g : GA E k,
    (∀ B : ℝ, (∀ x : UnipotentBlockColumnIndex m k k → Ad E, ‖F (blkU x * ι g)‖ ≤ B) →
      ∑' ξ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ξ) * g))‖ₑ ^ 2 ≤ ENNReal.ofReal (B ^ 2)) ∧
    ({ξ : RowT E k k | colT ψ k F (ι (ratGL E k (gam ξ) * g)) ≠ 0}.Finite → sumF (fun h => colT ψ k F (ι h)) g = F (ι g))

def ShortRowsEmbedding : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m k : ℕ), 1 ≤ k → k < m →
  ∀ ι : GA E k →* GA E m, IsEmb ι → ∃ C : ℝ, ∀ (g : GA E k) (u : GA E m),
    (UU 0 u → dmin (u * ι g) ≤ Dt g ^ (-(m : ℝ)⁻¹)) ∧
    (UU (k + 1) u → dmin (u * ι g) ≤ C * Dt g ^ (((m : ℝ) - 1)⁻¹ - (m : ℝ)⁻¹))

def K6 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m k : ℕ), 1 ≤ k → k < m →
  ∀ ψ, StdPsi ψ → ∀ S : Finset (Pl E), (∀ w, w ∉ S → Cond ψ w) → ∀ ι : GA E k →* GA E m, IsEmb ι →
    ∀ (α : Off E S → Fin m → ℂˣ) M U (φ : XB E m), Prep ψ S α M k U φ →
      ∃ C : Set (Fin k → Ad E), IsCompact C ∧ ∀ g, Wh ψ φ (ι g) ≠ 0 → lastRow g ∈ C

def LocalHeckeAlgebra : Prop := ∀ (E : Type) [Field E] [NumberField E] (S : Finset (Pl E)) (m k : ℕ) (α : Off E S → Fin m → ℂˣ)
  (α' : Off E S → Fin k → ℂˣ) (w : Off E S) (χ : AddChar (w.1.adicCompletion E) ℂ), PositivityTheory.JacquetShalikaLocal.PsiOK χ → 1 ≤ k → k ≤ m →
    aLoc α α' w 0 = 1 ∧ ∀ l : Fin k → ℤ,
      (∀ s : ℂ, (nq w : ℂ) ^ rhoPair l * (aLoc α α' w l * (((nq w : ℝ) ^ (-∑ i, l i) : ℝ) : ℂ) ^ (s - ((m : ℂ) - k) / 2)) =
        loc (nq w) (α w) (α' w) s l) ∧
      ((k < m ∨ ∀ i : Fin k, (i : ℕ) + 1 = k → 0 ≤ l i) →
        sphericalWhittaker χ (α w) (Iwasawa.torusPow _ m (pad m l)) *
          conj (sphericalWhittaker χ (α' w) (Iwasawa.torusPow _ k l)) = aLoc α α' w l) ∧
      ((∃ i, l i < 0) → aLoc α α' w l = 0)

def KU : Prop := ForE fun E _ _ _ k => ∀ ψ, StdPsi ψ → ∀ (φ : XB E k) (u : ℝ), Good ψ (k - 1) φ → Wh ψ φ 1 = 1 →
  ∃ U ∈ 𝓝 (1 : GA E k), ∀ c ∈ U, 1 / 2 ≤ Dt c ∧ Dt c ≤ 2 ∧ 0 < (conj (Wh ψ φ c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I)).re

def KLt1 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m k : ℕ), 1 ≤ k → k < m →
  ∀ ψ, StdPsi ψ → ∀ S : Finset (Pl E), (∀ w, w ∉ S → Cond ψ w) → ∀ ι : GA E k →* GA E m, IsEmb ι →
    ∀ (α : Off E S → Fin m → ℂˣ) (α' : Off E S → Fin k → ℂˣ) (u : ℝ) (φ' : XB E k), Sec ψ S α' φ' →
      ∃ U ∈ 𝓝 (1 : GA E m), ∀ M, 1 ≤ M → ∀ φ : XB E m, Prep ψ S α M k U φ →
        Dat ψ S α α' u (fun g => pT ψ k (m - k) φ (ι g)) φ'

def KLt2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m k : ℕ), 1 ≤ k → k < m →
  ∀ ψ, StdPsi ψ → ∀ S : Finset (Pl E), (∀ w, w ∉ S → Cond ψ w) → ∀ ι : GA E k →* GA E m, IsEmb ι →
    ∀ (α : Off E S → Fin m → ℂˣ) (α' : Off E S → Fin k → ℂˣ) (φ' : XB E k), Sec ψ S α' φ' →
      ∀ U (φ : XB E m), Prep ψ S α (m ^ 3) k U φ →
        Grow (fun g => sumF (fun g => pT ψ k (m - k) φ (ι g)) g * conj (φ' g) * (Dt g : ℂ) ^ (-(((m : ℂ) - k) / 2))) 0

def LastRowCutoff : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ ψ, StdPsi ψ → ∀ S : Finset (Pl E), (∀ w, w ∉ S → Cond ψ w) →
  ∀ U ∈ 𝓝 (1 : GA E k), ∀ φ : XB E k, SmV (repI E k) φ → Lev S φ → ∃ η s, Cut ψ S U φ η s

def PoissonCutoffFormula : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ ψ, StdPsi ψ → ∀ (S : Finset (Pl E)) U (φ : XB E k) η s,
  Cut ψ S U φ η s → RatInv (φ : GA E k → ℂ) → ∀ g,
    (Dt g : ℂ) * sumF (fun g => (η (lastRow g) : ℂ) * φ (g * (s (lastRow g))⁻¹)) g =
      (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k)) + ∑' ξ : {ξ : Fin k → E // ξ ≠ 0},
        ∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) * ψ (∑ i, y i * ((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* (invT g).val) i)
          ∂vecMeasure E (Fin k)

def KEq1 : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ ψ, StdPsi ψ → ∀ S : Finset (Pl E), (∀ w, w ∉ S → Cond ψ w) →
  ∀ (α α' : Off E S → Fin k → ℂˣ) (u : ℝ) (φ' : XB E k), Sec ψ S α' φ' →
    ∃ U ∈ 𝓝 (1 : GA E k), ∀ φ : XB E k, Prep ψ S α (k + 1) (k - 1) U φ → ∀ η s, Cut ψ S U φ η s →
      Dat ψ S α α' u (fun g => (η (lastRow g) : ℂ) * φ (g * (s (lastRow g))⁻¹)) φ'

def KEq2 : Prop := ForE fun E _ _ _ k => 1 ≤ k → ∀ ψ, StdPsi ψ → ∀ (S : Finset (Pl E)) (α' : Off E S → Fin k → ℂˣ)
  (φ' : XB E k), Sec ψ S α' φ' → ∀ U (φ : XB E k) η s, Cut ψ S U φ η s → RatInv (φ : GA E k → ℂ) →
    (∀ t g, φ (splitCentre E k t * g) = φ g) →
    Grow (fun g => sumF (fun g => (η (lastRow g) : ℂ) * φ (g * (s (lastRow g))⁻¹)) g * conj (φ' g) *
        (Dt g : ℂ) ^ (-(((k : ℂ) - k) / 2)))
      fun g => (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k)) * conj (φ' g)

def ORT : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuB E k k) β → ∀ π π' : CuspSub E k, IsNormalised π →
  IsNormalised π' → π ≠ π' → ∀ φ ∈ π.V, ∀ φ' ∈ π'.V, ∀ h h' : GA E k,
    ∫ g in band E k, φ.1 (g * h) * conj (φ'.1 (g * h')) ∂μ.withDensity β = 0

def KY : Prop := ForMu fun E _ _ _ k μ => 1 ≤ k → ∀ β, IsWt (nuB E k k) β → ∀ φ' : XB E k,
  ∃ Y : Submodule ℂ (XB E k), IsClosed (Y : Set (XB E k)) ∧ (∀ g, ∀ x ∈ Y, Rt E k g x ∈ Y) ∧
    (∀ x : XB E k, x ∈ Y ↔ (∀ t g, x (splitCentre E k t * g) = x g) ∧
      ∀ h, ∫ g in band E k, x (g * h) * conj (φ' g) ∂μ.withDensity β = 0) ∧
    ∀ φ ∈ Y, ∀ ψ S U η s, Cut ψ S U φ η s →
      ∫ g in band E k, (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k)) * conj (φ' g) ∂μ.withDensity β = 0

end PositivityTheory.AdelicQuotientData

end
