import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

abbrev Mx (n : ℕ) : Type := Fin n → Fin n → ℂ

def SmoothSum : Prop :=
  ∀ (X P : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] (W : X × P → ℂ), ContDiff ℝ ∞ W →
    ∀ (K : Set P) (B : Set X), IsCompact K → IsCompact B → ∀ (I : Type) (p : I → P), (∀ i, p i ∈ K) →
    ∀ a : I → ℂ, Summable (fun i => ‖a i‖) →
      ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ x ∈ B, Φ x = ∑' i, a i * W (x, p i)

def ClosedGraph : Prop :=
  ∀ (Ω I : Type) [MeasurableSpace Ω] (m : Measure Ω) (u : I → Ω → ℂ), (∀ x, ∃ M : ℝ, ∀ i, ‖u i x‖ ≤ M) →
    (∀ a : I → ℂ, Summable (fun i => ‖a i‖) → Integrable (fun x => ∑' i, a i * u i x) m) →
    ∃ B : ℝ, ∀ i, Integrable (u i) m ∧ ∫ x, ‖u i x‖ ∂m ≤ B

def ker {H Ω I : Type} (c : I → Ω → ℂ) (q : I → Ω → H) (φ : H → ℂ) (x : Ω) : ℂ := ∑' i, c i x * φ (q i x)

structure IsKer {H Ω I : Type} [Group H] [TopologicalSpace H] [MeasurableSpace H] [MeasurableSpace Ω] {n : ℕ}
    (ι : H →* Matrix (Fin n) (Fin n) ℂ) (m : Measure Ω) (c : I → Ω → ℂ) (q : I → Ω → H) : Prop where
  mc : ∀ i, Measurable (c i)
  mq : ∀ i, Measurable (q i)
  fin : ∀ x (C : Set H), IsCompact C → {i | c i x ≠ 0 ∧ q i x ∈ C}.Finite
  int : ∀ φ ∈ CcMat ι, Integrable (ker c q φ) m

def BumpOn : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (n : ℕ) (ι : H →* Matrix (Fin n) (Fin n) ℂ),
    Topology.IsClosedEmbedding (matCoord ι) → ∀ C : Set H, IsCompact C → ∃ φ ∈ CcMat ι, ∀ y ∈ C, φ y = 1

def KerUnif : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (n : ℕ) (ι : H →* Matrix (Fin n) (Fin n) ℂ),
    Topology.IsClosedEmbedding (matCoord ι) →
    ∀ (Ω I : Type) [MeasurableSpace Ω] [Countable I] (m : Measure Ω) [SFinite m] (c : I → Ω → ℂ) (q : I → Ω → H), IsKer ι m c q →
    ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (W : Mx n × P → ℂ) (p : H → P)
    (K C : Set H), ContDiff ℝ ∞ W → Continuous p → IsCompact K → IsCompact C →
    (∀ k ∈ K, ∀ y ∉ C, W (matCoord ι y, p k) = 0) →
    ∃ B : ℝ, ∀ k ∈ K, Integrable (ker c q fun y => W (matCoord ι y, p k)) m ∧
      ∫ x, ‖ker c q (fun y => W (matCoord ι y, p k)) x‖ ∂m ≤ B

def KerSwap : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (n : ℕ) (ι : H →* Matrix (Fin n) (Fin n) ℂ),
    Topology.IsClosedEmbedding (matCoord ι) → ∀ (μ : Measure H) [μ.IsHaarMeasure]
    (Ω I : Type) [MeasurableSpace Ω] [Countable I] (m : Measure Ω) [SFinite m] (c : I → Ω → ℂ) (q : I → Ω → H), IsKer ι m c q →
    ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] (W : Mx n × P → ℂ) (p : H → P)
    (K C : Set H), ContDiff ℝ ∞ W → Continuous p → IsCompact K → IsCompact C →
    (∀ k ∈ K, ∀ y ∉ C, W (matCoord ι y, p k) = 0) →
    ∫ k in K, (∫ x, ker c q (fun y => W (matCoord ι y, p k)) x ∂m) ∂μ =
      ∫ x, ker c q (fun y => ∫ k in K, W (matCoord ι y, p k) ∂μ) x ∂m

structure IsWeight {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ B
  nonneg : ∀ z, 0 ≤ B z
  pos : 0 < B (matCoord ι s, matCoord ι 1)
  shift : ∀ z h z' h' : H, ∃ t₀ ∈ cent s, ∀ t ∈ cent s,
    B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * t * h)) =
      B (matCoord ι (z'⁻¹ * s * z'), matCoord ι (z'⁻¹ * (t * t₀) * h'))
  proper : ∀ C₁ C₂ : Set H, IsCompact C₁ → IsCompact C₂ → ∃ K : Set H, IsCompact K ∧ ∀ z k : H,
    z⁻¹ * s * z ∈ C₁ → (z * k)⁻¹ * s * (z * k) ∈ C₂ → B (matCoord ι (z⁻¹ * s * z), matCoord ι k) ≠ 0 → k ∈ K

def Lagr : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℂ), Function.Injective l → ∃ e : Fin n → Mx n → Mx n, (∀ i, ContDiff ℝ ∞ (e i)) ∧
    ∀ (i : Fin n) (g g' : Matrix (Fin n) (Fin n) ℂ), g' * g = 1 → g * g' = 1 →
      Matrix.of (e i fun a b => (g' * diagonal l * g) a b) = g' * single i i 1 * g

def ShiftT : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ), Function.Injective l →
    (diagonal l)ᴴ * J * diagonal l = J → ∀ σ : Fin n → ℝ, (∀ i, 0 < σ i) →
      ∃ τ : Fin n → ℂ, (diagonal τ)ᴴ * J * diagonal τ = J ∧ ∀ i, 1 < ‖l i‖ → ‖τ i‖ ^ 2 = σ i

def BoundT : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ), IsUnit J.det → Function.Injective l →
    (diagonal l)ᴴ * J * diagonal l = J → ∀ a b : ℝ, 0 < a → ∃ R : ℝ, ∀ τ : Fin n → ℂ,
      (diagonal τ)ᴴ * J * diagonal τ = J → (∀ i, 1 < ‖l i‖ → a ≤ ‖τ i‖ ∧ ‖τ i‖ ≤ b) → ∀ j, ‖τ j‖ ≤ R

def IsUGroup {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (J : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsUnit J.det ∧ Topology.IsClosedEmbedding (matCoord ι) ∧ ∀ M, M ∈ Set.range ι ↔ Mᴴ * J * M = J

def WeightDiag : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (n : ℕ) (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (J : Matrix (Fin n) (Fin n) ℂ), IsUGroup ι J → ∀ (s : H) (l : Fin n → ℂ), Function.Injective l →
    ι s = diagonal l → IsProperOrbit (cent s) s → ∃ B, IsWeight ι s B

def Weight : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (n : ℕ) (ι : H →* Matrix (Fin n) (Fin n) ℂ)
    (J : Matrix (Fin n) (Fin n) ℂ), IsUGroup ι J → ∀ s : H, IsRegSS (ι s) → IsProperOrbit (cent s) s →
    ∃ B, IsWeight ι s B

def IdentOne : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (n : ℕ) (ι : H →* Matrix (Fin n) (Fin n) ℂ),
    Continuous (matCoord ι) → ∀ (s : H) (B : Mx n × Mx n → ℝ), IsWeight ι s B → ∀ (μ : Measure H) [μ.IsHaarMeasure]
    (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (φ : H → ℝ), Continuous φ →
    HasCompactSupport φ → (∀ y, 0 ≤ φ y) → 0 < φ s → ∃ a : ℂ, a ≠ 0 ∧ ∀ z : H,
      ∫ k, (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) * (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ∂μ = a

def IdentTwo : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (n : ℕ) (ι : H →* Matrix (Fin n) (Fin n) ℂ),
    Continuous (matCoord ι) → ∀ (s : H) (B : Mx n × Mx n → ℝ), IsWeight ι s B → ∀ (μ : Measure H) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (φ : H → ℂ),
    Continuous φ → HasCompactSupport φ → HasOrbInt μ s dt φ 0 → ∀ h : H,
      ∫ k, φ (k * (h⁻¹ * s * h) * k⁻¹) * (B (matCoord ι (k * (h⁻¹ * s * h) * k⁻¹), matCoord ι k) : ℂ) ∂μ = 0

def Vanish : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (n : ℕ) (ι : H →* Matrix (Fin n) (Fin n) ℂ),
    Topology.IsClosedEmbedding (matCoord ι) → ∀ (s : H) (B : Mx n × Mx n → ℝ), IsWeight ι s B →
    ∀ (μ : Measure H) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (dt : Measure (cent s)) [dt.IsHaarMeasure]
    [dt.IsMulRightInvariant] (Ω I : Type) [MeasurableSpace Ω] [Countable I] (m : Measure Ω) [SFinite m] (c : I → Ω → ℂ) (q : I → Ω → H), IsKer ι m c q →
    (∀ i x, ∃ z : H, q i x = z⁻¹ * s * z) →
    (∀ φ ∈ CcMat ι, ∀ k : H, ∫ x, ker c q (fun y => φ (k * y * k⁻¹)) x ∂m = ∫ x, ker c q φ x ∂m) →
    ∀ φ ∈ CcMat ι, HasOrbInt μ s dt φ 0 → ∫ x, ker c q φ x ∂m = 0

def FDRight : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ F : G → ℂ, (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → ∀ g : G,
      ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in 𝓕, F x ∂μ

example {H : Type} [Group H] [TopologicalSpace H] [MeasurableSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) :
    IsKer ι (Measure.dirac ()) (fun _ : Unit => fun _ => (1 : ℂ)) (fun _ _ => (1 : H)) :=
  ⟨fun _ => measurable_const, fun _ => measurable_const, fun _ _ _ => Set.toFinite _, fun _ _ => Integrable.of_finite⟩

end MainStatements.WeightKernel

end
