import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.SgMemUnipB

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction
open GroundTheory.Automorphic.Whittaker (transl supportedIn vanishingOn)

namespace UpperTheory.Gal.LocD

def StabSub : Prop :=
  ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] (τ : H →* H) (p : ℕ), 0 < p → Continuous τ → (∀ h, τ^[p] h = h) →
    ∀ L : Subgroup H, IsOpen (L : Set H) →
      ∃ L₀ : Subgroup H, IsCompact (L₀ : Set H) ∧ IsOpen (L₀ : Set H) ∧ L₀ ≤ L ∧ ∀ l, τ l ∈ L₀ ↔ l ∈ L₀

def CellStep : Prop :=
  ∀ (X H : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [MulAction H X] [ContinuousSMul H X]
    (s : X → X) (τ : H →* H) (p : ℕ), 0 < p → Continuous s → Continuous τ → (∀ x, s^[p] x = x) → (∀ h, τ^[p] h = h) →
    (∀ (h : H) x, s (h • x) = τ h • s x) → ∀ χ : H →* ℂ, (∃ L : Subgroup H, IsOpen (L : Set H) ∧ ∀ l ∈ L, χ l = 1) →
    ∀ D : (X → ℂ) →ₗ[ℂ] ℂ, (∀ h : H, ∀ f ∈ Cc X, D (transl h f) = χ h * D f) →
    (∀ f ∈ Cc X, ∑ i ∈ Finset.range p, D (f ∘ s^[i]) = 0) →
    ∀ (U C : Set X) (x₀ : X), IsOpen U → IsClosed C → U ∩ C = orbit H x₀ → (∀ h : H, ∀ x ∈ U, h • x ∈ U) →
    (∀ x, s x ∈ U ↔ x ∈ U) → s x₀ = x₀ → (∀ f ∈ supportedIn U ⊓ vanishingOn C, D f = 0) → ∀ f ∈ supportedIn U, D f = 0

def DistZero : Prop :=
  ∀ (X H : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [MulAction H X] [ContinuousSMul H X]
    (s : X → X) (τ : H →* H) (p : ℕ), 0 < p → Continuous s → Continuous τ → (∀ x, s^[p] x = x) → (∀ h, τ^[p] h = h) →
    (∀ (h : H) x, s (h • x) = τ h • s x) → ∀ χ : H →* ℂ, (∃ L : Subgroup H, IsOpen (L : Set H) ∧ ∀ l ∈ L, χ l = 1) →
    ∀ (k : ℕ) (x : Fin k → X), (∀ j, s (x j) = x j) → (∀ y, ∃! j, y ∈ orbit H (x j)) →
    (∀ j, closure (orbit H (x j)) ⊆ ⋃ l, ⋃ (_ : j ≤ l), orbit H (x l)) →
    ∀ D : (X → ℂ) →ₗ[ℂ] ℂ, (∀ h : H, ∀ f ∈ Cc X, D (transl h f) = χ h * D f) →
    (∀ f ∈ Cc X, ∑ i ∈ Finset.range p, D (f ∘ s^[i]) = 0) → ∀ f ∈ Cc X, D f = 0

def DistInv : Prop :=
  ∀ (X H : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [MulAction H X] [ContinuousSMul H X]
    (s : X → X) (τ : H →* H) (p : ℕ), 0 < p → Continuous s → Continuous τ → (∀ x, s^[p] x = x) → (∀ h, τ^[p] h = h) →
    (∀ (h : H) x, s (h • x) = τ h • s x) → ∀ χ : H →* ℂ, (∃ L : Subgroup H, IsOpen (L : Set H) ∧ ∀ l ∈ L, χ l = 1) →
    (∀ h, χ (τ h) = χ h) →
    ∀ (k : ℕ) (x : Fin k → X), (∀ j, s (x j) = x j) → (∀ y, ∃! j, y ∈ orbit H (x j)) →
    (∀ j, closure (orbit H (x j)) ⊆ ⋃ l, ⋃ (_ : j ≤ l), orbit H (x l)) →
    ∀ D : (X → ℂ) →ₗ[ℂ] ℂ, (∀ h : H, ∀ f ∈ Cc X, D (transl h f) = χ h * D f) → ∀ f ∈ Cc X, D (f ∘ s) = D f

def Cells {G : Type} [Group G] [TopologicalSpace G] (B N : Subgroup G) (s : G → G) : Prop :=
  ∃ (k : ℕ) (w : Fin k → G), (∀ j, s (w j) = w j) ∧ (∀ g, ∃! j, g ∈ cell B N (w j)) ∧
    ∀ j, closure (cell B N (w j)) ⊆ ⋃ l, ⋃ (_ : j ≤ l), cell B N (w l)

example {G : Type} [Group G] [TopologicalSpace G] : Cells (⊤ : Subgroup G) ⊤ id := by
  have h : cell (⊤ : Subgroup G) ⊤ 1 = Set.univ := Set.eq_univ_of_forall fun g => ⟨g, trivial, 1, trivial, by simp⟩
  exact ⟨1, fun _ => 1, fun _ => rfl, fun g => ⟨0, by simp [h], fun _ _ => Subsingleton.elim _ _⟩,
    fun j => by simp [h, Set.iUnion_const, Subsingleton.elim j 0]⟩

def BiInv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] [SecondCountableTopology G] (B N : Subgroup G), IsClosed (B : Set G) → IsClosed (N : Set G) →
    ∀ (s : G →* G) (p : ℕ), 0 < p → Continuous s → (∀ g, s^[p] g = g) → (∀ b ∈ B, s b ∈ B) → (∀ u ∈ N, s u ∈ N) →
    Cells B N s → ∀ (η : B →* ℂ) (θ : N →* ℂˣ), (∃ L : Subgroup G, IsOpen (L : Set G) ∧ ∀ b : B, (b : G) ∈ L → η b = 1) →
    IsOpen (θ.ker : Set N) → (∀ b b' : B, (b' : G) = s b → η b' = η b) → (∀ u u' : N, (u' : G) = s u → θ u' = θ u) →
    ∀ D : (G → ℂ) →ₗ[ℂ] ℂ, (∀ b : B, ∀ f ∈ Cc G, D (fun x => f ((b : G)⁻¹ * x)) = η b * D f) →
    (∀ u : N, ∀ f ∈ Cc G, D (fun x => f (x * u)) = (θ u : ℂ) * D f) → ∀ f ∈ Cc G, D (f ∘ s) = D f

def PrMem : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] [SecondCountableTopology G] (B : Subgroup G), IsClosed (B : Set G) →
    ∀ [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [μ.IsHaarMeasure] (χ : B →* ℂˣ), IsOpen (χ.ker : Set B) →
    (∀ f ∈ Cc G, pr B μ χ f ∈ indF B χ) ∧ ∀ f ∈ Cc G, ∀ f' ∈ Cc G, pr B μ χ (f + f') = pr B μ χ f + pr B μ χ f'

def PrLeft : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] (B : Subgroup G), IsClosed (B : Set G) →
    ∀ [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [μ.IsHaarMeasure] (χ : B →* ℂˣ) (b : B),
    ∃ c : ℂ, ∀ (f : G → ℂ) (g : G), pr B μ χ (fun x => f ((b : G)⁻¹ * x)) g = c * pr B μ χ f g

def PrAuto : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] (B : Subgroup G), IsClosed (B : Set G) →
    ∀ [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [μ.IsHaarMeasure] (χ : B →* ℂˣ)
    (s : G →* G) (p : ℕ), 0 < p → Continuous s → (∀ g, s^[p] g = g) → (∀ b ∈ B, s b ∈ B) →
    (∀ b b' : B, (b' : G) = s b → χ b' = χ b) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ (f : G → ℂ) (g : G), pr B μ χ (f ∘ s) g = κ * pr B μ χ f (s g)

def PrSurj : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] (B : Subgroup G), IsClosed (B : Set G) →
    ∀ [MeasurableSpace B] [BorelSpace B] (μ : Measure B) [μ.IsHaarMeasure] (χ : B →* ℂˣ)
    (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ g, ∃ b ∈ B, ∃ k ∈ K, g = b * k) →
    ∀ φ ∈ indF B χ, ∃ f ∈ Cc G, pr B μ χ f = φ

def EtaEx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (B : Subgroup G) (s : G →* G) (p : ℕ), 0 < p → (∀ g, s^[p] g = g) →
    ∀ (P : (G → ℂ) → G → ℂ) (κ : ℝ), 0 < κ → (∀ f g, P (f ∘ s) g = κ * P f (s g)) →
    (∀ b : B, ∃ c : ℂ, ∀ f g, P (fun x => f ((b : G)⁻¹ * x)) g = c * P f g) → (∃ f ∈ Cc G, ∃ g, P f g ≠ 0) →
    κ = 1 ∧ ∃ η : B →* ℂ, (∀ (b : B) f g, P (fun x => f ((b : G)⁻¹ * x)) g = η b * P f g) ∧
      (∃ L : Subgroup G, IsOpen (L : Set G) ∧ ∀ b : B, (b : G) ∈ L → η b = 1) ∧ ∀ b b' : B, (b' : G) = s b → η b' = η b

def FunInv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] [SecondCountableTopology G] (B N : Subgroup G), IsClosed (B : Set G) → IsClosed (N : Set G) →
    ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ g, ∃ b ∈ B, ∃ k ∈ K, g = b * k) →
    ∀ (s : G →* G) (p : ℕ), 0 < p → Continuous s → (∀ g, s^[p] g = g) → (∀ b ∈ B, s b ∈ B) → (∀ u ∈ N, s u ∈ N) →
    Cells B N s → ∀ (χ : B →* ℂˣ) (θ : N →* ℂˣ), IsOpen (χ.ker : Set B) → IsOpen (θ.ker : Set N) →
    (∀ b b' : B, (b' : G) = s b → χ b' = χ b) → (∀ u u' : N, (u' : G) = s u → θ u' = θ u) →
    ∀ l : (G → ℂ) →ₗ[ℂ] ℂ, (∀ u : N, ∀ φ ∈ indF B χ, l (fun x => φ (x * u)) = (θ u : ℂ) * l φ) →
    ∀ φ ∈ indF B χ, l (φ ∘ s) = l φ

def GLCells : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E),
    Cells (borel E (Fin n)) (unipB E (Fin n)) (sg σ)

def GLFacts : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ),
    IsClosed (borel E (Fin n) : Set (GL (Fin n) E)) ∧ IsClosed (unipB E (Fin n) : Set (GL (Fin n) E)) ∧
    (∃ K : Subgroup (GL (Fin n) E), IsOpen (K : Set (GL (Fin n) E)) ∧ IsCompact (K : Set (GL (Fin n) E)) ∧
      ∀ g, ∃ b ∈ borel E (Fin n), ∃ k ∈ K, g = b * k) ∧
    (∀ ψ : AddChar E Circle, Continuous ψ → IsOpen ((whitChar ψ n).ker : Set (unipB E (Fin n)))) ∧
    ∀ (σ : E ≃+* E) (q : ℕ), Cyc σ q → Continuous (sg (n := n) σ) ∧ (∀ g : GL (Fin n) E, (sg σ)^[q] g = g) ∧
      (∀ b ∈ borel E (Fin n), sg σ b ∈ borel E (Fin n)) ∧
      ∀ ψ : AddChar E Circle, (∀ x, ψ (σ x) = ψ x) → ∀ u u' : unipB E (Fin n), (u' : GL (Fin n) E) = sg σ u →
        whitChar ψ n u' = whitChar ψ n u

def Core : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
    (σ : E ≃+* E) (q : ℕ), Cyc σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V),
    IsSmooth π → π.IsIrreducible → ∀ A : V →ₗ[ℂ] V, Semi σ π A → ∀ χ : borel E (Fin n) →* ℂˣ,
    (∀ b b' : borel E (Fin n), (b' : GL (Fin n) E) = sg σ b → χ b' = χ b) → ∀ (l : V →ₗ[ℂ] ℂ) (c : ℂ), l ≠ 0 →
    (∀ (b : borel E (Fin n)) (v : V), l (π b v) = (χ b : ℂ) * l v) → (∀ v, l (A v) = c * l v) →
      (A ≠ 0 → c ≠ 0) ∧ ∀ ψ : AddChar E Circle, Continuous ψ → (∀ x, ψ (σ x) = ψ x) →
        ∀ v, A v - c • v ∈ twKer π (unipB E (Fin n)) (whitChar ψ n)

def Eig : Prop :=
  ∀ (T J : Type) [CommGroup T] [AddCommGroup J] [Module ℂ J] [FiniteDimensional ℂ J] [Nontrivial J]
    (ρ : Representation ℂ T J) (s : T → T) (A : J →ₗ[ℂ] J), (∀ t y, A (ρ t y) = ρ (s t) (A y)) →
    (∀ μ : T →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) : Submodule ℂ J) ≠ ⊥ → ∀ t, μ (s t) = μ t) →
    ∃ (μ : T →* ℂˣ) (l : J →ₗ[ℂ] ℂ) (c : ℂ), l ≠ 0 ∧ (∀ t, μ (s t) = μ t) ∧ (∀ t y, l (ρ t y) = (μ t : ℂ) * l y) ∧
      ∀ y, l (A y) = c * l y

def EigZero : Prop :=
  ∀ (T J : Type) [CommGroup T] [AddCommGroup J] [Module ℂ J] [FiniteDimensional ℂ J] [Nontrivial J]
    (ρ : Representation ℂ T J), ∃ (μ : T →* ℂˣ) (l : J →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (μ t : ℂ) * l y) ∧
      (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) : Submodule ℂ J) ≠ ⊥

def JFacts : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V),
    π.IsIrreducible → ∀ ω : Fin n → Eˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) → IsSubquotient π (prinSeries ω) →
      IsSmooth π ∧ Nontrivial (Jacquet π (unipB E (Fin n))) ∧ FiniteDimensional ℂ (Jacquet π (unipB E (Fin n))) ∧
      ∀ μ : (Fin n → Eˣ) →* ℂˣ,
        (⨅ t, Module.End.maxGenEigenspace (jacB π t) (μ t : ℂ) : Submodule ℂ (Jacquet π (unipB E (Fin n)))) ≠ ⊥ →
          ∃ w : Equiv.Perm (Fin n), μ = torusChar (ω ∘ w)

def ToBorel : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
    (σ : E ≃+* E), Isom σ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V)
    (μ : (Fin n → Eˣ) →* ℂˣ), (∀ t, μ (fun i => Units.map (σ : E →* E) (t i)) = μ t) →
    ∀ l : Jacquet π (unipB E (Fin n)) →ₗ[ℂ] ℂ, (∀ t y, l (jacB π t y) = (μ t : ℂ) * l y) →
    ∃ χ : borel E (Fin n) →* ℂˣ, (∀ b b' : borel E (Fin n), (b' : GL (Fin n) E) = sg σ b → χ b' = χ b) ∧
      ∀ (b : borel E (Fin n)) (v : V), l (Submodule.Quotient.mk (π b v)) = (χ b : ℂ) * l (Submodule.Quotient.mk v)

def JacSemi : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ)
    (σ : E ≃+* E), Isom σ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V)
    (A : V →ₗ[ℂ] V) (hA : Semi σ π A) (t : Fin n → Eˣ) (y : Jacquet π (unipB E (Fin n))),
    jacA hA (jacB π t y) = jacB π (fun i => Units.map (σ : E →* E) (t i)) (jacA hA y)

def TracePow : Prop :=
  ∀ (J : Type) [AddCommGroup J] [Module ℂ J] [FiniteDimensional ℂ J] [Nontrivial J] (φ : J →ₗ[ℂ] J),
    Function.Injective φ → ∀ k₀ : ℕ, ∃ k ≥ k₀, LinearMap.trace ℂ J (φ ^ k) ≠ 0

end UpperTheory.Gal.LocD

end
