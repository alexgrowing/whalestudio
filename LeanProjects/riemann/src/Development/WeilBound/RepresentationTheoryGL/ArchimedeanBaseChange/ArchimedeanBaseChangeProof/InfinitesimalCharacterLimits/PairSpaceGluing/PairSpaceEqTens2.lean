import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Glue

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_eq_tens2 (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ = tens2 U₁ U₂ := rfl

end Pair

def TensMap1 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (U₁ U₁' : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (T : Sm E a →ₗ[ℂ] Sm E a),
  IsStable U₁ → IsStable U₂ → (∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ)) →
  (∀ F ∈ pairSpace U₁ U₂, ∀ (ψ : Sm E a) (m₂ : GA E b), ψ.1 = (fun x => F (x, m₂)) →
      (fun x => InducedTensorMap.tensOp T LinearMap.id F (x, m₂)) = (T ψ).1) ∧
  ((∀ ψ ∈ U₁, T ψ ∈ U₁') → ∀ F ∈ pairSpace U₁ U₂, InducedTensorMap.tensOp T LinearMap.id F ∈ pairSpace U₁' U₂) ∧
  ((∀ ψ ∈ U₁, T ψ = 0 → ψ = 0) → ∀ F ∈ pairSpace U₁ U₂, InducedTensorMap.tensOp T LinearMap.id F = 0 → F = 0) ∧
  (∀ (ι : Type) [Fintype ι] (F : ι → H E a b → ℂ), (∀ i, F i ∈ pairSpace U₁ U₂) → ∀ h : HeckeM E a b ι,
    heckeAct h (fun i => InducedTensorMap.tensOp T LinearMap.id (F i)) =
      (fun i => InducedTensorMap.tensOp T LinearMap.id (heckeAct h F i)) ∧
    ∀ c : ℂ, heckeAct h F = c • F →
      heckeAct h (fun i => InducedTensorMap.tensOp T LinearMap.id (F i)) = c • fun i => InducedTensorMap.tensOp T LinearMap.id (F i)) ∧
  (∀ (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ))
    (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ →
    ∀ F ∈ pairSpace U₁ U₂, TypeH K₁ K₂ W₁ W₂ F → TypeH K₁ K₂ W₁ W₂ (InducedTensorMap.tensOp T LinearMap.id F)) ∧
  (∀ (ι : Type) (F : ι → H E a b → ℂ), (∀ i, F i ∈ pairSpace U₁ U₂) → (∃ ψ ∈ slices₁ F, T ψ ≠ 0) →
    (fun i => InducedTensorMap.tensOp T LinearMap.id (F i)) ≠ 0)

def TensMap2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (U₁ : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (T : Sm E b →ₗ[ℂ] Sm E b),
  IsStable U₁ → IsStable U₂ → (∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) →
  (∀ F ∈ pairSpace U₁ U₂, ∀ (ψ : Sm E b) (m₁ : GA E a), ψ.1 = (fun y => F (m₁, y)) →
      (fun y => InducedTensorMap.tensOp LinearMap.id T F (m₁, y)) = (T ψ).1) ∧
  ((∀ ψ ∈ U₂, T ψ ∈ U₂') → ∀ F ∈ pairSpace U₁ U₂, InducedTensorMap.tensOp LinearMap.id T F ∈ pairSpace U₁ U₂') ∧
  ((∀ ψ ∈ U₂, T ψ = 0 → ψ = 0) → ∀ F ∈ pairSpace U₁ U₂, InducedTensorMap.tensOp LinearMap.id T F = 0 → F = 0) ∧
  (∀ (ι : Type) [Fintype ι] (F : ι → H E a b → ℂ), (∀ i, F i ∈ pairSpace U₁ U₂) → ∀ h : HeckeM E a b ι,
    heckeAct h (fun i => InducedTensorMap.tensOp LinearMap.id T (F i)) =
      (fun i => InducedTensorMap.tensOp LinearMap.id T (heckeAct h F i)) ∧
    ∀ c : ℂ, heckeAct h F = c • F →
      heckeAct h (fun i => InducedTensorMap.tensOp LinearMap.id T (F i)) = c • fun i => InducedTensorMap.tensOp LinearMap.id T (F i)) ∧
  (∀ (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ))
    (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ →
    ∀ F ∈ pairSpace U₁ U₂, TypeH K₁ K₂ W₁ W₂ F → TypeH K₁ K₂ W₁ W₂ (InducedTensorMap.tensOp LinearMap.id T F)) ∧
  (∀ (ι : Type) (F : ι → H E a b → ℂ), (∀ i, F i ∈ pairSpace U₁ U₂) → (∃ ψ ∈ slices₂ F, T ψ ≠ 0) →
    (fun i => InducedTensorMap.tensOp LinearMap.id T (F i)) ≠ 0)

def HullFacts : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (S : Set (Sm E N)),
  IsStable (hull S) ∧ S ⊆ (hull S : Set (Sm E N)) ∧
    ∀ U' : Submodule ℂ (Sm E N), IsStable U' → S ⊆ (U' : Set (Sm E N)) → hull S ≤ U'

def SliceFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (F : ι → H E a b → ℂ) (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b))
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ))
  (W₂ : Submodule ℂ (Kinf E b → ℂ)),
  (∀ i, F i ∈ pairSpace U₁ U₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (F i)) →
  ((∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => F i (x, m₂)) ∧ (∀ i m₁, ∃ φ : Sm E b, φ.1 = fun y => F i (m₁, y)) ∧
    slices₁ F ⊆ (U₁ : Set (Sm E a)) ∧ slices₂ F ⊆ (U₂ : Set (Sm E b)) ∧
    (∀ φ ∈ slices₁ F, TypeB K₁ W₁ φ) ∧ (∀ φ ∈ slices₂ F, TypeB K₂ W₂ φ)) ∧
  (∃ S : Finset (Sm E a), (↑S : Set (Sm E a)) ⊆ slices₁ F ∧
    ∀ U' : Submodule ℂ (Sm E a), IsStable U' → (↑S : Set (Sm E a)) ⊆ U' → hull (slices₁ F) ≤ U') ∧
  (∃ S : Finset (Sm E b), (↑S : Set (Sm E b)) ⊆ slices₂ F ∧
    ∀ U' : Submodule ℂ (Sm E b), IsStable U' → (↑S : Set (Sm E b)) ⊆ U' → hull (slices₂ F) ≤ U') ∧
  (∀ i, F i ∈ pairSpace U₁ (hull (slices₂ F))) ∧ (∀ i, F i ∈ pairSpace (hull (slices₁ F)) U₂)

def TypeEquiv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (U : Submodule ℂ (Sm E N))
  (T : Sm E N →ₗ[ℂ] Sm E N) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)),
  FiniteDimensional ℂ W → IsStable U → (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) →
  ∀ φ ∈ U, TypeB K W φ → TypeB K W (T φ)

def KerStable : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (U : Submodule ℂ (Sm E N))
  (S : Set (Sm E N)) (T : Sm E N →ₗ[ℂ] Sm E N), IsStable U → S ⊆ (U : Set (Sm E N)) →
  (∀ U' : Submodule ℂ (Sm E N), IsStable U' → S ⊆ (U' : Set (Sm E N)) → U ≤ U') →
  (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) → (∃ ψ ∈ U, T ψ ≠ 0) → ∃ ψ ∈ S, T ψ ≠ 0

inductive Shape : ℕ → Type
  | leaf (N : ℕ) : Shape N
  | node {r s : ℕ} : Shape r → Shape s → Shape (r + s)

def Shape.Pos : {N : ℕ} → Shape N → Prop
  | N, .leaf _ => 0 < N
  | _, .node σ₁ σ₂ => σ₁.Pos ∧ σ₂.Pos

def trShape {E : Type} [Field E] [NumberField E] [IsCMField E] : {N : ℕ} → Tr E N → Shape N
  | N, .leaf _ _ => .leaf N
  | _, .node t₁ t₂ => .node (trShape t₁) (trShape t₂)

theorem shape_pos_one : (Shape.leaf 1).Pos := Nat.one_pos

def ShapeSub : Prop := (∀ N : ℕ, {σ : Shape N | σ.Pos}.Finite) ∧
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N),
    (∀ k, (t k).AllLeaves fun M _ => 0 < M) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, trShape (t (φ k)) = trShape (t (φ 0))

def LeafBdd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (B : ℝ), ∃ R : ℝ,
  ∀ (t : Tr E N) (U : Submodule ℂ (Sm E N)) (T : Sm E N →ₗ[ℂ] Sm E N) (m : (E →+* ℂ) → Multiset ℂ),
  t.Good → (t.AllLeaves fun M _ => 0 < M) → IsStable U → (∀ τ, HasInfCharGL U τ (m τ)) →
  (∀ τ, ∀ x ∈ m τ, ‖x‖ ≤ B) → (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) → (∀ ψ ∈ U, T ψ ∈ t.space) →
  (∃ ψ ∈ U, T ψ ≠ 0) →
  t.AllLeaves (fun _ V => InfBdd R V) ∧ ∀ z ∈ t.twists, ‖z‖ ≤ R

def LeafLim : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (Ω' : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))), KTypes E Ω' →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ω ∧
  ∀ Θ' : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θ' →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θ ∧
  (∀ (M : ℕ) [MeasurableSpace (GA E M)] [BorelSpace (GA E M)] (ν : Measure (GA E M)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin M) (Af E))) (W' : Submodule ℂ (Kinf E M → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin M) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R') →
  ∀ (R : ℝ) (t : ℕ → Tr E N), (∀ k, (t k).Good) →
    (∀ k, (t k).AllLeaves fun M V => 0 < M ∧ (∃ K' ∈ Θ' M, ∃ W' ∈ Ω' M, HasType K' W' V) ∧ InfBdd R V) →
    (∀ k, ∀ z ∈ (t k).twists, ‖z‖ ≤ R) →
    ∃ (φ : ℕ → ℕ) (s : ℕ → Tr E N) (s₀ : Tr E N), StrictMono φ ∧ s₀.Good ∧ (∀ k, (s k).Disc) ∧
      (∀ k, (s k).strip = s₀.strip) ∧
      s₀.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
      (∀ i, Tendsto (fun k => (s k).twists.getD i 0) atTop (𝓝 (s₀.twists.getD i 0))) ∧
      ∀ k, Emb (t (φ k)).space (· ∈ (s k).space)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Glue

end
