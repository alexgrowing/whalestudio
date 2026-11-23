import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.NoAccum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def untwDet {N : ℕ} (z : ℂ) (χ : Sm E N) : Sm E N := mulChi N (Model.absC E (-z)) χ

def LeafFormS {N : ℕ} (U : Submodule ℂ (Sm E N)) (t : Tr E N) : Prop :=
  0 < N → ∀ (V' : Submodule ℂ (Sm E N)) (z' : ℂ), t = .leaf V' z' →
    ∃ (V : Submodule ℂ (Sm E N)) (z : ℂ), IsDiscrete V ∧ Emb (tw V z) (· ∈ tw V' z') ∧
      (∀ χ ∈ U, ∀ (s : ℝ) g, (untwDet z χ).1 (splitCentre E N s * g) = (untwDet z χ).1 g) ∧
      ∃ χ ∈ U, ∃ v ∈ V, Cz.Leaf2Aux.pr (untwDet z χ).1 v.1 ≠ 0

end Defs

def LimAtS (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (W₁ : Submodule ℂ (Kinf E a → ℂ))
    (W₂ : Submodule ℂ (Kinf E b → ℂ)) (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ (D : Dom E a b) (ι : Type) [Fintype ι] (M : ℕ)
  (m₁ : ℕ → (E →+* ℂ) → Multiset ℂ) (m₂ : ℕ → (E →+* ℂ) → Multiset ℂ) (n₁ n₂ : (E →+* ℂ) → Multiset ℂ)
  (C : Set (HeckeM E a b ι)) (lam : ℕ → HeckeM E a b ι → ℂ) (lam₀ : HeckeM E a b ι → ℂ)
  (f : ℕ → ι → H E a b → ℂ), C.Countable →
  (∀ (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin N) (Af E))) (W' : Submodule ℂ (Kinf E N → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R') →
  (∀ k i, Continuous (f k i)) → (∀ k, f k ≠ 0) → (∀ k, LeftInv (f k)) → (∀ k, WL2 D M (f k)) →
  (∀ k i, TypeH K₁ K₂ W₁ W₂ (f k i)) →
  (∀ k i (m₂ : GA E b), ∃ φ : Sm E a, φ.1 = fun x => f k i (x, m₂)) →
  (∀ k i (m₁ : GA E a), ∃ φ : Sm E b, φ.1 = fun x => f k i (m₁, x)) →
  (∀ k, ∀ φ ∈ slices₁ (f k), IsAutForm φ) → (∀ k, ∀ φ ∈ slices₂ (f k), IsAutForm φ) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₁ (f k))) τ (m₁ k τ)) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₂ (f k))) τ (m₂ k τ)) →
  (∀ k, ∀ h ∈ C, heckeAct h (f k) = lam k h • f k) →
  (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, MClose ε (m₁ k τ) (n₁ τ) ∧ MClose ε (m₂ k τ) (n₂ τ)) →
  RealSym n₁ → RealSym n₂ → (∀ τ, GapM (n₁ τ) ∧ GapM (n₂ τ)) →
  (∀ h ∈ C, Tendsto (fun k => lam k h) atTop (𝓝 (lam₀ h))) →
  ∃ (s₁ : Tr E a) (s₂ : Tr E b) (F : ι → H E a b → ℂ) (ψ : ℕ → ℕ) (t₁ : ℕ → Tr E a) (t₂ : ℕ → Tr E b)
    (T₁ : ℕ → Sm E a →ₗ[ℂ] Sm E a) (T₂ : ℕ → Sm E b →ₗ[ℂ] Sm E b),
    s₁.Good ∧ s₂.Good ∧ s₁.Untw ∧ s₂.Untw ∧
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₁ M, ∃ W' ∈ Ω₁ M, HasType K' W' V) ∧
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₂ M, ∃ W' ∈ Ω₂ M, HasType K' W' V) ∧
    (∀ τ, HasInfCharGL s₁.space τ (n₁ τ)) ∧ (∀ τ, HasInfCharGL s₂.space τ (n₂ τ)) ∧
    F ≠ 0 ∧ (∀ i, F i ∈ pairSpace s₁.space s₂.space) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (F i)) ∧
    (∀ h ∈ C, heckeAct h F = lam₀ h • F) ∧
    GlobalTheory.CompanionTheory.EGlue.Red s₁ ∧ GlobalTheory.CompanionTheory.EGlue.Red s₂ ∧ StrictMono ψ ∧
    (∀ k, (t₁ k).Disc) ∧ (∀ k, (t₂ k).Disc) ∧ (∀ k, (t₁ k).strip = s₁.strip) ∧ (∀ k, (t₂ k).strip = s₂.strip) ∧
    (∀ i, Tendsto (fun k => ((t₁ k).twists.getD i 0)) atTop (𝓝 (s₁.twists.getD i 0))) ∧
    (∀ i, Tendsto (fun k => ((t₂ k).twists.getD i 0)) atTop (𝓝 (s₂.twists.getD i 0))) ∧
    (∀ k o, ∀ χ ∈ hull (slices₁ (f (ψ k))), T₁ k (act o χ) = act o (T₁ k χ)) ∧
    (∀ k o, ∀ χ ∈ hull (slices₂ (f (ψ k))), T₂ k (act o χ) = act o (T₂ k χ)) ∧
    (∀ k, ∀ χ ∈ hull (slices₁ (f (ψ k))), T₁ k χ ∈ (t₁ k).space) ∧
    (∀ k, ∀ χ ∈ hull (slices₂ (f (ψ k))), T₂ k χ ∈ (t₂ k).space) ∧
    (∀ k, ∃ χ ∈ hull (slices₁ (f (ψ k))), T₁ k χ ≠ 0) ∧ (∀ k, ∃ χ ∈ hull (slices₂ (f (ψ k))), T₂ k χ ≠ 0) ∧
    (∀ k, LeafFormS (hull (slices₁ (f (ψ k)))) (t₁ k)) ∧ (∀ k, LeafFormS (hull (slices₂ (f (ψ k)))) (t₂ k))

def EFinalS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ →
  ∃ (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))), KTypes E Ω₁ ∧ KTypes E Ω₂ ∧
  ∀ (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))),
  IsOpen (K₁ : Set (GL (Fin a) (Af E))) → IsOpen (K₂ : Set (GL (Fin b) (Af E))) →
  ∃ (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))), Levels E Θ₁ ∧ Levels E Θ₂ ∧
    LimAtS E a b W₁ W₂ Ω₁ Ω₂ K₁ K₂ Θ₁ Θ₂

def NoAccumulationSplitSliceLimit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (hb : b = 0) (Pi : Submodule ℂ (Sm E a))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))),
  KTypes E Ω₁ → KTypes E Ω₂ → Levels E Θ₁ → Levels E Θ₂ → LimAtS E a b W₁ W₂ Ω₁ Ω₂ K₁ K₂ Θ₁ Θ₂ →
  ∀ (D : Dom E a b) (ι : Type) [Fintype ι] (M : ℕ)
  (m₁ : ℕ → (E →+* ℂ) → Multiset ℂ) (m₂ : ℕ → (E →+* ℂ) → Multiset ℂ) (n₁ n₂ : (E →+* ℂ) → Multiset ℂ)
  (C : Set (HeckeM E a b ι)) (lam : ℕ → HeckeM E a b ι → ℂ) (lam₀ : HeckeM E a b ι → ℂ)
  (f : ℕ → ι → H E a b → ℂ), C.Countable →
  IsOpen (K₁ : Set (GL (Fin a) (Af E))) → IsOpen (K₂ : Set (GL (Fin b) (Af E))) →
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ →
  (∀ (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin N) (Af E))) (W' : Submodule ℂ (Kinf E N → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R') →
  (∀ k i, Continuous (f k i)) → (∀ k, f k ≠ 0) → (∀ k, LeftInv (f k)) → (∀ k, WL2 D M (f k)) →
  (∀ k i, TypeH K₁ K₂ W₁ W₂ (f k i)) →
  (∀ k i (y : GA E b), ∃ φ : Sm E a, φ.1 = fun x => f k i (x, y)) →
  (∀ k i (x : GA E a), ∃ φ : Sm E b, φ.1 = fun y => f k i (x, y)) →
  (∀ k, ∀ φ ∈ slices₁ (f k), IsAutForm φ) → (∀ k, ∀ φ ∈ slices₂ (f k), IsAutForm φ) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₁ (f k))) τ (m₁ k τ)) →
  (∀ k τ, HasInfCharGL (Submodule.span ℂ (slices₂ (f k))) τ (m₂ k τ)) →
  (∀ k, ∀ h ∈ C, heckeAct h (f k) = lam k h • f k) →
  (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, MClose ε (m₁ k τ) (n₁ τ) ∧ MClose ε (m₂ k τ) (n₂ τ)) →
  RealSym n₁ → RealSym n₂ → (∀ τ, GapM (n₁ τ) ∧ GapM (n₂ τ)) →
  (∀ h ∈ C, Tendsto (fun k => lam k h) atTop (𝓝 (lam₀ h))) →
  IsCuspD Pi →
  (∀ (s₁ : Tr E a) (s₂ : Tr E b) (F : ι → H E a b → ℂ), s₁.Good → s₂.Good → s₁.Untw → s₂.Untw →
    s₁.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₁ M, ∃ W' ∈ Ω₁ M, HasType K' W' V) →
    s₂.AllLeaves (fun M V => M = 0 ∨ ∃ K' ∈ Θ₂ M, ∃ W' ∈ Ω₂ M, HasType K' W' V) →
    (∀ τ, HasInfCharGL s₁.space τ (n₁ τ)) → (∀ τ, HasInfCharGL s₂.space τ (n₂ τ)) →
    F ≠ 0 → (∀ i, F i ∈ pairSpace s₁.space s₂.space) → (∀ i, TypeH K₁ K₂ W₁ W₂ (F i)) →
    (∀ h ∈ C, heckeAct h F = lam₀ h • F) → s₁.space ≤ Pi) →
  (∀ k, OrthPackets D Pi (f k)) →
  False

end PositivityTheory.Rg.BcB.SpectralAccumulation

end
