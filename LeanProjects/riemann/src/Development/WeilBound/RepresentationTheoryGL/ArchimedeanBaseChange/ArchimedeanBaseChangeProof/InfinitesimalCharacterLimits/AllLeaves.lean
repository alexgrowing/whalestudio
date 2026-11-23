import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def GapM (m : Multiset ℂ) : Prop := m.Nodup ∧ ∀ x ∈ m, ∀ y ∈ m, x ≠ y → (1 / 2 : ℝ) ≤ ‖x - y‖

def NonPos (U : Submodule ℂ (Sm E N)) : Prop :=
  ∀ φ ∈ U, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c ≤ 0

def CentIm (U : Submodule ℂ (Sm E N)) : Prop :=
  ∃ z : ℂ, z.re = 0 ∧ ∀ φ ∈ U, ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = Complex.exp (z * t) * φ.1 g

variable (E) in

inductive Tr : ℕ → Type
  | leaf {N : ℕ} (V : Submodule ℂ (Sm E N)) (z : ℂ) : Tr N
  | node {r s : ℕ} (t₁ : Tr r) (t₂ : Tr s) : Tr (r + s)

def Tr.space : {N : ℕ} → Tr E N → Submodule ℂ (Sm E N)
  | _, .leaf V z => tw V z
  | _, @Tr.node _ _ _ _ r s t₁ t₂ =>
    Submodule.span ℂ {φ | MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) φ ∧
      φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))}

def Tr.Good : {N : ℕ} → Tr E N → Prop
  | M, .leaf V z => (M = 0 ∧ V = ⊤ ∧ z = 0) ∨ (0 < M ∧ IsDiscrete V ∧ z.re = 0)
  | _, .node t₁ t₂ => t₁.Good ∧ t₂.Good

def Tr.Disc : {N : ℕ} → Tr E N → Prop
  | M, .leaf V z => (M = 0 ∧ V = ⊤ ∧ z = 0) ∨ (0 < M ∧ IsDiscrete V)
  | _, .node t₁ t₂ => t₁.Disc ∧ t₂.Disc

def Tr.twists : {N : ℕ} → Tr E N → List ℂ
  | _, .leaf _ z => [z]
  | _, .node t₁ t₂ => t₁.twists ++ t₂.twists

def Tr.strip : {N : ℕ} → Tr E N → Tr E N
  | _, .leaf V _ => .leaf V 0
  | _, .node t₁ t₂ => .node t₁.strip t₂.strip

def TypeB (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (φ : Sm E N) : Prop :=
  (∀ u ∈ K, ∀ g, φ.1 (g * finGL E N u) = φ.1 g) ∧
    ∀ g, (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W

def HasType (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∃ φ ∈ V, φ ≠ 0 ∧ TypeB K W φ

def IsoV (V V' : Submodule ℂ (Sm E N)) : Prop :=
  ∃ T : V ≃ₗ[ℂ] V', ∀ (o : Op E N) (φ ψ : V), ψ.1 = act o φ.1 → (T ψ).1 = act o (T φ).1

def InfBdd (R : ℝ) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL V τ m ∧ ∀ x ∈ m, ‖x‖ ≤ R

def Repro [MeasurableSpace (GA E N)] (μ : Measure (GA E N)) (K : Subgroup (GL (Fin N) (Af E)))
    (W : Submodule ℂ (Kinf E N → ℂ)) (R : ℝ) : Prop :=
  ∃ (α : GA E N → ℂ) (δ : ℝ), Continuous α ∧ HasCompactSupport α ∧ 0 < δ ∧
    ∀ φ : Sm E N, IsAutForm φ → TypeB K W φ → InfBdd R (Submodule.span ℂ {φ}) →
      ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * φ.1 (x * y) ∂μ = s * φ.1 x

end Lin

def Tr.AllLeaves {E : Type} [Field E] [NumberField E] [IsCMField E] (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    {N : ℕ} → Tr E N → Prop
  | M, .leaf V _ => P M V
  | _, .node t₁ t₂ => t₁.AllLeaves P ∧ t₂.AllLeaves P

def KTypes (E : Type) [Field E] [NumberField E] [IsCMField E] (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) :
    Prop :=
  ∀ M, (Ω M).Finite ∧ ∀ W' ∈ Ω M, FiniteDimensional ℂ W'

def Levels (E : Type) [Field E] [NumberField E] [IsCMField E] (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) :
    Prop :=
  ∀ M, (Θ M).Finite ∧ ∀ K' ∈ Θ M, IsOpen (K' : Set (GL (Fin M) (Af E)))

def Sep4 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (W : Submodule ℂ (Kinf E N → ℂ)), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), (∀ M, (Ω M).Finite ∧ ∀ W' ∈ Ω M, FiniteDimensional ℂ W') ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))),
    (∀ M, (Θ M).Finite ∧ ∀ K' ∈ Θ M, IsOpen (K' : Set (GL (Fin M) (Af E)))) ∧
    ∀ (U : Submodule ℂ (Sm E N)), 0 < N → IsStable U → (∀ φ ∈ U, IsAutForm φ) →
      (∃ S : Finset (Sm E N), (∀ φ ∈ S, TypeB K W φ) ∧ ↑S ⊆ (U : Set (Sm E N)) ∧
        ∀ U' : Submodule ℂ (Sm E N), IsStable U' → ↑S ⊆ (U' : Set (Sm E N)) → U ≤ U') →
      NonPos U → CentIm U → (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL U τ m ∧ m.Nodup) → U ≠ ⊥ →
      ∃ (t : Tr E N) (T : Sm E N →ₗ[ℂ] Sm E N), t.Good ∧
        t.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
        (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) ∧ (∀ ψ ∈ U, T ψ ∈ t.space) ∧ ∃ ψ ∈ U, T ψ ≠ 0

def FinDisc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) (R ε : ℝ), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → 0 < ε →
  Repro μ K W R →
  ∃ V₀ : Finset (Submodule ℂ (Sm E N)), ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → HasType K W V → InfBdd R V →
    (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) → ∃ V' ∈ V₀, IsoV V V'

def Lim5 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (W : Submodule ℂ (Kinf E N → ℂ)), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ω ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θ ∧
  ∀ [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (R : ℝ), 0 < N →
  (∀ (M : ℕ) [MeasurableSpace (GA E M)] [BorelSpace (GA E M)] (ν : Measure (GA E M)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin M) (Af E))) (W' : Submodule ℂ (Kinf E M → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin M) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R') →
  ∀ V : ℕ → Submodule ℂ (Sm E N), (∀ k, IsDiscrete (V k)) → (∀ k, HasType K W (V k)) → (∀ k, InfBdd R (V k)) →
  ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E N) (t₀ : Tr E N), StrictMono φ ∧ t₀.Good ∧ (∀ k, (t k).Disc) ∧
    (∀ k, (t k).strip = t₀.strip) ∧
    t₀.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (t₀.twists.getD i 0))) ∧
    ∀ k, Emb (V (φ k)) (· ∈ (t k).space)

def Tr.shift {E : Type} [Field E] [NumberField E] [IsCMField E] (z : ℂ) : {N : ℕ} → Tr E N → Tr E N
  | _, .leaf V z' => .leaf V (z' + z)
  | _, .node t₁ t₂ => .node (t₁.shift z) (t₂.shift z)

def TrStable : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N),
  (t.AllLeaves fun _ V => IsStable V) → IsStable t.space

def TwShift : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N))
  (t : Tr E N) (z : ℂ), IsStable V → Emb V (· ∈ t.space) → Emb (tw V z) (· ∈ (t.shift z).space)

def Graft : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (t₁ t₁' : Tr E r) (t₂ t₂' : Tr E s),
  IsStable t₁.space → IsStable t₁'.space → IsStable t₂.space → IsStable t₂'.space →
  Emb t₁.space (· ∈ t₁'.space) → Emb t₂.space (· ∈ t₂'.space) →
  Emb (Tr.node t₁ t₂).space (· ∈ (Tr.node t₁' t₂').space)

section Pair

open PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

abbrev Hf (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Type :=
  GL (Fin a) (Af E) × GL (Fin b) (Af E)

def finH (g : Hf E a b) : H E a b := (finGL E a g.1, finGL E b g.2)

abbrev HeckeM (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) : Type :=
  Matrix ι ι (Hf E a b →₀ ℂ)

def heckeAct {ι : Type} [Fintype ι] (h : HeckeM E a b ι) (f : ι → H E a b → ℂ) : ι → H E a b → ℂ :=
  fun i x => ∑ j, (h i j).sum fun g c => c * f j (x * finH g)

def pairSpace (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) : Submodule ℂ (H E a b → ℂ) :=
  Submodule.span ℂ {F | ∃ φ₁ ∈ U₁, ∃ φ₂ ∈ U₂, F = fun x => φ₁.1 x.1 * φ₂.1 x.2}

def TypeH (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ) : Prop :=
  (∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ x, F (x * (finGL E a u₁, finGL E b u₂)) = F x) ∧
    ∀ x, (fun k : Kinf E a × Kinf E b => F (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) ∈
      Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}

def AdmDisc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (K' : Subgroup (GL (Fin M) (Af E)))
  (W' : Submodule ℂ (Kinf E M → ℂ)), IsOpen (K' : Set (GL (Fin M) (Af E))) → FiniteDimensional ℂ W' →
  ∀ V : Submodule ℂ (Sm E M), IsDiscrete V → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ V ∧ TypeB K' W' φ})

def LimVec : Prop := AdmDisc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (t₁ : ℕ → Tr E a) (t₂ : ℕ → Tr E b) (s₁ : Tr E a) (s₂ : Tr E b) (K₁ : Subgroup (GL (Fin a) (Af E)))
  (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (C : Set (HeckeM E a b ι)) (lam : ℕ → HeckeM E a b ι → ℂ) (lam₀ : HeckeM E a b ι → ℂ) (f : ℕ → ι → H E a b → ℂ),
  IsOpen (K₁ : Set (GL (Fin a) (Af E))) → IsOpen (K₂ : Set (GL (Fin b) (Af E))) → FiniteDimensional ℂ W₁ →
  FiniteDimensional ℂ W₂ → C.Countable → s₁.Good → s₂.Good → (∀ k, (t₁ k).Disc) → (∀ k, (t₂ k).Disc) →
  (∀ k, (t₁ k).strip = s₁.strip) → (∀ k, (t₂ k).strip = s₂.strip) →
  (∀ i, Tendsto (fun k => ((t₁ k).twists.getD i 0)) atTop (𝓝 (s₁.twists.getD i 0))) →
  (∀ i, Tendsto (fun k => ((t₂ k).twists.getD i 0)) atTop (𝓝 (s₂.twists.getD i 0))) →
  (∀ k, f k ≠ 0) → (∀ k i, f k i ∈ pairSpace (t₁ k).space (t₂ k).space) →
  (∀ k i, TypeH K₁ K₂ W₁ W₂ (f k i)) → (∀ k, ∀ h ∈ C, heckeAct h (f k) = lam k h • f k) →
  (∀ h ∈ C, Tendsto (fun k => lam k h) atTop (𝓝 (lam₀ h))) →
  ∃ F : ι → H E a b → ℂ, F ≠ 0 ∧ (∀ i, F i ∈ pairSpace s₁.space s₂.space) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (F i)) ∧
    ∀ h ∈ C, heckeAct h F = lam₀ h • F

end Pair

end PositivityTheory.Rg.BcB.SpectralAccumulation

end
