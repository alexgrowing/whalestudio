import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def Red : {N : ℕ} → Tr E N → Prop
  | _, .leaf _ _ => True
  | _, @Tr.node _ _ _ _ r s t₁ t₂ => 0 < r ∧ 0 < s ∧ Red t₁ ∧ Red t₂

inductive Conv : {N : ℕ} → (ℕ → Tr E N) → Tr E N → Prop
  | leaf {N : ℕ} (V : Submodule ℂ (Sm E N)) (z : ℕ → ℂ) (z₀ : ℂ) (h : Tendsto z atTop (𝓝 z₀)) :
      Conv (fun k => .leaf V (z k)) (.leaf V z₀)
  | node {r s : ℕ} {t₁ : ℕ → Tr E r} {t₂ : ℕ → Tr E s} {s₁ : Tr E r} {s₂ : Tr E s} (h₁ : Conv t₁ s₁) (h₂ : Conv t₂ s₂) :
      Conv (fun k => .node (t₁ k) (t₂ k)) (.node s₁ s₂)

noncomputable def LeafZ (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → ℂ → Prop) : {N : ℕ} → Tr E N → Prop
  | M, .leaf V z => P M V z
  | _, .node t₁ t₂ => LeafZ P t₁ ∧ LeafZ P t₂

variable {a b : ℕ}

def sl₁ (F : H E a b → ℂ) (m₂ : GA E b) : Sm E a :=
  open Classical in if h : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂) then h.choose else 0

def sl₂ (F : H E a b → ℂ) (m₁ : GA E a) : Sm E b :=
  open Classical in if h : ∃ φ : Sm E b, φ.1 = fun x => F (m₁, x) then h.choose else 0

def ap₁ (A : Sm E a →ₗ[ℂ] Sm E a) (F : H E a b → ℂ) : H E a b → ℂ := fun x => (A (sl₁ F x.2)).1 x.1

def ap₂ (B : Sm E b →ₗ[ℂ] Sm E b) (F : H E a b → ℂ) : H E a b → ℂ := fun x => (B (sl₂ F x.1)).1 x.2

theorem good_disc : ∀ {N : ℕ} {t : Tr E N}, t.Good → t.Disc := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1⟩
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem disc_stable : ∀ {N : ℕ} {t : Tr E N}, t.Disc → t.AllLeaves fun _ V => IsStable V := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with ⟨-, rfl, -⟩ | h
    · exact fun _ _ _ => trivial
    · exact h.2.stable
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem rank_pos_of_leaves {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} : ∀ {N : ℕ} {t : Tr E N},
    t.AllLeaves (fun M V => 0 < M ∧ Q M V) → 0 < N := by
  intro N t
  induction t with
  | leaf V z => exact fun h => h.1
  | node t₁ t₂ i₁ i₂ => exact fun h => Nat.add_pos_left (i₁ h.1) _

theorem red_of_leaves {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} : ∀ {N : ℕ} {t : Tr E N},
    t.AllLeaves (fun M V => 0 < M ∧ Q M V) → Red t := by
  intro N t
  induction t with
  | leaf V z => exact fun _ => trivial
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨rank_pos_of_leaves h.1, rank_pos_of_leaves h.2, i₁ h.1, i₂ h.2⟩

section Props

def ListLeaf (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) :
    ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop :=
  fun M V => M = 0 ∨ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V

def CapEig {N : ℕ} (ψ : Sm E N) (m : (E →+* ℂ) → Multiset ℂ) : Prop :=
  ∀ τ u, cap τ u ψ = ((m τ).map (u + ·)).prod • ψ

def FinGen {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (U : Submodule ℂ (Sm E N)) : Prop :=
  ∃ S : Finset (Sm E N), (∀ φ ∈ S, TypeB K W φ) ∧ ↑S ⊆ (U : Set (Sm E N)) ∧
    ∀ U' : Submodule ℂ (Sm E N), IsStable U' → ↑S ⊆ (U' : Set (Sm E N)) → U ≤ U'

def Fac {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) : Prop :=
  ∀ U : Submodule ℂ (Sm E N), IsStable U → (∀ φ ∈ U, IsAutForm φ) → FinGen K W U → NonPos U → CentIm U →
    (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL U τ m ∧ m.Nodup) → U ≠ ⊥ →
    ∃ (t : Tr E N) (T : Sm E N →ₗ[ℂ] Sm E N), Red t ∧ t.Good ∧ t.AllLeaves (ListLeaf Θ Ω) ∧
      (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) ∧ (∀ ψ ∈ U, T ψ ∈ t.space) ∧ ∃ ψ ∈ U, T ψ ≠ 0

def ReproAll (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin N) (Af E))) (W' : Submodule ℂ (Kinf E N → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R'

def LimLeafP (N : ℕ) (Θs : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) : Prop :=
  ∀ M, 0 < M → M ≤ N → ∀ (V : ℕ → Submodule ℂ (Sm E M)) (z : ℕ → ℂ) (R : ℝ), ReproAll E →
    (∀ k, IsDiscrete (V k)) → (∀ k, (z k).re = 0) → (∀ k, ∃ K' ∈ Θs M, ∃ W' ∈ Ωs M, HasType K' W' (V k)) →
    (∀ k, InfBdd R (V k)) → (∀ k, ‖z k‖ ≤ R) →
    ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (s : Tr E M), StrictMono φ ∧ Conv t s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t k).Disc) ∧ ∀ k, Emb (tw (V (φ k)) (z (φ k))) (· ∈ (t k).space)

end Props

def PairSlices : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ), F ∈ pairSpace U₁ U₂ →
  (∀ m₂, sl₁ F m₂ ∈ U₁ ∧ (sl₁ F m₂).1 = fun x => F (x, m₂)) ∧
  (∀ m₁, sl₂ F m₁ ∈ U₂ ∧ (sl₂ F m₁).1 = fun x => F (m₁, x))

def PairRestrict : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (U₁ : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (F : H E a b → ℂ), F ∈ pairSpace U₁ U₂ →
  (∀ m₁ (φ : Sm E b), (φ.1 = fun x => F (m₁, x)) → φ ∈ U₂') → F ∈ pairSpace U₁ U₂'

def PairFD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (f : ι → H E a b → ℂ), (∀ i, f i ∈ pairSpace U₁ U₂) →
  FiniteDimensional ℂ (Submodule.span ℂ (slices₁ f)) ∧ FiniteDimensional ℂ (Submodule.span ℂ (slices₂ f))

def SliceType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ), TypeH K₁ K₂ W₁ W₂ F →
  (∀ (φ : Sm E a) m₂, (φ.1 = fun x => F (x, m₂)) → TypeB K₁ W₁ φ) ∧
  (∀ (φ : Sm E b) m₁, (φ.1 = fun x => F (m₁, x)) → TypeB K₂ W₂ φ)

def PairStep₁ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (U₁ U₁' : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (T : Sm E a →ₗ[ℂ] Sm E a) (f : ι → H E a b → ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → IsStable U₁ → (∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ)) →
  (∀ ψ ∈ U₁, T ψ ∈ U₁') → (∀ i, f i ∈ pairSpace U₁ U₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∃ i m₂, ∃ φ : Sm E a, (φ.1 = fun x => f i (x, m₂)) ∧ T φ ≠ 0) →
  (fun i => ap₁ T (f i)) ≠ 0 ∧ (∀ i, ap₁ T (f i) ∈ pairSpace U₁' U₂) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (ap₁ T (f i))) ∧
    ∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h f = c • f → heckeAct h (fun i => ap₁ T (f i)) = c • fun i => ap₁ T (f i)

def PairStep₂ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (U₁ : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (T : Sm E b →ₗ[ℂ] Sm E b) (f : ι → H E a b → ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → IsStable U₂ → (∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) →
  (∀ ψ ∈ U₂, T ψ ∈ U₂') → (∀ i, f i ∈ pairSpace U₁ U₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∃ i m₁, ∃ φ : Sm E b, (φ.1 = fun x => f i (m₁, x)) ∧ T φ ≠ 0) →
  (fun i => ap₂ T (f i)) ≠ 0 ∧ (∀ i, ap₂ T (f i) ∈ pairSpace U₁ U₂') ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (ap₂ T (f i))) ∧
    ∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h f = c • f → heckeAct h (fun i => ap₂ T (f i)) = c • fun i => ap₂ T (f i)

def PairEmb : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (X₁ Y₁ : Submodule ℂ (Sm E a)) (X₂ Y₂ : Submodule ℂ (Sm E b)) (G : ι → H E a b → ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → IsStable X₁ → IsStable X₂ → Emb X₁ (· ∈ Y₁) → Emb X₂ (· ∈ Y₂) →
  G ≠ 0 → (∀ i, G i ∈ pairSpace X₁ X₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (G i)) →
  ∃ G' : ι → H E a b → ℂ, G' ≠ 0 ∧ (∀ i, G' i ∈ pairSpace Y₁ Y₂) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (G' i)) ∧
    ∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h G = c • G → heckeAct h G' = c • G'

def HullGen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (S : Set (Sm E N)),
  (∀ φ ∈ S, TypeB K W φ) → FiniteDimensional ℂ (Submodule.span ℂ S) → IsStable (hull S) ∧ FinGen K W (hull S)

def CapEquiv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (U : Submodule ℂ (Sm E N))
  (T : Sm E N →ₗ[ℂ] Sm E N) (ψ : Sm E N) (m : (E →+* ℂ) → Multiset ℂ), IsStable U →
  (∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) → ψ ∈ U → CapEig ψ m → CapEig (T ψ) m

def DiscInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (V : Submodule ℂ (Sm E M)),
  IsDiscrete V → ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL V τ m

def TopInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ),
  HasInfCharGL (⊤ : Submodule ℂ (Sm E 0)) τ 0

def InfOfEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (ψ : Sm E N)
  (m : (E →+* ℂ) → Multiset ℂ) (τ : E →+* ℂ) (m' : Multiset ℂ), InfTree → t.InfOf τ m' → ψ ∈ t.space → ψ ≠ 0 → CapEig ψ m →
  m' = m τ

def LeafBound : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (ψ : Sm E N)
  (m : (E →+* ℂ) → Multiset ℂ) (B : ℝ), InfTree → t.Good → ψ ∈ t.space → ψ ≠ 0 → CapEig ψ m →
  (∀ τ, ∀ x ∈ m τ, ‖x‖ ≤ B) → LeafZ (fun M V z => 0 < M → InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B) t

def ConvStrip : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N),
  Conv t s ↔ (∀ k, (t k).strip = s.strip) ∧
    ∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0))

def ConvShift : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N)
  (z : ℕ → ℂ) (z₀ : ℂ), Conv t s → Tendsto z atTop (𝓝 z₀) → Conv (fun k => (t k).shift (z k)) (s.shift z₀)

def ConvComp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N)
  (φ : ℕ → ℕ), Conv t s → StrictMono φ → Conv (fun k => t (φ k)) s

def ConvInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N)
  (τ : E →+* ℂ), Conv t s → s.Good → ∃ (m₀ : Multiset ℂ) (m : ℕ → Multiset ℂ), s.InfOf τ m₀ ∧ (∀ k, (t k).InfOf τ (m k)) ∧
    ∀ u, Tendsto (fun k => ((m k).map (u + ·)).prod) atTop (𝓝 ((m₀.map (u + ·)).prod))

def FactorStep : Prop := Sep4 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (W : Submodule ℂ (Kinf E N → ℂ)), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ω ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θ ∧ Fac K W Θ Ω

def OneStep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
  (f : ι → H E a b → ℂ) (m₁ m₂ : (E →+* ℂ) → Multiset ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → Fac K₁ W₁ Θ₁ Ω₁ → Fac K₂ W₂ Θ₂ Ω₂ → f ≠ 0 →
  (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∀ i (m₂ : GA E b), ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) →
  (∀ i (m₁ : GA E a), ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  (∀ φ ∈ hull (slices₁ f), IsAutForm φ) → (∀ φ ∈ hull (slices₂ f), IsAutForm φ) →
  NonPos (hull (slices₁ f)) → NonPos (hull (slices₂ f)) → CentIm (hull (slices₁ f)) → CentIm (hull (slices₂ f)) →
  (∀ τ, HasInfCharGL (hull (slices₁ f)) τ (m₁ τ)) → (∀ τ, HasInfCharGL (hull (slices₂ f)) τ (m₂ τ)) →
  (∀ τ, (m₁ τ).Nodup) → (∀ τ, (m₂ τ).Nodup) → (∀ i, f i ∈ pairSpace (hull (slices₁ f)) (hull (slices₂ f))) →
  ∃ (t₁ : Tr E a) (t₂ : Tr E b) (G : ι → H E a b → ℂ) (ψ₁ : Sm E a) (ψ₂ : Sm E b),
    Red t₁ ∧ Red t₂ ∧ t₁.Good ∧ t₂.Good ∧ t₁.AllLeaves (ListLeaf Θ₁ Ω₁) ∧ t₂.AllLeaves (ListLeaf Θ₂ Ω₂) ∧
    G ≠ 0 ∧ (∀ i, G i ∈ pairSpace t₁.space t₂.space) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (G i)) ∧
    (∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h f = c • f → heckeAct h G = c • G) ∧
    ψ₁ ∈ t₁.space ∧ ψ₁ ≠ 0 ∧ CapEig ψ₁ m₁ ∧ ψ₂ ∈ t₂.space ∧ ψ₂ ≠ 0 ∧ CapEig ψ₂ m₂

def LimLists : Prop := Lim5 → TwShift → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (Ωs : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))), KTypes E Ωs →
  ∃ Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ωf ∧
  ∀ Θs : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θs →
  ∃ Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θf ∧ LimLeafP N Θs Ωs Θf Ωf

def LimTrees : Prop := TrStable → Graft → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
  (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ),
  LimLeafP N Θs Ωs Θf Ωf → ReproAll E → ∀ (n : ℕ), n ≤ N → ∀ (t : ℕ → Tr E n) (R : ℝ), (∀ k, Red (t k)) → (∀ k, (t k).Good) →
  (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) → (∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (t k)) →
  ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E n) (s : Tr E n), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧
    s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t' k).Disc) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space)

def MCloseFacts : Prop := (∀ (ε : ℝ) (m n : Multiset ℂ) (B : ℝ), MClose ε m n → (∀ y ∈ n, ‖y‖ ≤ B) → ∀ x ∈ m, ‖x‖ ≤ B + ε) ∧
  (∀ (ε : ℝ) (m n : Multiset ℂ), ε < 1 / 4 → MClose ε m n → GapM n → m.Nodup) ∧
  ∀ (m : ℕ → Multiset ℂ) (n : Multiset ℂ), (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, MClose ε (m k) n) →
    ∀ u : ℂ, Tendsto (fun k => ((m k).map (u + ·)).prod) atTop (𝓝 ((n.map (u + ·)).prod))

def FactorLim : Prop := TrStable → Graft → InfTree → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
  (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ)
  (t : ℕ → Tr E N) (ψ : ℕ → Sm E N) (m : ℕ → (E →+* ℂ) → Multiset ℂ) (n : (E →+* ℂ) → Multiset ℂ) (B : ℝ),
  LimLeafP N Θs Ωs Θf Ωf → ReproAll E → (∀ k, Red (t k)) → (∀ k, (t k).Good) →
  (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) → (∀ k, ψ k ∈ (t k).space) → (∀ k, ψ k ≠ 0) → (∀ k, CapEig (ψ k) (m k)) →
  (∀ k τ, ∀ x ∈ m k τ, ‖x‖ ≤ B) → (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, MClose ε (m k τ) (n τ)) →
  ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E N) (s : Tr E N), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧ s.AllLeaves (ListLeaf Θf Ωf) ∧
    (∀ k, (t' k).Disc) ∧ (∀ τ, HasInfCharGL s.space τ (n τ)) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space)

end GlobalTheory.CompanionTheory.EGlue

end
