import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorEllPBound

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section defs
variable {n : ℕ} {K : Type} [Field K] {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def IsSubrepresentation (E : GLOps n K V) (W : Submodule K V) : Prop := ∀ a b, ∀ x ∈ W, E a b x ∈ W

def IsEquivariantMap (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') : Prop := ∀ a b x, T (E a b x) = E' a b (T x)

def restrictRepresentation (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) : GLOps n K W :=
  fun a b => (E a b).restrict (h a b)

def homRepresentation (E : GLOps n K V) (E' : GLOps n K V') : GLOps n K (V →ₗ[K] V') :=
  fun a b => LinearMap.llcomp K V V' V' (E' a b) - LinearMap.lcomp K V' (E a b)

def cyclicSubmodule (E : GLOps n K V) (v : V) : Submodule K V := Submodule.span K {x | ∃ u ∈ Umon E, x = u v}

end defs

def CompleteReducibilityGL : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ W : Submodule K V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule K V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W'

def WeightProjectionExistsStable : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∀ mu, ∃ π : Module.End K V, IsWtProj E mu π ∧
      ∀ W : Submodule K V, (∀ a, ∀ x ∈ W, E a a x ∈ W) → ∀ x ∈ W, π x ∈ W

def RestrictionIsRepresentation : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∀ (W : Submodule K V) (h : IsSubrepresentation E W), IsGLRep (restrictRepresentation E W h)

def HomSpaceIsRepresentation : Prop :=
  ∀ (n : ℕ) (K V V' : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V'),
    IsGLRep E → IsGLRep E' → IsGLRep (homRepresentation E E')

def IsotypicSubmodulesSpanTop : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → (⨆ mu, isoSub E mu) = ⊤

def InvariantProjectionExists : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∃ P : Module.End K V, IsInvProj E P

def EquivariantCommutesInvariantProjection : Prop :=
  ∀ (n : ℕ) (K V V' : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V'),
    IsGLRep E → IsGLRep E' → ∀ T : V →ₗ[K] V', IsEquivariantMap E E' T →
    ∀ (P : Module.End K V) (P' : Module.End K V'), IsInvProj E P → IsInvProj E' P' → ∀ x, T (P x) = P' (T x)

def OperatorsKillInvariantProjection : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∀ P : Module.End K V, IsInvProj E P → ∀ x a b, E a b (P x) = 0

def IsotypicProjectorTraceFormula : Prop :=
  ∀ (n : ℕ) (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : GLOps n K W), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K W), IsIsoProj E lam e →
    ∀ v0, IsHWV E lam v0 → ∀ (hL : IsSubrepresentation E (cyclicSubmodule E v0))
      (P : Module.End K (cyclicSubmodule E v0 →ₗ[K] W)), IsInvProj (homRepresentation (restrictRepresentation E _ hL) E) P →
      ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι K (cyclicSubmodule E v0)) (m : W),
        (Fintype.card ι : K) • ∑ i, P ((b.coord i).smulRight m) (b i) = e m

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

def homLattice (M : Submodule O W) (L : Submodule (KK O) W) : Submodule O (L →ₗ[KK O] W) where
  carrier := {f | ∀ x : L, (x : W) ∈ M → f x ∈ M}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hf hg x hx => by simpa using M.add_mem (hf x hx) (hg x hx)
  smul_mem' := fun c f hf x hx => by simpa using M.smul_mem c (hf x hx)

end lat

def LatticeAdaptedBasisExists : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (W : Type) [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (M : Submodule O W), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ L : Submodule (KK O) W, ∃ (d : ℕ) (b : Module.Basis (Fin d) (KK O) L), (∀ i, ((b i : L) : W) ∈ M) ∧
      ∀ x : L, (x : W) ∈ M → ∀ i, ∃ o : O, b.coord i x = algebraMap O (KK O) o

def HomLatticeDividedPowerStable : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)]
    (n : ℕ) (W : Type) [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W), IsGLRep E →
    ∀ M : Submodule O W, UZLattice E M → MQ (K := KK O) M = ⊤ →
    ∀ (L : Submodule (KK O) W) (hL : IsSubrepresentation E L),
      UZLattice (homRepresentation (restrictRepresentation E L hL) E) (homLattice M L) ∧ MQ (K := KK O) (homLattice M L) = ⊤

def HomRepEllBoundedByTarget : Prop :=
  ∀ (n : ℕ) (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : GLOps n K W), IsGLRep E → ∀ (L : Submodule K W) (hL : IsSubrepresentation E L),
      ellP (homRepresentation (restrictRepresentation E L hL) E) ⊤ ≤ ellOf E ⊤

end Formalism.MainNotions.G.GLWeightTheory
