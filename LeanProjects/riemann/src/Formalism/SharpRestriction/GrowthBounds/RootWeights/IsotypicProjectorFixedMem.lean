import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorEllPBound

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def highestWeightVectors {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (lam : Fin n → ℤ) :
    Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

def generatedSubrep {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (h : V) :
    Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, x = u h}

def IsotypicProjectorFixedMem : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K V), IsIsoProj E lam e →
      ∀ Y : V, e Y = Y → Y ∈ isoSub E lam

def GeneratedMultipleOfHWV : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (h : V), h ∈ highestWeightVectors E lam →
      generatedSubrep E h ≤ Submodule.span K {h} ⊔ ⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)

def DualLatticeDivisibility : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ (t : KK O) (z : V),
      (∀ f : V →ₗ[KK O] KK O, (∀ x ∈ M, ∃ o : O, f x = algebraMap O (KK O) o) →
        ∃ o : O, f z = t * algebraMap O (KK O) o) →
      ∃ m ∈ M, z = t • m

def LatticeSubspaceBasis : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ H : Submodule (KK O) V, ∃ (k : ℕ) (h : Fin k → V), (∀ j, h j ∈ M ∧ h j ∈ H) ∧
      LinearIndependent (KK O) h ∧ H ≤ Submodule.span (KK O) (Set.range h) ∧
      ∀ x ∈ M, x ∈ H → ∃ o : Fin k → O, x = ∑ j, o j • h j

def GeneratedLatticeCorollary : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M →
      ∀ lam : Fin n → ℤ, Dominant lam →
      ∀ π : Module.End (KK O) V, IsWtProj E lam π →
      ∀ h : V, h ∈ M → h ∈ highestWeightVectors E lam → h ≠ 0 →
      ∀ (c : ℤ) (y : V), y ∈ generatedSubrep E h →
        (∀ u ∈ UZmon E, ∃ o : O, π (u y) = ((p : KK O) ^ c * algebraMap O (KK O) o) • h) →
        ∃ m ∈ M, y = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m

end Formalism.MainNotions.G.GLWeightTheory
