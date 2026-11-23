import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.CardStepOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatLocGlob

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def PatchStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) → Submodule.IsLattice E L0 →
    ∀ γ : Ideal (𝓞 E) → UJ (σ : E →+* E) J,
      {p : Ideal (𝓞 E) | p.IsMaximal ∧ γ p ≠ 1}.Finite →
      (∀ p q : Ideal (𝓞 E), p.IsMaximal → q.IsMaximal → hcompl (K := E) p = hcompl (K := E) q →
        loc (K := E) p (gmap (linOf b (γ p : GL (Fin M) E)) L0) =
          loc (K := E) p (gmap (linOf b (γ q : GL (Fin M) E)) L0)) →
      ∃ g : HA (AF F) σ J, latSet σ J b L0 g =
        {v | ∀ p : Ideal (𝓞 E), p.IsMaximal → v ∈ loc (K := E) p (gmap (linOf b (γ p : GL (Fin M) E)) L0)}

def InterLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (N : Submodule (𝓞 E) V),
    Submodule.IsLattice E N → ∀ v : V, (∀ p : Ideal (𝓞 E), p.IsMaximal → v ∈ loc (K := E) p N) → v ∈ N

def CofinStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (L N : Submodule (𝓞 E) V),
    Submodule.IsLattice E L → Submodule.IsLattice E N →
    ∃ D : ℤ, D ≠ 0 ∧ (∀ v ∈ L, (D : 𝓞 E) • v ∈ N) ∧ (∀ v ∈ N, (D : 𝓞 E) • v ∈ L)

def FinMaxStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (D : ℤ), D ≠ 0 →
    {p : Ideal (𝓞 E) | p.IsMaximal ∧ ((D : 𝓞 E)) ∈ p}.Finite

def LocGmapStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (u : V ≃ₗ[E] V) (p : Ideal (𝓞 E)) (L : Submodule (𝓞 E) V),
    loc (K := E) p (gmap u L) = gmap u (loc (K := E) p L)

def LocEqStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L N : Submodule (𝓞 E) V) (D : ℤ) (p : Ideal (𝓞 E)),
    p.IsMaximal → ((D : 𝓞 E)) ∉ p → (∀ v ∈ L, (D : 𝓞 E) • v ∈ N) → (∀ v ∈ N, (D : 𝓞 E) • v ∈ L) →
    loc (K := E) p L = loc (K := E) p N

def LinOneStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (M : ℕ) (b : Module.Basis (Fin M) E V) (L : Submodule (𝓞 E) V),
    gmap (linOf b (1 : GL (Fin M) E)) L = L

end PI.UnitaryGroupMassFormula.UJClassMass

end
