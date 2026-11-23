import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def InducedSectionsSpanStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (R : Type) [CommRing R] [IsDomain R],
    (IsField R ∨ IsDiscreteValuationRing R ∨ Nonempty (R ≃+* ℤ)) →
    (Dominant mu → inducedSections R mu = (Submodule.span R (Set.range fun I : TIdx mu => mapCoord (n := n) R (brk mu I)) : Set _)) ∧
    (¬ Dominant mu → inducedSections R mu = {0})

def RationalBitableauLatticeStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu →
    (Submodule.span ℤ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => mu a + ((-(mu (lastIdx n))).toNat : ℤ))
          (MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu (canT mu)))}

def WeightLatticeSaturationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (La : Submodule O V),
    IsGLRep E → Dominant mu → isoSub E mu = ⊤ → UZLattice E La →
    (∀ x ∈ La, ∀ nu e, IsWtProj E nu e → e x ∈ La) →
    Submodule.span O {x | ∃ u ∈ UZmon E, ∃ y ∈ La, y ∈ weightSp E mu ∧ x = u y} ≤ La ∧
    ∀ y ∈ La, ∀ u ∈ UZmon E, ∀ e, IsWtProj E mu e → e (u y) ∈ La ∧ e (u y) ∈ weightSp E mu

def dualOps {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) :
    GLOps n K (Module.Dual K V) := fun a b => -(LinearMap.dualMap (E a b))

def MinimalLatticeDualityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    (Delta (O := O) E v : Set V) =
      {x | ∀ φ ∈ Nabla (O := O) (dualOps E) (dualWt mu) v', φ x ∈ Set.range (algebraMap O (KK O))}

end Formalism.InvariantFactorPaths.ColumnFamilies
