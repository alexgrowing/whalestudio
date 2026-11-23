import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidualConstituentShape

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

section Loc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def cpol {Γ S : Type} [Group Γ] [CommRing S] {a : ℕ} (ρ : Γ →* GL (Fin a) S) (g : Γ) : S[X] :=
  ((ρ g : GL (Fin a) S) : Matrix (Fin a) (Fin a) S).charpoly

def IsPointRepBar (i : N.Loc) (x : N.X i) (ρ : GE N →* GL (Fin R.nV) (Qbar (N.l i))) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))) ∧
  IsSSRep ρ ∧
  ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    cpol ρ σ = (heckePol N i x w).map (iotaOQ N A i)

def EnlargementAt (i : N.Loc) : Prop :=
  ∀ ρ : N.X i → (GE N →* GL (Fin R.nV) (Qbar (N.l i))), (∀ x, IsPointRepBar N A i x (ρ x)) →
    (∃ L' : Loc.FinExt (N.l i), (∀ a : KK N i, A.iotaQ i a ∈ L'.1) ∧
      ∀ x, ∃ ρ' : GE N →* GL (Fin R.nV) ↥L'.1,
        (∃ P : GL (Fin R.nV) (Qbar (N.l i)), ∀ g,
          mapRep (algebraMap ↥L'.1 (Qbar (N.l i))) ρ' g = P * ρ x g * P⁻¹) ∧
        AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ'))) ∧
    ∀ x y g (k : ℕ), ‖(cpol (ρ x) g).coeff k‖ ≤ 1 ∧
      ‖(cpol (ρ x) g).coeff k - (cpol (ρ y) g).coeff k‖ < 1

def CoeffLarge (i : N.Loc) : Prop :=
  ∃ r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)), GoodR N i r ∧
    ∀ x W, IsIrrSub (mapRep (toK N i) (r x)) W → AbsIrrSub (mapRep (toK N i) (r x)) W

def ResidualSame (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x y g, cpol (redRep N i (r x)) g = cpol (redRep N i (r y)) g

def ConstituentsOver (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  (∀ x, IsSS (repK N i r x) ∧ AbsIrrDistinct (repK N i r x)) ∧ ResidualSame N i r

def IsBlockComplement (i : N.Loc) (r₀ : GE N →* GL (Fin R.nV) (N.O i))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
    ∀ g v, e (((mapRep (toK N i) r₀ g : GL _ _) : Matrix _ _ _).mulVec v) =
      (((mapRep (toK N i) ρ g : GL _ _) : Matrix _ _ _).mulVec (e v).1,
        fun c : Fin R.t => toK N i ((N.chi i (c.1 + 1) g : (N.O i)ˣ) : N.O i) * (e v).2 c)

def ResidualShape (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  1 < R.r ∧ AbsIrrSub (redRep N i ρ) ⊤ ∧
    ∀ x g, cpol (redRep N i (r x)) g = cpol (redRep N i ρ) g *
      ∏ c ∈ Finset.Icc 1 R.t,
        (X - C (IsLocalRing.residue (N.O i) ((N.chi i c g : (N.O i)ˣ) : N.O i)))

def ResidualAtGood (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x₀ ∈ N.Zgood i, (∃ ρ, IsBlockComplement N i (r x₀) ρ) ∧
    ∀ ρ, IsBlockComplement N i (r x₀) ρ → ResidualShape N i r ρ

end Loc

def TypePrimeSizes (D : D7) : Prop :=
  100 ≤ D.R.r ∧ (∀ k : Fin 2, 2 * D.R.r ≤ D.host.g k) ∧
    Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1))

def Constituents_at (D : D7) : Prop :=
  ∀ i : D.nd.Loc, EnlargementAt D.nd D.naut i ∧
    (CoeffLarge D.nd i → ∀ r, GoodR D.nd i r → ConstituentsOver D.nd i r)

def ResidualShape_at (D : D7) : Prop :=
  TypePrimeSizes D → ∀ i : D.nd.Loc, CoeffLarge D.nd i → ∀ r, GoodR D.nd i r → ResidualAtGood D.nd i r

def ConstituentsAndShape_at (D : D7) : Prop := Constituents_at D ∧ ResidualShape_at D

def ConstituentsAndShapeF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ConstituentsAndShape_at (Fm.D x i)

def ConstituentsAndShape (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => ConstituentsAndShapeF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.ResidualConstituentShape

end
