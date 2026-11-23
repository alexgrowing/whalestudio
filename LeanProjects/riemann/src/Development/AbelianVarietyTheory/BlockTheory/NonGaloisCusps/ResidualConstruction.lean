import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Polynomial

section Base

variable {Γ : Type} [Group Γ] {X : Type} {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}

abbrev mat {B : Type} [CommRing B] {k : ℕ} (σ : Γ →* GL (Fin k) B) (g : Γ) : Matrix (Fin k) (Fin k) B :=
  ((σ g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B)

abbrev toFr (A : Type) [CommRing A] : A →+* FractionRing A := algebraMap A (FractionRing A)

def overK {k : ℕ} (σ : Γ →* GL (Fin k) A) : Representation (FractionRing A) Γ (Fin k → FractionRing A) :=
  matRep (mapM (toFr A) ((Units.coeHom _).comp σ))

def InRing (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (a : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∃ (m : ℕ) (f : Fin m → X → A) (h : Fin m → Γ), (∀ k, f k ∈ T) ∧
    a = ∑ k, fun x => f k x • mat (rep x) (h k)

def InMatrixCongruenceModule (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X)
    (e s : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∃ (m : ℕ) (j : Fin m → X → A) (a : Fin m → X → Matrix (Fin n) (Fin n) A),
    (∀ k, j k ∈ T ∧ j k π = 0 ∧ InRing T rep (a k)) ∧
    s = ∑ k, fun x => j k x • (e x * a k x * e x)

def CharPolyIn (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) : Prop :=
  ∀ (h : Γ) (d : ℕ), (fun x => (mat (rep x) h).charpolyRev.coeff d) ∈ T

def ResidualSame (rep : X → (Γ →* GL (Fin n) A)) : Prop :=
  ∀ (x y : X) (h : Γ), ((mat (rep x) h).map (IsLocalRing.residue A)).charpoly =
    ((mat (rep y) h).map (IsLocalRing.residue A)).charpoly

def IsDecomp (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))) :
    Prop :=
  ∀ g u, e (overK σ g u) =
    (overK ρ g (e u).1, fun c : Fin t => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A) * (e u).2 c)

def HidaSetting (t : ℕ) (T : Subalgebra A (X → A)) (Z : Finset X) (rep : X → (Γ →* GL (Fin n) A))
    (ρ : X → (Γ →* GL (Fin r) A)) (χ : ℕ → (Γ →* Aˣ)) : Prop :=
  IsLocalRing T ∧ (∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y) ∧
  (∀ x, IsSS (overK (rep x))) ∧
  CharPolyIn T rep ∧
  (∀ x, AbsIrrDistinct (overK (rep x))) ∧ ResidualSame rep ∧
  (∀ x ∈ Z, ∃ e, IsDecomp (t := t) (rep x) (ρ x) χ e) ∧
  (∀ x ∈ Z, AbsIrrSub (mapRep (IsLocalRing.residue A) (ρ x)) ⊤)

def blockPol (e M : Matrix (Fin n) (Fin n) A) : A[X] :=
  Matrix.det ((Polynomial.X : A[X]) • e.map (C (R := A)) - M.map (C (R := A)) + 1 - e.map (C (R := A)))

def IsChoice (t : ℕ) (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (ρ : X → (Γ →* GL (Fin r) A)) (χ : ℕ → (Γ →* Aˣ)) (π : X) (g0 : Γ) (L : ℕ)
    (eB e1 X0 : X → Matrix (Fin n) (Fin n) A) : Prop :=
  (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧
  (∃ e, IsDecomp (t := t) (rep π) (ρ π) χ e ∧
    (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧
    ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧
      ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0)) ∧
  (∃ (ϖ : A) (s : X → Matrix (Fin n) (Fin n) A), Irreducible ϖ ∧ InMatrixCongruenceModule T rep π eB s ∧
    X0 = fun x => eB x * mat (rep x) g0 * eB x + ϖ ^ L • s x) ∧
  ∀ x, (((blockPol (eB x) (X0 x)).map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t

def RootsIn (t : ℕ) (B : Type) [CommRing B] [Algebra A B] (eB X0 : X → Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ x, ∃ α : Fin t → FractionRing B,
    (blockPol (eB x) (X0 x)).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - C (α c))

end Base

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

def IsInertiaCyclotomicGeneratorElement (g0 : GE N) : Prop :=
  (∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  ∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
    1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])

def IsEnlargement (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
    (A : Type) [CommRing A] [Algebra A (N.O i)] (TA : Subalgebra A (N.X i → A))
    (repA : N.X i → (GE N →* GL (Fin R.nV) A)) (ρA : N.X i → (GE N →* GL (Fin R.r) A))
    (χA : ℕ → (GE N →* Aˣ)) : Prop :=
  Function.Injective (algebraMap A (N.O i)) ∧
  Subalgebra.toSubmodule (N.T i) =
    Submodule.span (N.O i) ((fun f : N.X i → A => fun x => algebraMap A (N.O i) (f x)) '' (TA : Set _)) ∧
  (∀ x, rep x = mapRep (algebraMap A (N.O i)) (repA x)) ∧
  (∀ x ∈ N.Z i, ρ x = mapRep (algebraMap A (N.O i)) (ρA x)) ∧
  ∀ c, 1 ≤ c → c ≤ R.t → ∀ g, ((N.chi i c g : (N.O i)ˣ) : N.O i) = algebraMap A (N.O i) ((χA c g : Aˣ) : A)

def RepCont (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x, Continuous fun g => mat (rep x) g

def ConsExist : Prop :=
  ∀ (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra ℤ_[N.l i] A]
    [Module.Finite ℤ_[N.l i] A] [Algebra A (N.O i)] [IsScalarTower ℤ_[N.l i] A (N.O i)]
    (TA : Subalgebra A (N.X i → A)) (repA : N.X i → (GE N →* GL (Fin R.nV) A))
    (ρA : N.X i → (GE N →* GL (Fin R.r) A)) (χA : ℕ → (GE N →* Aˣ)),
    RepCont N i rep → IsEnlargement N i rep ρ A TA repA ρA χA → HidaSetting R.t TA (N.Z i) repA ρA χA →
    (∀ π ∈ N.Z i, ∀ g0, IsInertiaCyclotomicGeneratorElement N i g0 → ∀ L : ℕ,
      ∃ eB e1 X0, IsChoice R.t TA repA ρA χA π g0 L eB e1 X0) ∧
    (∀ (g0 : N.X i → GE N) (L : N.X i → ℕ)
        (eB e1 X0 : N.X i → N.X i → Matrix (Fin R.nV) (Fin R.nV) A),
      (∀ π ∈ N.Z i, IsInertiaCyclotomicGeneratorElement N i (g0 π) ∧ IsChoice R.t TA repA ρA χA π (g0 π) (L π) (eB π) (e1 π) (X0 π)) →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B),
        Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧
        ∀ π ∈ N.Z i, RootsIn R.t B (eB π) (X0 π)) ∧
    (∀ π ∈ N.Z i, ∀ g0 L eB e1 X0, IsInertiaCyclotomicGeneratorElement N i g0 → IsChoice R.t TA repA ρA χA π g0 L eB e1 X0 →
      RootsIn R.t (N.O i) eB X0 →
      ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧
        (∀ x, S.eB x = (eB x).map (algebraMap A (N.O i))) ∧
        (∀ x, S.e1 x = (e1 x).map (algebraMap A (N.O i))) ∧
        (∀ x, S.X0 x = (X0 x).map (algebraMap A (N.O i))) ∧
        GoodCongruenceObjects N rep ρ π S)

def TakenAfter (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : Algebra ℤ_[N.l i] A)
    (_ : Module.Finite ℤ_[N.l i] A) (_ : Algebra A (N.O i)) (_ : IsScalarTower ℤ_[N.l i] A (N.O i))
    (TA : Subalgebra A (N.X i → A)) (repA : N.X i → (GE N →* GL (Fin R.nV) A))
    (ρA : N.X i → (GE N →* GL (Fin R.r) A)) (χA : ℕ → (GE N →* Aˣ)),
    IsEnlargement N i rep ρ A TA repA ρA χA ∧ HidaSetting R.t TA (N.Z i) repA ρA χA ∧
    ∀ π ∈ N.Z i, ∃ g0 L eB e1 X0, IsInertiaCyclotomicGeneratorElement N i g0 ∧ IsChoice R.t TA repA ρA χA π g0 L eB e1 X0 ∧
      RootsIn R.t (N.O i) eB X0

theorem isEnlargement_self (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) :
    IsEnlargement N i rep ρ (N.O i) (N.T i) rep ρ (N.chi i) := by
  refine ⟨fun _ _ h => h, ?_, fun x => ?_, fun x _ => ?_, fun _ _ _ _ => rfl⟩
  · have : ((fun f : N.X i → N.O i => fun x => algebraMap (N.O i) (N.O i) (f x)) '' (N.T i : Set _)) =
        (Subalgebra.toSubmodule (N.T i) : Set _) := by
      simp
    rw [this, Submodule.span_eq]
  · ext g a b
    rfl
  · ext g a b
    rfl

end Record

example {A : Type} [CommRing A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) : blockPol 1 M = M.charpoly := by
  unfold blockPol Matrix.charpoly Matrix.charmatrix
  congr 1
  ext a b
  by_cases h : a = b <;> simp [h, Matrix.one_apply]

def ConsExist_at (D : D7) : Prop := ∀ i : D.nd.Loc, ConsExist D.nd i

def ConsExistF {eps : ℝ} (Fm : FamP eps) : Prop := ∀ (x : ℝ) (k : Fm.Ix x), ConsExist_at (Fm.D x k)

def ConsExistClosed (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm _ => ConsExistF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

end
