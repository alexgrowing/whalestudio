import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

def SameSS {k Γ V W : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) : Prop :=
  ∃ (s : CompositionSeries (Submodule (MonoidAlgebra k Γ) ρ.asModule))
    (t : CompositionSeries (Submodule (MonoidAlgebra k Γ) σ.asModule)),
    s.head = ⊥ ∧ s.last = ⊤ ∧ t.head = ⊥ ∧ t.last = ⊤ ∧
    ∃ f : Fin s.length ≃ Fin t.length, ∀ j : Fin s.length,
      Nonempty ((↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) ≃ₗ[MonoidAlgebra k Γ]
        (↥(t (f j).succ) ⧸ (t (f j).castSucc).submoduleOf (t (f j).succ)))

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

section HidaSetting

variable (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def repBar (x : N.X i) : Representation (kk N i) (GE N) (Fin R.nV → kk N i) :=
  matRep (mapM (IsLocalRing.residue (N.O i)) (rO N i r x))

def ContSemisimple : Prop :=
  ∀ x, Continuous (fun g => rO N i r x g) ∧ IsSS (repK N i r x)

def CharPolyInT : Prop :=
  ∀ (h : GE N) (d : ℕ),
    (fun x => (Matrix.det (1 - (X : (N.O i)[X]) • (rO N i r x h).map (C (R := N.O i)))).coeff d) ∈ N.T i

def Constituents : Prop :=
  (∀ x, AbsIrrDistinct (repK N i r x)) ∧
  (∀ x y, SameSS (repBar N i r x) (repBar N i r y)) ∧
  (∀ x (h : GE N), ∃ s : Multiset (kk N i),
    ((rO N i r x h).map (IsLocalRing.residue (N.O i))).charpoly = (s.map fun a => X - C a).prod)

def ThetaShape : Prop :=
  ∀ x ∈ N.Z i,
    (∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
      ∀ g u, e ((mapM (toK N i) (rO N i r x) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ x) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)) ∧
    AbsIrrSub (mapRep (IsLocalRing.residue (N.O i)) (ρ x)) ⊤

def HidaSetting : Prop :=
  ContSemisimple N i r ∧ CharPolyInT N i r ∧ Constituents N i r ∧ ThetaShape N i r ρ

def IsStdElt (g₀ : GE N) : Prop :=
  (∃ w ∈ placesOver H.E (N.l i), g₀ ∈ Ine (F := H.E) (N.plOm.1 w)) ∧
  ∃ u : ℤ_[N.l i]ˣ, ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g₀ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
    1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * (u : ℤ_[N.l i])

def StdEltExists : Prop := ∀ i : N.Loc, ∃ g₀ : GE N, IsStdElt N i g₀

def blockPoly (eB X0 : MatN N i) : (N.O i)[X] :=
  Matrix.det ((X : (N.O i)[X]) • eB.map (C (R := N.O i)) - X0.map (C (R := N.O i)) + 1 -
    eB.map (C (R := N.O i)))

def ChosenBefore (eB e1 X0 : N.X i → MatN N i) : Prop :=
  InR N i r eB ∧ InR N i r e1 ∧ InR N i r X0 ∧
  ∀ x, (blockPoly N i (eB x) (X0 x)).Monic ∧ (blockPoly N i (eB x) (X0 x)).natDegree = R.t ∧
    ((blockPoly N i (eB x) (X0 x)).map (toK N i)).Separable

end HidaSetting

section Enlarge

variable (N : NData R H what₂) (i : N.Loc) (N₁ : NData R H what₂) (i₁ : N₁.Loc)
  (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁) (β : N.X i ≃ N₁.X i₁)

def IsEnlargement : Prop :=
  N₁.l i₁ = N.l i ∧ Function.Injective φ ∧ φ.Finite ∧
  (∀ v (y : N.Om), σ y ∈ N₁.plOm.1 v ↔ y ∈ N.plOm.1 v) ∧
  Subalgebra.toSubmodule (N₁.T i₁) = Submodule.span (N₁.O i₁)
    ((fun (f : N.X i → N.O i) (x₁ : N₁.X i₁) => φ (f (β.symm x₁))) '' (N.T i : Set (N.X i → N.O i))) ∧
  (∀ x, β x ∈ N₁.Z i₁ ↔ x ∈ N.Z i) ∧ N₁.S i₁ = N.S i ∧ N₁.Q i₁ = N.Q i ∧
  ∀ c, 1 ≤ c → c ≤ R.t → ∀ g : GE N,
    ((N₁.chi i₁ c (AlgEquiv.autCongr σ g) : (N₁.O i₁)ˣ) : N₁.O i₁) =
      φ ((N.chi i c g : (N.O i)ˣ) : N.O i)

variable {N i N₁ i₁}

def enlRep {a : ℕ} (M : N.X i → (GE N →* GL (Fin a) (N.O i))) (x₁ : N₁.X i₁) :
    GE N₁ →* GL (Fin a) (N₁.O i₁) :=
  (mapRep φ (M (β.symm x₁))).comp (AlgEquiv.autCongr σ).symm.toMonoidHom

def enlMat (a : N.X i → MatN N i) (x₁ : N₁.X i₁) : MatN N₁ i₁ := (a (β.symm x₁)).map φ

def RootsIn (eB X0 : N.X i → MatN N i) : Prop :=
  ∀ x, ∃ al : Fin R.t → KK N₁ i₁,
    (blockPoly N i (eB x) (X0 x)).map ((toK N₁ i₁).comp φ) = ∏ c, (X - C (al c))

end Enlarge

def ConstructionsExist (N : NData R H what₂) : Prop :=
  ∀ (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (g₀ : GE N),
    HidaSetting N i r ρ → IsStdElt N i g₀ →
    ∃ eB e1 X0 : N.X i → N.X i → MatN N i,
      (∀ π ∈ N.Z i, ChosenBefore N i r (eB π) (e1 π) (X0 π)) ∧
      (∃ (N₁ : NData R H what₂) (i₁ : N₁.Loc) (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁)
          (β : N.X i ≃ N₁.X i₁), IsEnlargement N i N₁ i₁ σ φ β ∧
          ∀ π ∈ N.Z i, RootsIn φ (eB π) (X0 π)) ∧
      ∀ (N₁ : NData R H what₂) (i₁ : N₁.Loc) (σ : N.Om ≃ₐ[H.E] N₁.Om) (φ : N.O i →+* N₁.O i₁)
        (β : N.X i ≃ N₁.X i₁), IsEnlargement N i N₁ i₁ σ φ β →
        ∀ π ∈ N.Z i, RootsIn φ (eB π) (X0 π) →
          ∃ S : IdempotentChoiceData N₁ i₁, S.eB = enlMat φ β (eB π) ∧ S.e1 = enlMat φ β (e1 π) ∧
            S.X0 = enlMat φ β (X0 π) ∧ S.g0 = AlgEquiv.autCongr σ g₀ ∧
            GoodCongruenceObjects N₁ (enlRep σ φ β r) (enlRep σ φ β ρ) (β π) S

def ConstructionsExist_at (D : D7) : Prop := ConstructionsExist D.nd

def ConstructionsExistF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ConstructionsExist_at (Fm.D x i)

def ConstructionsExistClosed (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => ConstructionsExistF Fm)

def ConstructionsExistAll : Prop :=
  ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂), ConstructionsExist N

end GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction

end
