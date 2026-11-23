import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.CoefDuty

def LatInt (D : D7) (M : MtFam D) (Q : Finset (PlE D.host)) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (w : D.what₂.places.Pl) : Prop :=
  (∀ y ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, y ∈ Set.range (D.what₂.jMt (D.what₂.muTw w) j)) ∧
  ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    GenAt D (D.what₂.places.resChar w) Q v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
    ∀ y ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, ∃ c : D.what₂.Mt (D.what₂.muTw w) j → D.what₂.LL,
      (∀ g, 0 ≤ D.what₂.places.val w (c g)) ∧
      NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real y) =
        (M (D.what₂.muTw w) j h1 h2).real (∑ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, D.what₂.embLL (c g) • g)

section Plain

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def IsInvForm (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, β x y = starRingEnd ℂ (β y x)) ∧ (∀ x, x ≠ 0 → 0 < (β x x).re) ∧
    ∀ (γ : GQ L n) x y, β (a.ρ γ x) (a.ρ γ y) = β x y

def IsBounded (J : Subgroup (GAf L n)) : Prop := ∃ F : Finset (GAf L n), ∀ κ ∈ J, ∃ f ∈ F, f⁻¹ * κ ∈ Umax L n

def IsClassReps (J : Subgroup (GAf L n)) (T : Finset (GAf L n)) : Prop :=
  ∀ g : GAf L n, ∃! t, t ∈ T ∧ ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * t * κ

def classSum (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))
    (f f' : GAf L n → a.W) : ℂ :=
  ∑ t ∈ T, ((Nat.card {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} : ℕ) : ℂ)⁻¹ * β (f t) (f' t)

def IsPetersson (a : NG.AlgWt L n) (B : (GAf L n → a.W) →ₗ⋆[ℂ] (GAf L n → a.W) →ₗ[ℂ] ℂ) : Prop :=
  ∀ f ∈ NG.AFall L n a.ρ, ∀ f' ∈ NG.AFall L n a.ρ, B f f' = starRingEnd ℂ (B f' f) ∧ (f ≠ 0 → 0 < (B f f).re) ∧
    ∀ h, B (NG.rt L n h f) (NG.rt L n h f') = B f f'

end Plain

def ClassSum {D : D7} {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) : Prop :=
  IsBounded X.J ∧ ∃ (β : X.wt.W →ₗ⋆[ℂ] X.wt.W →ₗ[ℂ] ℂ) (T : Finset (GAf D.host.E D.R.nV)) (c : ℝ),
    IsInvForm X.wt β ∧ IsClassReps X.J T ∧ 0 < c ∧
    ∀ x y : D.what₂.Mt μ j, inner ℂ x y = (c : ℂ) * classSum X.wt β X.J T (X.real x) (X.real y)

def EigSet {D : D7} {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) (l : ℕ) (Q : Finset (PlE D.host)) :
    Set (PlE D.host → ℕ → ℂ) :=
  {c | (∀ v k, ¬ GenAt D l Q v k → c v k = 0) ∧ ∃ y : D.what₂.Mt μ j, y ≠ 0 ∧
    ∀ (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D l Q v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      NG.tN X.J s ϖ k (X.real y) = c v k • X.real y}

open Classical in

def ptSys (D : D7) (i : D.nd.Loc) (x : D.nd.X i) : PlE D.host → ℕ → ℂ := fun v k =>
  if GenAt D (D.nd.l i) (D.nd.Q i) v k then iotaOC D i ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) else 0

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def Contains (N : NData R H what₂) (A : NAut N) (i : N.Loc) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, ∃ x, A.iotaQC i (A.iotaQ i x) = z

def Live (N : NData R H what₂) (i : N.Loc) : Prop :=
  ∃ π ∈ N.Z i, ∃ (r : GE N →* GL (Fin R.nV) (N.O i)) (ρ : GE N →* GL (Fin R.r) (N.O i)),
    IsHeckeGalois N i π r ∧ (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := R.t) r ρ (N.chi i) e) ∧
    AbsIrrSub (mapRep (IsLocalRing.residue (N.O i)) ρ) ⊤

def ZDecomp (N : NData R H what₂) (i : N.Loc) : Prop :=
  ∀ π ∈ N.Z i, ∀ r : GE N →* GL (Fin R.nV) (N.O i), IsHeckeGalois N i π r →
    ∃ (ρ : GE N →* GL (Fin R.r) (N.O i)), ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := R.t) r ρ (N.chi i) e

def IsWildInertiaCyclotomicElement (N : NData R H what₂) (i : N.Loc) (g0 : GE N) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsInertiaCyclotomicGeneratorElement N i g0 ∧ ((∃ k, N.l i = H.g k) → ∀ w ∈ placesOver H.E (N.l i),
    g0 ∈ Ine (F := H.E) (N.plOm.1 w) → g0 ∈ wildSet N (N.plOm.1 w))

def TakenWild (N : NData R H what₂) (i : N.Loc) (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : Algebra ℤ_[N.l i] A)
    (_ : Module.Finite ℤ_[N.l i] A) (_ : Algebra A (N.O i)) (_ : IsScalarTower ℤ_[N.l i] A (N.O i))
    (TA : Subalgebra A (N.X i → A)) (repA : N.X i → (GE N →* GL (Fin R.nV) A))
    (ρA : N.X i → (GE N →* GL (Fin R.r) A)) (χA : ℕ → (GE N →* Aˣ)),
    GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsEnlargement N i rep ρ A TA repA ρA χA ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting R.t TA (N.Z i) repA ρA χA ∧
    ∀ π ∈ N.Z i, ∃ g0 L eB e1 X0, IsWildInertiaCyclotomicElement N i g0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice R.t TA repA ρA χA π g0 L eB e1 X0 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.RootsIn R.t (N.O i) eB X0

def Chosen (N : NData R H what₂) (A : NAut N) (i : N.Loc) (S : Set ℂ) : Prop :=
  ∃ (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))),
    GoodR N i rep ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting R.t (N.T i) (N.Z i) rep ρ (N.chi i) ∧
    ∀ π ∈ N.Z i, ∃ g0 L eB e1 X0, IsWildInertiaCyclotomicElement N i g0 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsChoice R.t (N.T i) rep ρ (N.chi i) π g0 L eB e1 X0 ∧
      ∀ x, ∃ α : Fin R.t → ℂ, (∀ c, α c ∈ S) ∧
        (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.blockPol (eB x) (X0 x)).map (iotaO N A i) = ∏ c, (X - C (α c))

structure LocExt (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc) where
  l_eq : N₀.l i₀ = N₁.l i₁
  φ : N₀.O i₀ →+* N₁.O i₁
  φ_iota : ∀ z, iotaO N₁ A₁ i₁ (φ z) = iotaO N₀ A₀ i₀ z
  φ_alg : ∀ (z : ℤ_[N₀.l i₀]) (z' : ℤ_[N₁.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z'
  e : N₁.X i₁ ≃ N₀.X i₀
  out : ∀ v, SplitOut N₁ i₁ v ↔ SplitOut N₀ i₀ v
  hT : ∀ v k x, SplitOut N₁ i₁ v → 1 ≤ k → k ≤ R.nV →
    (N₁.hT i₁ v k : N₁.X i₁ → N₁.O i₁) x = φ ((N₀.hT i₀ v k : N₀.X i₀ → N₀.O i₀) (e x))
  Z : ∀ x, x ∈ N₁.Z i₁ ↔ e x ∈ N₀.Z i₀
  γ : GE N₁ ≃* GE N₀
  γ_cont : Continuous γ
  γ_cont' : Continuous γ.symm
  frob : ∀ (w : PlE H) (σ : GE N₁), (∃ B : ValuationSubring N₁.Om, IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ) ↔
    ∃ B : ValuationSubring N₀.Om, IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) (γ σ)
  ine : ∀ (w : PlE H) (σ : GE N₁), σ ∈ Ine (F := H.E) (N₁.plOm.1 w) ↔ γ σ ∈ Ine (F := H.E) (N₀.plOm.1 w)
  wild : ∀ (w : PlE H) (σ : GE N₁), σ ∈ wildSet N₁ (N₁.plOm.1 w) ↔ γ σ ∈ wildSet N₀ (N₀.plOm.1 w)
  cyc : ∀ σ : GE N₁, HEq (cycZ (F := H.E) (Ω := N₀.Om) (N₀.l i₀) (γ σ)) (cycZ (F := H.E) (Ω := N₁.Om) (N₁.l i₁) σ)
  chi : ∀ c, 1 ≤ c → c ≤ R.t → ∀ σ : GE N₁,
    ((N₁.chi i₁ c σ : (N₁.O i₁)ˣ) : N₁.O i₁) = φ ((N₀.chi i₀ c (γ σ) : (N₀.O i₀)ˣ) : N₀.O i₀)

end Record

def TakenAll (D : D7) : Prop := ∀ i, Live D.nd i → ∃ r ρ, GoodR D.nd i r ∧ TakenWild D.nd i r ρ

def Large (D : D7) : Prop := SumRepresentations.hypO D ∧ GlobalTheory.SplitCoef.OSplit D ∧ TakenAll D

def Duties (D : D7) : Prop :=
  SumRepresentations.hypO D ∧ (∀ i r, GoodR D.nd i r → AbsIrreducibleDistinct D i r) ∧ Formalism.MainNotions.N.K.Rows.AllDesignConditions D ∧ TypePrimeCongruences.TypePrimeWildIdempotentChoice D

end GlobalTheory.CoefDuty

end
