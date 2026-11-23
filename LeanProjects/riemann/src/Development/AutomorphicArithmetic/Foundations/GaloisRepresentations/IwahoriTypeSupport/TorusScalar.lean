import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPow

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

structure Loc : Prop where
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  geo : GlobalTheory.Published.GeometricLemma
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  disj : GlobalTheory.Published.TotallyDisjointProductIrreducible
  mp : GlobalTheory.Published.MoyPrasadJacquetIso
  dzi : GlobalTheory.Published.DepthZeroInduction
  dzj : GlobalTheory.Published.DepthZeroJacquetInjective

structure LocN : Prop where
  loc : Loc

def Lifts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (η : kˣ →* ℂˣ) (θ : 𝓀[k]ˣ →* ℂˣ), IsTameLift η θ → IsSmoothChar η) ∧
    (∀ θ : 𝓀[k]ˣ →* ℂˣ, ∃ η : kˣ →* ℂˣ, IsTameLift η θ) ∧
    ∀ (η : kˣ →* ℂˣ) (θ θ' : 𝓀[k]ˣ →* ℂˣ), IsTameLift η θ → IsTameLift η θ' → θ = θ'

def FinTri : Prop :=
  ∀ (R : Type) [CommRing R] (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (h : GL (Fin N) R),
    (∀ i j, j < i → (h : Matrix (Fin N) (Fin N) R) i j = 0) →
    ∃ hp : h ∈ parab R (stdBlocks d hd), ∀ a,
      ((GeneralLinearGroup.det (leviProj R (stdBlocks d hd) ⟨h, hp⟩ a) : Rˣ) : R) =
        ∏ j : Fin (d a), (h : Matrix (Fin N) (Fin N) R) (stdBlocks d hd ⟨a, j⟩) (stdBlocks d hd ⟨a, j⟩)

def TypeToIw : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) (μ : Fin s → kˣ →* ℂˣ),
    (∀ a, IsTameLift (μ a) (θ a)) → ∀ v ∈ typeSp π (stdBlocks d hd) θ,
      GlobalTheory.TameIwahori.IsIwVec (fun i => μ (blockOf d hd i)) π v

def TameDepth : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (ω : Fin N → 𝓀[k]ˣ →* ℂˣ), HasTameSupp π ω → fixed π (KOne k (Fin N)) ≠ ⊥

def Reorder : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (μ : Fin N → kˣ →* ℂˣ), IsCuspSupport π (fun _ : Fin N => 1) (fun i => detRep (Fin 1) (μ i)) →
    IsSubquotient π (multiProd (iwBlocks N) fun i => detRep (Fin 1) (μ i))

def FinVec : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H : Subgroup Γ) (ψ : H →* ℂˣ) (U X W : Type) [AddCommGroup U] [Module ℂ U]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ U) (σ : Representation ℂ Γ X)
    (f : ρ.IntertwiningMap σ), Function.Surjective f → (∃ x : X, x ≠ 0) → ∀ φ : U →ₗ[ℂ] W,
    (∀ (h : H) (u : U), φ (ρ h u) = (ψ h : ℂ) • φ u) → (∀ u : U, (∀ g : Γ, φ (ρ g u) = 0) → u = 0) →
    ∃ v : X, v ≠ 0 ∧ ∀ h : H, σ h v = (ψ h : ℂ) • v

def ParaFactor : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n),
    (∀ g : parahoric k e, ∃ (p : parab k e) (x : leviK k m), (p : GL n k) ∈ KO k n ∧ leviProj k e p = (x : Levi k m) ∧
      redLevi k m x = parahoricProj k e g ∧ ∃ c ∈ KOne k n, (g : GL n k) = p * c) ∧
    ∀ p : parab k e, (p : GL n k) ∈ KOne k n → leviProj k e p ∈ leviKOne k m

def SubqType : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (W V : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (π : Representation ℂ (GL (Fin N) k) V)
    (θ : Fin s → 𝓀[k]ˣ →* ℂˣ),
    (∀ (x : leviK k fun a => Fin (d a)) (w : W), ρ x w = (leviChar (fun a => Fin (d a)) θ (redLevi k _ x) : ℂ) • w) →
    IsSubquotient π (parInd (stdBlocks d hd) ρ) → fixed π (KOne k (Fin N)) ≠ ⊥ → HasTypeVec π (stdBlocks d hd) θ

def TorusScalar : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (μ : Fin N → kˣ →* ℂˣ) (ω : Fin N → 𝓀[k]ˣ →* ℂˣ), (∀ i, IsTameLift (μ i) (ω i)) →
    ∀ (x : leviK k fun _ : Fin N => Fin 1) (w : PiTensorProduct ℂ fun _ : Fin N => ℂ),
      piTensor (fun i => detRep (Fin 1) (μ i)) (x : Levi k fun _ : Fin N => Fin 1) w =
        (leviChar (fun _ : Fin N => Fin 1) ω (redLevi k _ x) : ℂ) • w

def IndSupp : Prop :=
  ∀ (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (P C : Subgroup G) (σ : Representation ℂ P W) (u : W), IsOpen (C : Set G) → (∀ p : P, (p : G) ∈ C → σ p u = u) →
    ∃ f : smoothPart (ind P σ), (∀ (p : P), ∀ c ∈ C, f.1.1 ((p : G) * c) = σ p u) ∧
      ∀ g : G, (¬ ∃ p : P, ∃ c ∈ C, g = (p : G) * c) → f.1.1 g = 0

def ProdVec : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W) (w : W), w ≠ 0 →
    ∀ (H : Set (Levi 𝓀[k] m)) (ψ : Levi 𝓀[k] m → ℂ), 1 ∈ H → ψ 1 = 1 →
    (∀ x : leviK k m, redLevi k m x ∈ H → ρ x w = ψ (redLevi k m x) • w) →
    ∃ F : IndSp e ρ, F ≠ 0 ∧ ∀ g : parahoric k e, parahoricProj k e g ∈ H →
      parInd e ρ g F = ψ (parahoricProj k e g) • F

def TwoComb : Prop :=
  ∀ (R : Type) [CommRing R] (a r s s' : ℕ) (d : Fin s → ℕ) (hd : ∑ j, d j = a) (d' : Fin s' → ℕ) (hd' : ∑ j, d' j = r)
    (h2 : ∑ j, Fin.append d d' j = a + r) (h : parab R (stdBlocks (Fin.append d d') h2)),
    ∃ (hp : (h : GL (Fin (a + r)) R) ∈ parab R (two (stdSum (rfl : a + r = a + r))))
      (h₁ : parab R (stdBlocks d hd)) (h₂ : parab R (stdBlocks d' hd')),
      leviProj R (two (stdSum (rfl : a + r = a + r))) ⟨h, hp⟩ = leviTwo R (Fin a) (Fin r) (h₁, h₂) ∧
      (∀ j, GeneralLinearGroup.det (leviProj R _ h (Fin.castAdd s' j)) = GeneralLinearGroup.det (leviProj R _ h₁ j)) ∧
      ∀ j, GeneralLinearGroup.det (leviProj R _ h (Fin.natAdd s j)) = GeneralLinearGroup.det (leviProj R _ h₂ j)

def ProdTwo : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a r s s' : ℕ) (d : Fin s → ℕ) (hd : ∑ j, d j = a) (d' : Fin s' → ℕ) (hd' : ∑ j, d' j = r)
    (h2 : ∑ j, Fin.append d d' j = a + r) (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) (θ' : Fin s' → 𝓀[k]ˣ →* ℂˣ)
    (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (A : Representation ℂ (GL (Fin a) k) X) (B : Representation ℂ (GL (Fin r) k) Y),
    HasTypeVec A (stdBlocks d hd) θ → HasTypeVec B (stdBlocks d' hd') θ' →
    HasTypeVec (prod₂ A B) (stdBlocks (Fin.append d d') h2) (Fin.append θ θ')

def JacOfType : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) (μ : Fin s → kˣ →* ℂˣ), (∀ a, IsTameLift (μ a) (θ a)) → HasTypeVec π e θ →
    ∃ y : Jacquet π (unipRad k e), y ≠ 0 ∧ ∀ x ∈ leviK k (m := fun a : Fin s => Fin (d a)),
      jacU e π x y = (∏ a, ((μ a (GeneralLinearGroup.det (x a)) : ℂˣ) : ℂ)) • y

def GrpFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) (μ : Fin s → kˣ →* ℂˣ), Function.Injective θ → (∀ a, IsTameLift (μ a) (θ a)) →
    ∀ a b, a ≠ b → UpperTheory.TNZ.res (μ a) ≠ UpperTheory.TNZ.res (μ b) ∧ UpperTheory.TNZ.cc μ a b = 1

def JacProd : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (G : UpperTheory.TNZ.Grp k N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    (∃ y : Jacquet π (unipRad k G.e), y ≠ 0 ∧ ∀ x ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)),
      jacU G.e π x y = (∏ a, ((G.μ a (GeneralLinearGroup.det (x a)) : ℂˣ) : ℂ)) • y) →
    UpperTheory.TNZ.IsTwSphProd π G.d G.hd G.μ

def BlockCount : Prop :=
  ∀ (β : Type) (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (θ : Fin s → β),
    Finset.univ.val.map (fun i => θ (blockOf d hd i)) = ∑ a, Multiset.replicate (d a) (θ a)

end UpperTheory.Gal.TypesAndIwahori
