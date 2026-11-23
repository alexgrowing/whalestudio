import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Aut
open scoped Pointwise

namespace UpperTheory.V.Pr

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

def upl (L : Type) [Field L] [NumberField L] [Algebra L Ω] : Subgroup (G ℚ Ω) where
  carrier := {s | ∀ x ∈ maximalRealSubfield L, s (algebraMap L Ω x) = algebraMap L Ω x}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x hx := by rw [AlgEquiv.mul_apply, hb x hx, ha x hx]
  inv_mem' {a} ha x hx := a.symm_apply_eq.2 (ha x hx).symm

variable {Ω} {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]

structure GalLink (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ)
    (L : Type) [Field L] [NumberField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField O)) where
  ab : IsAbelianGalois ℚ L
  gal : galOf ℚ L Ω = upl Ω L ⊓ η.ker
  unr : ∀ B' : ValuationSubring Ω, Ine (F := ℚ) B' ⊓ upl Ω L ≤ η.ker
  split : ∀ B' : ValuationSubring Ω, B'.valuation (M : Ω) < 1 → Dec (F := ℚ) B' ⊓ upl Ω L ≤ η.ker
  teich : ∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) B' ⊓ upl Ω L,
    barChar O Ψ s = 1 → Ψ s = 1
  p : upl Ω L →* Φ.Γ
  p_cont : Continuous p
  p_surj : Function.Surjective p
  p_ker : p.ker = (Subgroup.normalClosure {s : upl Ω L | ∃ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 ∧
    s.1 ∈ Ine (F := ℚ) B' ∧ η s = 1 ∧ barChar O Ψ s = 1}).topologicalClosure
  del : ∀ s, Φ.del (p s) = η s
  eps : ∀ s, Φ.eps (p s) = cycZ ℚ Ω l s
  psi : ∀ s, Φ.Ψ (p s) = barChar O Ψ s
  c : ∃ h : σ ∈ upl Ω L, p ⟨σ, h⟩ = Φ.c
  g0 : ∃ h : g₁ ∈ upl Ω L, p ⟨g₁, h⟩ = Φ.g0
  pl : Φ.V → ValuationSubring Ω
  pl_conj : ∀ v, ∃ γ : G ℚ Ω, η γ = 1 ∧ pl v = γ • B
  pl_all : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → ∃! v, ∃ u ∈ upl Ω L, B' = u • pl v
  j : ∀ v, Φ.Gv v →* upl Ω L
  j_cont : ∀ v, Continuous (j v)
  j_inj : ∀ v, Function.Injective (j v)
  j_range : ∀ v (s : upl Ω L), s ∈ (j v).range ↔ s.1 ∈ Dec (F := ℚ) (pl v)
  j_loc : ∀ v g, Φ.loc v g = p (j v g)
  j_ine : ∀ v g, g ∈ Φ.Iv v ↔ (j v g).1 ∈ Ine (F := ℚ) (pl v)
  dv : ∀ v, Φ.dv v = (upl Ω L).relIndex (Dec (F := ℚ) (pl v))
  mu : ∀ v, ∃ g, cycMod ℚ Ω l 1 (j v g) ≠ 1

def GalLink.p0 {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ)
    (s : G L Ω) : Φ.G0 :=
  have h : galEmb ℚ L Ω s ∈ upl Ω L ⊓ η.ker := k.gal ▸ galEmb_mem ℚ L Ω s
  ⟨k.p ⟨galEmb ℚ L Ω s, h.1⟩, (k.del _).trans h.2⟩

def SeedClause (c : Coef l) (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ : G ℚ Ω) (L : Type) [Field L] [NumberField L] [Algebra L Ω] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω) (N w : ℕ) (χ' η' θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    Sd.FieldPairCharacterTripleConditions K L σ N w χ' η' θ j ∧ χ' ≠ η' ∧ ¬ l ∣ orderOf χ' ∧ (∀ s, (η' s).val = (((η s).val : ℤ) : Qbar l)) ∧
    (∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Ψ s).val.1‖ < 1) ∧ ¬ (l : ℤ) ∣ discr K

def HasFrame (c : Coef l) [CharP (ResidueField c.O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω)
    (M : ℕ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : Algebra L Ω) (g₁ : G ℚ Ω)
    (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ), Nonempty (GalLink η Ψ σ g₁ B M L Φ) ∧ Φ.Ok C₀ ∧ Φ.Big C₀ ∧
      SeedClause c η Ψ σ L

def HostFrameEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l]
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ →
  ∀ σ : G ℚ Ω, IsCC σ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 →
    HasFrame c (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ B (l * N)

def GdFrameEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ)
    (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ) (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 →
    HasFrame c D.η D.Ψ D.cc B (l * N * (discr K).natAbs)

end UpperTheory.V.Pr

end
