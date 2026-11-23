import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryThreePoint

noncomputable section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr

namespace UpperTheory.V.J

def TanA : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
    (ξ : R.S.R →ₐ[c₁.O] c₁.O) (r : G L Ω →* GL (Fin 3) (Qbar l)),
    (∀ s, (r s).val = (R.S.ρ.r (k.p0 s)).map fun a => (ξ a).1) → IsIrr r →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ξ (R.S.ρ.ψ v i g).val).1 = (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val.1) →
    ∀ v : Φ.V, PotCrysAt r (k.pl v) → ∀ i j,
    (∀ g : Φ.Gv v, (ξ (R.S.ρ.ψ v i g).val).1 = (ξ (R.S.ρ.ψ v j g).val).1 * (cycBar ℚ Ω l (k.j v g).1 : Qbar l)) →
    ∃ D ∈ PtDer ξ c₁.O, ∃ D' ∈ PtDer ξ c₁.O, (∀ v i, ∀ g ∈ (Φ.ext f).Iv v, D (R.S.ρ.ψ v i g : R.S.Rˣ) = 0) ∧
      (∀ v i, ∀ g ∈ (Φ.ext f).Iv v, D' (R.S.ρ.ψ v i g : R.S.Rˣ) = 0) ∧ LinearIndependent c₁.O ![D, D']

def OpenEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → Φ.Big C₀ → SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [Module.Finite c.O A],
    ∃ (c₁ : Coef l) (_ : Fr.IsCoef l c₁.O) (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
      (Λ : LamObj R.r) (J : Ideal R.B₀.B) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) (m : ℕ),
      (∀ x ∈ A, x ∈ c₁.O) ∧ Large L c₁ ∧ IsKa σ M ι 3 (cycBar L Ω l)⁻¹ ∧ R.B₀.Modular ι J Λ ∧ Num R.B₀ Λ J ∧
      Nonempty (Λ.Λ ≃ₐ[c₁.O] MvPowerSeries (Fin m) c₁.O) ∧ R.T.IsPhi φ ∧ Function.Surjective φ ∧ AllGood R.S (J.map φ) ∧
      R.T.DimT J

def XiEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
    (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] [IsLocalHom (algebraMap c.O A)],
    (∀ x ∈ A, x ∈ c₁.O) → ∀ ρ : Fr.NRep Φ 3 A, IsLiftA c.O ρ →
    ∃ ξ : R.S.R →ₐ[c₁.O] c₁.O, (∀ g i j, (ξ (R.S.ρ.r g i j)).1 = A.val (ρ.r g i j)) ∧
      ∀ v i g, (ξ (R.S.ρ.ψ v i g).val).1 = A.val (ρ.ψ v i g).val

def XiTI : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
    (ξ : R.S.R →ₐ[c₁.O] c₁.O) (r : G L Ω →* GL (Fin 3) (Qbar l)),
    (∀ s, (r s).val = (R.S.ρ.r (k.p0 s)).map fun a => (ξ a).1) → IsIrr r →
    R.S.ρ.TI (RingHom.ker ξ) ∧ IntPt R.S (ptA R ξ) ∧ R.S.u.TI (RingHom.ker (ptA R ξ))

def XiArith : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹), IsKa σ M ι 3 (cycBar L Ω l)⁻¹ →
    ∀ φ : R.B₀.B →ₐ[c₁.O] R.S.B, R.T.IsPhi φ → ∀ (ξ : R.S.R →ₐ[c₁.O] c₁.O) (r : G L Ω →* GL (Fin 3) (Qbar l)),
    (∀ s, (r s).val = (R.S.ρ.r (k.p0 s)).map fun a => (ξ a).1) → IsIrr r →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ξ (R.S.ρ.ψ v i g).val).1 = (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val.1) →
    (∃ w, (ptOf R φ ξ).Arith w) ∧ IrrPt (ptOf R φ ξ)

end UpperTheory.V.J

end
