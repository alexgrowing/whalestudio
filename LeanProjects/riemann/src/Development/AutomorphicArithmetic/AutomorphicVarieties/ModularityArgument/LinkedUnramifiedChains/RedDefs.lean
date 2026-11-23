import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.LinkedRig
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg

namespace UpperTheory.V.J

section Space

variable {l : ℕ} [Fact l.Prime] {c : Coef l} {F : Fr.Frame l (ResidueField c.O)} {n : ℕ} (S : Fr.Space c.O F n)

def IntPt (ξ : S.A →ₐ[c.O] Qbar l) : Prop := (∀ a, ‖ξ a‖ ≤ 1) ∧ ∀ b ∈ S.mB, ‖ξ (S.inc b)‖ < 1

def VPt (ξ : S.A →ₐ[c.O] Qbar l) : Prop := IntPt S ξ ∧ ∀ g i j, i ≠ j → ‖ξ (S.u.r g i j)‖ < 1

abbrev ptRep (ξ : S.A →ₐ[c.O] Qbar l) : Fr.NRep F n (Qbar l) := S.u.map (ξ : S.A →+* Qbar l)

def FixTan (ξ : S.A →ₐ[c.O] Qbar l) : Submodule (Qbar l) (S.A →ₗ[c.O] Qbar l) :=
  PtDer ξ (Qbar l) ⊓
    { carrier := {D | ∀ v i, ∀ g ∈ F.Iv v, D (S.u.ψ v i g : S.A) = 0}
      add_mem' := fun h h' v i g hg => by rw [LinearMap.add_apply, h v i g hg, h' v i g hg, add_zero]
      zero_mem' := fun _ _ _ _ => rfl
      smul_mem' := fun a D h v i g hg => by rw [LinearMap.smul_apply, h v i g hg, smul_zero] }

def Over {x : Ideal S.A} (L : S.Loc x) (q : Ideal S.A) (Q : Ideal L.R) : Prop :=
  Q.IsPrime ∧ L.im Q = q ∧ Q ∈ (q.map (L.ι : S.A →+* L.R)).minimalPrimes ∧ ringKrullDim (L.R ⧸ Q) = 1

def DenseB (M : Ideal S.B) (Gd : (S.B →ₐ[c.O] Qbar l) → Prop) : Prop :=
  ∀ Z : Ideal S.B, Z.IsPrime → M ≤ Z → ringKrullDim (S.B ⧸ Z) ≤ ((1 + n * F.d : ℕ) : WithBot ℕ∞) ∧
    (ringKrullDim (S.B ⧸ Z) = ((1 + n * F.d : ℕ) : WithBot ℕ∞) → ∀ b ∉ Z, ∃ y : S.B →ₐ[c.O] Qbar l, Z ≤ RingHom.ker y ∧ Gd y ∧ y b ≠ 0)

end Space

def RedAbs : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
    ∀ (S : Fr.Space c.O F n) (M : Ideal S.B) (Gd : (S.B →ₐ[c.O] Qbar l) → Prop), AllGood S M → DenseB S M Gd →
    (∀ ξ : S.A →ₐ[c.O] Qbar l, VPt S ξ → S.u.TI (RingHom.ker ξ) → M ≤ RingHom.ker (ξ.comp S.inc) → Gd (ξ.comp S.inc) →
      Module.rank (Qbar l) (FixTan S ξ) ≤ 1) →
    ∀ ξ : S.A →ₐ[c.O] Qbar l, IntPt S ξ → S.u.TI (RingHom.ker ξ) → ∀ b ∈ M, ∃ s : S.A, ξ s ≠ 0 ∧ s * S.inc b = 0

def WtEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∃ h : R.s.Wt 3, h.Incr ∧ ∀ x : R.B₀.Pt, x.Good h → Th.Free R.V.frame fun v => x.psi v

def NiceAt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → ∀ J, R.B₀.arithmeticPointClassicality ι J → ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ →
      R.S.u.TI (RingHom.ker ξ) → ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → J ≤ RingHom.ker x → x.Good h →
      (Th.Free R.V.frame fun v => x.psi v) →
      Th.NiceAPt ι x (R.K.tw (ptRep R.S ξ)).toHomUnits ∧ ∀ v, x.psi v = R.K.twψ (ptRep R.S ξ) v

def Red : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → Function.Surjective φ → ∀ J, AllGood R.S (J.map φ) → R.T.DimT J → R.B₀.Dense J →
      R.B₀.arithmeticPointClassicality ι J → ∀ ξ : R.S.A →ₐ[c₁.O] Qbar l, IntPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
      ∀ a ∈ J, ∃ s : R.S.A, ξ s ≠ 0 ∧ s * R.S.inc (φ a) = 0

end UpperTheory.V.J

end
