import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.MuRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr

namespace UpperTheory.V.J

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r}

def IrrPt (x : B.Pt) : Prop := ∃ ρ : G L Ω →* GL (Fin n) (Qbar l), Continuous ρ ∧ x.IsRep ρ ∧ IsIrr ρ

variable (B) in

def Num (Λ : LamObj r) (J : Ideal B.B) : Prop :=
  ∃ (M : Type) (_ : AddCommGroup M) (_ : Module B.B M) (_ : Module Λ.Λ M) (h : Dat (Λ.toPair B.u) J M)
    (e : Module.End Λ.Λ M), Z.Desc.V0.Idem B.B e ∧
    ∀ (x y : B.Pt) (w : s.Wt n), J ≤ RingHom.ker x → J ≤ RingHom.ker y → x.Arith w → y.Good w → IrrPt x → IrrPt y →
      1 ≤ Z.Desc.V0.muE (Λ.toPair B.u) M h.hs e x ∧
        Z.Desc.V0.muE (Λ.toPair B.u) M h.hs e x ≤ Z.Desc.V0.muE (Λ.toPair B.u) M h.hs e y

variable (B) in

def UnrAt (J : Ideal B.B) : Prop :=
  ∀ (x : B.Pt) (w : s.Wt n), J ≤ RingHom.ker x → x.Arith w → IrrPt x → ∀ δ ∈ PtDer x (Qbar l), (∀ a ∈ J, δ a = 0) →
    (∀ v i, ∀ g ∈ V.frame.Iv v, δ (B.u.ψ v i g : B.Bˣ) = 0) → δ = 0

end U

def ModN : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (r : Resid V.frame c.O 3), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (ι : Qbar l ≃+* ℂ),
      ∃ J : Ideal B.B, B.Modular ι J Λ ∧ Num B Λ J

def IrrOpen : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
    (J : Ideal B.B), 1 ≤ n → B.arithmeticPointPurity ι J → ∀ x : B.Pt, IrrPt x →
    ∃ b₀ : B.B, x b₀ ≠ 0 ∧ ∀ (y : B.Pt) (w : s.Wt n), J ≤ RingHom.ker y → y.Good w → y b₀ ≠ 0 → IrrPt y

def LamDer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (x : B.Pt)
    (m : ℕ), Nonempty (Λ.Λ ≃ₐ[c.O] MvPowerSeries (Fin m) c.O) → ∀ δ ∈ PtDer x (Qbar l),
    (∀ v i, ∀ g ∈ V.frame.Iv v, δ (B.u.ψ v i g : B.Bˣ) = 0) → ∀ a, δ (Λ.toPair B.u a) = 0

def Unr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
    (ι : Qbar l ≃+* ℂ) (J : Ideal B.B) (m : ℕ), 1 ≤ n → Nonempty (Λ.Λ ≃ₐ[c.O] MvPowerSeries (Fin m) c.O) →
    B.Dense J → B.arithmeticPointPurity ι J → Num B Λ J → UnrAt B J

def Det : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fr.IsCoef l O]
    (F : Fr.Frame l (ResidueField O)) (n : ℕ) (S : Fr.Space O F n) (ξ : S.R →ₐ[O] O), ∀ D ∈ PtDer ξ O,
    (∀ g i j, D (S.ρ.r g i j) = 0) → (∀ v i g, D (S.ρ.ψ v i g : S.Rˣ) = 0) → D = 0

def Tor : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fr.IsCoef l O]
    (F : Fr.Frame l (ResidueField O)) (S : Fr.Space O F 3) (ξ : S.R →ₐ[O] O), S.ρ.TI (RingHom.ker ξ) →
    ∀ D ∈ PtDer ξ O, ∀ D' ∈ PtDer ξ O, (∀ a ∈ S.B, D a = 0) → (∀ a ∈ S.B, D' a = 0) → ¬ LinearIndependent O ![D, D']

def AbsGood : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fr.IsCoef l O]
    [Algebra ℤ_[l] O] (F : Fr.Frame l (ResidueField O)) (T₂ : Setup F 2) (T₃ : Setup F 3) (J₂ : Ideal T₂.B.B)
    (J₃ : Ideal T₃.B.B), T₂.ModIn J₂ → T₃.ModIn J₃ →
    ∃ φ, T₃.IsPhi φ ∧ Function.Surjective φ ∧ AllGood T₃.S (J₃.map φ)

section Pt

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O} {n : ℕ}
  {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) (ξ : R.S.R →ₐ[c₁.O] c₁.O)

def ptOf : R.B₀.Pt := (Algebra.ofId c₁.O (Qbar l)).comp (ξ.comp (R.S.B.val.comp φ))

def ptA : R.S.A →ₐ[c₁.O] Qbar l := (Algebra.ofId c₁.O (Qbar l)).comp (ξ.comp R.S.A.val)

end Pt

def End : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l)
    (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ)
    (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η Ψ σ g₁ B M L Φ) (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka) (φ : R.B₀.B →ₐ[c₁.O] R.S.B), R.T.IsPhi φ → Function.Surjective φ →
    ∀ (J : Ideal R.B₀.B) (ξ : R.S.R →ₐ[c₁.O] c₁.O) (w : R.s.Wt 3), UnrAt R.B₀ J → R.S.ρ.TI (RingHom.ker ξ) →
    (ptOf R φ ξ).Arith w → IrrPt (ptOf R φ ξ) →
    (∀ a ∈ J, ∃ s : R.S.A, ptA R ξ s ≠ 0 ∧ s * R.S.inc (φ a) = 0) →
    ∀ D ∈ PtDer ξ c₁.O, ∀ D' ∈ PtDer ξ c₁.O, (∀ v i, ∀ g ∈ (Φ.ext f).Iv v, D (R.S.ρ.ψ v i g : R.S.Rˣ) = 0) →
      (∀ v i, ∀ g ∈ (Φ.ext f).Iv v, D' (R.S.ρ.ψ v i g : R.S.Rˣ) = 0) → ¬ LinearIndependent c₁.O ![D, D']

end UpperTheory.V.J

end
