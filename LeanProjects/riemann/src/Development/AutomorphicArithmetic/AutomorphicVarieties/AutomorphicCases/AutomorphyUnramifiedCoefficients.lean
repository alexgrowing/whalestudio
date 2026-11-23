import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

namespace UpperTheory.V.Aut

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)

def FinA (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : D.ULoc) (S : D.Ring U g₁), Module.Finite c.O (weightZeroSubalgebra c.O S.r.hom)

def AutB [IsCMField K] (ι : Qbar l ≃+* ℂ) (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : D.ULoc) (S : D.Ring U g₁) (ξ : entAlg c.O S.r.hom →ₐ[c.O] PadicAlgCl l)
    (r : G ℚ Ω →* GG 3 (PadicAlgCl l)) (hr : HasMult D.η r), IsPush ξ S.r.hom r → TypeI D.η r → D.IsAutI ι r hr

def LemW (ι : Qbar l ≃+* ℂ) (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : D.ULoc) (S : D.Ring U g₁) (ξ : entAlg c.O S.r.hom →ₐ[c.O] PadicAlgCl l)
    (r : G ℚ Ω →* GG 3 (PadicAlgCl l)), IsPush ξ S.r.hom r → TypeII D.η r → (∀ g ∈ D.η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → D.IsModular ι W

def AutomorphyUnramifiedCoefficients : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ),
    eO l c.O = 1 → ∀ ι : Qbar l ≃+* ℂ, ∃ g₁ : G ℚ Ω, D.Marked g₁ ∧ FinA D g₁ ∧ AutB D ι g₁ ∧ LemW D ι g₁

end UpperTheory.V.Aut

end
