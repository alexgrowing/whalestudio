import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyClauseStatement

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut

namespace UpperTheory.V.UnitaryThreeInertia

def HostVanE : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  F.VanE

def HostXpp : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ q : ℕ, XData l ψ q → ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  F.Xpp

def HostRigid : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∀ (ι : Qbar l ≃+* ℂ) (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r →
    (BPrime K ι fun s => (r (toGS Ω _ s)).mat) → F.Rigid r

def HostNumber : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K → ∃ C : ℕ,
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
  ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
  ∀ (ι : Qbar l ≃+* ℂ) (g₁ : Gam Ω S), F.Marked g₁ → ∃ φ : Gam Ω S,
    (∀ r : Gam Ω S →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r → TypeI F.η r → (BPrime K ι fun s => (r (toGS Ω _ s)).mat) →
      (r φ).mat.trace ≠ (F.rz (PadicAlgCl l) φ).mat.trace) ∧
    ∀ (n : ℕ) (r : Fin n → (Gam Ω S →* GG 3 (PadicAlgCl l))),
      (∀ i, F.IsCharZeroPt g₁ (r i) ∧ TypeI F.η (r i) ∧ BPrime K ι fun s => (r i (toGS Ω _ s)).mat) →
      (∀ i i', MatIso F.η.ker (mats (r i)) (mats (r i')) → i = i') →
      (∑ i, vl1 l ((r i φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace)) * Real.log l ≤ ((l : ℝ) * N * e) ^ C

end UpperTheory.V.UnitaryThreeInertia

end
