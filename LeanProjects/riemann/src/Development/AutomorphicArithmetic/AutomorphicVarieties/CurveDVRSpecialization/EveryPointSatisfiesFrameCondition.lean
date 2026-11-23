import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af

namespace UpperTheory.V.Pr

instance (priority := high) fieldTorsionFree (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

def CoefIs : Prop := ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), Fr.IsCoef l c.O

def CoefEx : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (ka ka' : G L Ω →* (Qbar l)ˣ), Continuous ka → Continuous ka' →
    ∃ c₁ : Coef l, c.O ≤ c₁.O ∧ W.Large L c₁ ∧ (∀ g, (ka g).val ∈ c₁.O) ∧ (∀ g, (ka' g).val ∈ c₁.O) ∧
      ∃ f : ResidueField c.O →+* ResidueField c₁.O, ∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}

variable (σ M) in

structure IsKa (ι : Qbar l ≃+* ℂ) (n : ℕ) (ka : G L Ω →* (Qbar l)ˣ) : Prop where
  alg : Sd.IsAlgChar ι ka
  conj : ∀ s s' : G L Ω, galEmb ℚ L Ω s' = σ * galEmb ℚ L Ω s * σ⁻¹ → ka s * ka s' = cycBar L Ω l s ^ (1 - (n : ℤ))
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, ka s = 1
  ord : ∃ m : ℕ, ¬ l ∣ m ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := L) A, ka s ^ m = 1

structure CReal (k : GalLink η Ψ σ g₁ B M L Φ) (c₁ : Coef l) [Fr.IsCoef l c₁.O]
    (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ) (ka : G L Ω →* (Qbar l)ˣ) : Type 1 where
  n23 : n = 2 ∨ n = 3
  C₀ : ℕ
  ok : (Φ.ext f).Ok C₀
  big : (Φ.ext f).Big C₀
  le : c.O ≤ c₁.O
  hf : ∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b
  s : W.HidaSetting l L Ω
  V : s.Lev
  hV : V.S' = s.S
  r : W.Resid V.frame c₁.O n
  K : TwLink (Φ.ext f) r
  π_pr : ∀ g, K.π (V.pr g) = k.p0 g
  κ_pr : ∀ g, (K.κ (V.pr g)).val.1 = (ka g).val
  lam_j : ∀ (v : W.Vl l L) (g : Dec (F := L) (s.A v)), (k.j (K.e v) (K.lam v g)).1 = galEmb ℚ L Ω g
  A_pl : ∀ v : W.Vl l L, s.A v = k.pl (K.e v)
  v0 : r.V0ok
  v0M : ¬ (s.A s.v0).valuation (M : Ω) < 1
  B₀ : W.UniversalOrdinaryDeterminantRing r
  S : Fr.Space c₁.O (Φ.ext f) n

def CReal.T {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
    {n : ℕ} {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) : Setup (Φ.ext f) n :=
  ⟨R.n23, R.C₀, R.ok, R.big, Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero, R.V.frame, R.r, R.K, R.B₀, R.S⟩

end

structure LinkHyp {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l)
    (N e : ℕ) (η : G ℚ Ω →* ℤˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) : Prop where
  e_pos : 1 ≤ e
  dvd : l * N ∣ M
  M_pos : M ≠ 0
  ram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ η.ker → B'.valuation (M : Ω) < 1
  atl : B.valuation (l : Ω) < 1
  cc : Sd.IsCC σ

def KaOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), IsKa σ M ι 3 (cycBar L Ω l)⁻¹ ∧
    ∀ (K : Type) [Field K] [NumberField K] [Algebra K Ω], η.ker = galOf ℚ K Ω → ∀ κ : G K Ω →* (Qbar l)ˣ, Sd.IsTwist ι σ κ →
      ∃ ka : G L Ω →* (Qbar l)ˣ, IsKa σ M ι 2 ka ∧ ∀ (s : G L Ω) (s' : G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s'

def CRealEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (C₀ : ℕ), (n = 2 ∨ n = 3) → Φ.Ok C₀ → Φ.Big C₀ → c.O ≤ c₁.O →
    (∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b) → IsKa σ M ι n ka → (∀ g, (ka g).val ∈ c₁.O) →
    Nonempty (CReal k c₁ f n ka)

def DegEq : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.V → Φ.d = Module.finrank ℚ (W.Lp L) ∧ ¬ ∃ ζ : L, IsPrimitiveRoot ζ l

def EveryPointSatisfiesFrameCondition : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f n ka) (y : W.Point R.r), y.N4

def SeedPtOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f n ka), IsKa σ M ι n ka → ∀ (χ' : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ), ¬ l ∣ orderOf χ' →
    (∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Chr.Psi l e (Chr.dirG ℚ Ω ψ) s).val.1‖ < 1) →
    ∀ (m : ℕ), 2 ≤ m → ∀ r : G L Ω →* GL (Fin n) (Qbar l),
    Sd.IsSeed ι σ (fun i => ((cycBar ℚ Ω l ^ j * χ') ^ Fr.w n i).comp (galEmb ℚ L Ω))
      (fun i => (χ' ^ Fr.w n i).comp (galEmb ℚ L Ω)) (fun i => m * Fr.w n i) ka r →
    ∀ J, R.B₀.PT ι J → R.T.IdealSpecializationPoint J

def AutPtOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f n ka), IsKa σ M ι n ka → ∀ J, R.T.GoodPt J → R.B₀.arithmeticPointClassicality ι J → AutPt k n ι ka

def FinPtDown : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c c₁ : Coef l) (f : ResidueField c.O →+* ResidueField c₁.O), c.O ≤ c₁.O →
    (∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b) →
    ∀ (Φ : Fr.Frame l (ResidueField c.O)) (n : ℕ), FinPt c₁.O (Φ.ext f) n → FinPt c.O Φ n

def DimOf : Prop :=
  ∀ (O Λ B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing Λ] [Algebra O Λ] [CommRing B]
    [IsNoetherianRing B] (φ : Λ →+* B) (J : Ideal B) (m : ℕ), Nonempty (Λ ≃ₐ[O] MvPowerSeries (Fin m) O) →
    ((Ideal.Quotient.mk J).comp φ).Finite → (∀ a : Λ, a ≠ 0 → ∀ b : B, φ a * b ∈ J → b ∈ J) →
    ∀ Z ∈ J.minimalPrimes, qdim Z = ((1 + m : ℕ) : WithBot ℕ∞)

end UpperTheory.V.Pr

end
