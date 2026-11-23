import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Adelise
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RW

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial CongruenceSubgroup UpperHalfPlane
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.GalN.V
open scoped MatrixGroups ModularForm ComplexConjugate

namespace UpperTheory.V.Z.Sym.Unl

abbrev cj {N : ℕ} (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) : DirichletCharacter ℂ N := χ.ringHomComp σ.toRingHom

def Cj (k N : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, ∃ f' : CuspForm (Gamma1 N) (k : ℤ), HasChar k (cj σ χ) f' ∧ ∀ n, 1 ≤ n → coef f' n = σ (coef f n)

def UnitFamC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (N : ℕ) [NeZero N], 3 ≤ N → ¬ l ∣ N → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    ∃ f : (ZMod N)ˣ → ModularForm (Gamma1 N) (k : ℤ), IsFam k f ∧ (∀ a, IntQ ι (f a)) ∧ (∀ a, VanOff N k (f a)) ∧
      ‖ι.symm (coef (f 1) 0)‖ = 1 ∧ (∀ a, a ≠ 1 → a ≠ -1 → coef (f a) 0 = 0) ∧
      ∀ σ : ℂ ≃+* ℂ, ∃ f' : (ZMod N)ˣ → ModularForm (Gamma1 N) (k : ℤ), IsFam k f' ∧ (∀ a, VanOff N k (f' a)) ∧
        ∀ a n, coef (f' a) n = σ (coef (f a) n)

def EisCj : Prop :=
  ∀ (N : ℕ) [NeZero N], 1 < N → ∀ σ : ℂ ≃+* ℂ, ∃ s : (ZMod N)ˣ, (∀ b : ZMod N, σ (ZMod.stdAddChar b : ℂ) = (ZMod.stdAddChar ((s : ZMod N) * b) : ℂ)) ∧
    ∀ k : ℕ, 3 ≤ k → ∀ (a : (ZMod N)ˣ) (n : ℕ), coef (eisFun N k ((s * a : (ZMod N)ˣ) : ZMod N)) n = σ (coef (eisFun N k a) n)

def UnitFormC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (N : ℕ) [NeZero N], 3 ≤ N → ¬ l ∣ N → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    ∀ χ : DirichletCharacter ℂ N, χ (-1) = (-1) ^ k →
      ∃ f : ModularForm (Gamma1 N) (k : ℤ), HasChar k χ f ∧ IntQ ι f ∧ VanOff N k f ∧ coef f 0 = 1 ∧
        ∀ σ : ℂ ≃+* ℂ, ∃ f' : ModularForm (Gamma1 N) (k : ℤ), HasChar k (cj σ χ) f' ∧ VanOff N k f' ∧ ∀ n, coef f' n = σ (coef f n)

def PrimCj : Prop := ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (σ : ℂ ≃+* ℂ), χ.IsPrimitive → (cj σ χ).IsPrimitive

def ConstCj : Prop :=
  ∀ (N k : ℕ) [NeZero N], 1 < N → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ (σ : ℂ ≃+* ℂ) (c c' : ℂ),
    2 * gaussSum χ⁻¹ ZMod.stdAddChar * c = ∑ a : ZMod N, χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ) →
    2 * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar * c' = ∑ a : ZMod N, (cj σ χ)⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ) → c' = σ c

def EigLiftC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N k : ℕ) [NeZero N], 1 ≤ k → ∀ (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) (k : ℤ)), HasChar k χ f → Cj k N χ f → IntQ ι f → ‖ι.symm (coef f 1)‖ = 1 → ∀ a : ℕ → ℂ,
    (∀ p : ℕ, p.Prime → ‖ι.symm (a p)‖ ≤ 1 ∧ ∀ n : ℕ, 1 ≤ n →
      ‖ι.symm (coef f (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0) - a p * coef f n)‖ < 1) →
    ∃ g : Eigenform k N χ, Cj k N χ g.f ∧ ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - a p)‖ < 1

def PropEC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M w : ℕ) φ θ χ, EDat l M w φ θ χ → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ (-1) = (-1) ^ k →
    ∃ g : Eigenform k (M * w) χ, Cj k (M * w) χ g.f ∧
      ∀ p : ℕ, p.Prime → ‖ι.symm (g.a p - (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)))‖ < 1

def ConjEig : Prop :=
  ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ), Cj k N χ g.f → ∀ σ : ℂ ≃+* ℂ,
    ∃ g' : Eigenform k N (cj σ χ), ∀ n, 1 ≤ n → g'.a n = σ (g.a n)

def SelfAdj : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ (g : Eigenform k N χ) (p : ℕ), p.Prime → ¬ p ∣ N →
    conj (g.a p) * χ (p : ZMod N) = g.a p

def BadAbs : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ (g : Eigenform k N χ) (p : ℕ), p.Prime → p ∣ N →
    ‖g.a p‖ ^ 2 = (p : ℝ) ^ (k - 1)

def SqrtFlip : Prop := ∀ p : ℕ, p.Prime → ∃ σ : ℂ ≃+* ℂ, σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ)

def HalfAlg : Prop :=
  ∀ (p m : ℕ) (a x α β : ℂ) (σ : ℂ ≃+* ℂ), 2 ≤ p → ‖x‖ = 1 → ‖σ x‖ = 1 → σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ) →
    conj a * x = a → conj (σ a) * σ x = σ a → α + β = a → α * β = x * (p : ℂ) ^ m → ‖α‖ ^ 2 ≠ (p : ℝ) * ‖β‖ ^ 2

def GoodHalf : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ g : Eigenform k N χ, Cj k N χ g.f →
    ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ α β : ℂ, α + β = g.a p → α * β = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) → ‖α‖ ^ 2 ≠ (p : ℝ) * ‖β‖ ^ 2

def TieS : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r →
    ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ B, π.HasSat w B → FrobEig ι r w (algSat 2 (normV w) B)

def TieU : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r →
    ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (n : ℕ) (lam : ℂ), n ≠ 0 → lam ≠ 0 → HasU w (π.locRep w) n lam →
    ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ t : G F Ω, IsFrob A (normV w) t →
      ∃ α : Qbar l, (r t⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot α ∧ ‖ι α‖ = ‖lam‖

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def NoHalf (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    ∀ s : G F Ω, IsFrob A (normV w) s → ∀ α β : Qbar l, (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot α →
      (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot β → ‖ι α‖ ^ 2 ≠ ((normV w : ℕ) : ℝ) * ‖ι β‖ ^ 2

end

def TwOk : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (δ : G F Ω →* (Qbar l)ˣ), (NoHalf ι r → NoHalf ι (tw r δ)) ∧ (RW ι r → RW ι (tw r δ))

def AdUnl : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)), RW ι r → NoHalf ι r → Unlinked (ad0 r)

def HalfOf : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k N : ℕ) [NeZero N], 3 ≤ k →
    ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → ∀ g : Eigenform k N χ, Cj k N χ g.f →
    ∀ (ξ : G ℚ Ω →* (Qbar l)ˣ) c m a π r, OrdForm ι ξ (1 - (k : ℤ)) c m a π r →
    (∀ w : Pl ℚ, HasU w (π.locRep w) (N.factorization (normV w)) (g.a (normV w))) →
    (∀ w : Pl ℚ, ¬ normV w ∣ N → ∃ B, π.HasSat w B ∧ ((algSat 2 (normV w) B).map fun b => X - C b).prod =
      X ^ 2 - C (g.a (normV w)) * X + C (χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1))) → NoHalf ι r

end UpperTheory.V.Z.Sym.Unl
