import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.TnOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu

def GoodAt {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (K' L : IntermediateField ℚ Ω) [NumberField L]
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∀ p : ℕ, p.Prime → (∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup) ∨
    (p ≠ l ∧ ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ s ∈ Ine (F := L) A, resQ L s ∈ K'.fixingSubgroup ∧ ρ (resQ L s) = 1)

def GoodOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ T : Tower D), D.Good → T₀.Le T →
    ∀ (K' : IntermediateField ℚ Ω), (∀ p ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup) →
    (∀ g : G T₀.F Ω, resQ T₀.F g ∉ K'.fixingSubgroup → T₀.rb wAl g = -1) →
    ∀ (w : ℕ) (θ : G ℚ Ω →* (Qbar l)ˣ), w.Prime → T₀.Splits w → (∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) →
    ∀ (k : ℕ) (g0 : G ℚ Ω) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (c₁ : Coef l) (h : c.O ≤ c₁.O) (ρ₁ : G ℚ Ω →* M2 c₁.O)
      (x : ValuationSubring Ω → c₁.O), Mod4 D T₀.pr θ k g0 ρ h ρ₁ x → GoodAt K' T.L ρ

def PolOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω) [NumberField K'], Module.finrank ℚ K' = 2 → IsTotallyComplex K' →
    ∀ ρ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ → IsAutR ι ρ →
    ∀ (g0 : G ℚ Ω) (m : ℕ) (c₁ : Coef l) (κ : G K' Ω →* (Qbar l)ˣ) (τ : G ℚ Ω →* M2 c₁.O) s, TauDat ι K' g0 m c₁ τ s κ →
    Af.Sol.Pol ι (Af.tw (ρ.comp (resQ K')) κ)

end UpperTheory.V.Cu

end
