import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.NewtonThorneSym
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Base

namespace UpperTheory.V.Z.Bc

def AdAutK : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IsAutR ι ρ → IrrOpen ρ → IsAutQ ι (tw (ad0 ρ) (cycBar ℚ Ω l)⁻¹)

def Sym3AutK : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)),
    Continuous ρ → IsAutR ι ρ → IrrOpen ρ → IsIrr (sym3 ρ) → IsAutQ ι (sym3 ρ)

def SeedSymK : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c →
    ∀ (N w : ℕ) (ξ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w ξ → ξ c = -1 → (∃ s, ¬ Cong (ξ s ^ 2) 1) →
    ∀ B : ℕ, ∃ k ≥ B, k ≡ 1 [MOD l - 1] ∧ ∃ ρ, EisRep ι ξ θ k ρ ∧ IrrOpen ρ ∧ IrrOpen (sym3 ρ) ∧ IsAutQ ι (sym3 ρ)

def UpAll : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
    Module.finrank F E = 2 → ∀ (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutR ι r →
      IsIrr (r.comp (galEmb F E Ω)) → IsAutC ι (r.comp (galEmb F E Ω))

theorem UpAll.autQ (h : UpAll) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ}
    (hn : 1 ≤ n) {r : G ℚ Ω →* GL (Fin n) (Qbar l)} (ha : IsAutR ι r) : IsAutQ ι r := by
  intro hr K _ _ _ i _ _ hK hirr
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact h ℚ K Ω l ι hK n hn r hr ha hirr

theorem adAutK_of (h : UpAll) (ha : Lit.AdAutQ) : AdAutK :=
  fun Ω _ _ _ l _ ι ρ h1 h2 h3 => h.autQ (by norm_num) (ha Ω l ι ρ h1 h2 h3)

theorem sym3AutK_of (h : UpAll) (ha : Lit.SymmetricCubeAutomorphyOverRationals) : Sym3AutK :=
  fun Ω _ _ _ l _ ι ρ h1 h2 h3 h4 => h.autQ (by norm_num) (ha Ω l ι ρ h1 h2 h3 h4)

structure HypothesesZ : Prop where
  af : Af.Hypotheses₂
  eg : PropEG
  up : UpSol

end UpperTheory.V.Z.Bc
