import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recSeam HostTie AnTie)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg LatWithBasis)

def JetOpWeyl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b)
    (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n →
    ∀ (M : ι → Submodule (𝓞 K) (Fin a → K)) (MW : ι → Submodule (𝓞 K) (Fin b → K)),
      (∀ τ, Submodule.IsLattice K (M τ)) → (∀ τ, Submodule.IsLattice K (MW τ)) → LatWithBasis w M 1 → LatWithBasis w MW 1 →
      ∀ (c : K) (J : (DVar ι a b →₀ ℕ) → K), (∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) →
        ∀ F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)),
          c • jetOp lam lam' J n F ∈ localization₂ w.asIdeal (delK lam' fun τ => dualFr (MW τ))

def LatticeFactsAt {X : Fields} (A : Amb X) : Prop := ∀ a b : ℕ, Even a → Even b → A.LaHyp a b ∅ ∧ A.ESmooth a b

def FamilyFacts (D : D7) (EX : ErrX D) {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  HostTie EX → AnTie D δ χ cD → B.VecP χ ∧ B.IntP χ ∧ LatticeFactsAt (ambOf (recSeam D) B χ cD)

end GlobalTheory.ColPeriod
