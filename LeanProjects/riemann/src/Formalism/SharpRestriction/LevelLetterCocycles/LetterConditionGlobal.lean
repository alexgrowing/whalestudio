import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

def LetterConditionLocal (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (y : ℕ), 1 ≤ y →
  ∀ (dop : W.DD T →ₗ[O] W.DD T), (∀ z, W.π₀ • dop z = W.γ T z - z) →
  ∀ (cc : ℤ → O), (∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1) →
  ∀ X : Finset ℤ,
    (∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T.ρ τ a → 1 ≤ j → j ≤ y →
      a + (j : ℤ) ∈ X) →
    ∀ z : W.DD T, Formalism.MainNotions.LiftingTheory.InNΔi W T i (qA W ^ y • z) →
      Formalism.MainNotions.LiftingTheory.InNΔi W T i
        (Polynomial.aeval dop (∏ x ∈ X, (Polynomial.X - Polynomial.C (cc x))) z)

def LetterConditionGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    LetterConditionLocal ((HW l).W K s LL h)

end Formalism.MainNotions.N
