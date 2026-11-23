import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

namespace GlobalTheory.HTW

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

def TateDualRule {G : Type}
    [Group G]
    [TopologicalSpace G]
    {Qp K₀ K : Type}
    [Field Qp]
    [Field K₀]
    [Field K]
    [Algebra Qp K₀]
    [Algebra Qp K]
    [Algebra K₀ K]
    [IsScalarTower Qp K₀ K]
    {B BdR : Type}
    [CommRing B]
    [CommRing BdR]
    [Algebra Qp B]
    [Algebra K₀ B]
    [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR]
    [Algebra K₀ BdR]
    [Algebra K BdR]
    [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR]
    [IsScalarTower Qp K₀ BdR]
    [TopologicalSpace Qp] (PD : PeriodData G Qp K₀ K B BdR) : Prop :=
  ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
    [Algebra O LL], GoodO (Qp := Qp) LL O →
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsCrys PD A.ρ → IsDual1 PD A.ρ A'.ρ P →
    IsCrys PD A'.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), multV PD A'.ρ τ (-a - 1) = multV PD A.ρ τ a

end GlobalTheory.HTW

namespace GlobalTheory.Published

open Formalism.BasicNotions Formalism.BasicNotions.Loc

def TateDualCrystalline : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ K : FinExt l, GlobalTheory.HTW.TateDualRule (P.PD K)

theorem TateDualCrystalline.rule (h : TateDualCrystalline) {l : ℕ} [Fact l.Prime] {P : LocPrime l}
    {AI : LocAinf l P} (T : LocTied l P AI) (K : FinExt l) : GlobalTheory.HTW.TateDualRule (P.PD K) :=
  h l P AI ⟨T⟩ K

end GlobalTheory.Published
