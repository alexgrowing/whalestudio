import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerUnitAndQFactor

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def GCoordProp (W : LocWach PD LL O v n) : Prop :=
  ∀ (T : LocLat G Qp LL O) (i : ZMod n) (h c : ℕ) {r : ℕ} (e e' : Fin r → W.DD T)
    (_ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T i e) (P Z : Matrix (Fin r) (Fin r) (PowerSeries O)),
    (∀ k, Formalism.MainNotions.LiftingTheory.qp W ^ h • W.φD T (e' k) = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (P m k) • e m) →
    PowerSeries.constantCoeff W.π₀₁ = 0 →
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) →
    ∀ (k : Fin r), Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k ∈ W.N T →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k) →
      ∀ (a : Fin r → PowerSeries O),
        Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a l) • e l →
        ∀ l, (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l = (P * Z) l k

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord
