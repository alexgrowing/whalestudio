import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

theorem rhoC_holds (hR : Ring9 W) (c : ZMod n) (s : ℕ) (a : O) :
    rhoL hR c s (PowerSeries.C a) =
      PowerSeries.C (algebraMap LL (KsW W s) (algebraMap O LL a)) := by
  ext k ζ
  have hC : (PowerSeries.C a : PowerSeries O) = algebraMap O (PowerSeries O) a := by
    rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have h1 : PowerSeries.coeff k (rhoL hR c s (PowerSeries.C a)) ζ =
      PowerSeries.coeff k (rhoZ W c ζ ((baseIdOf hR).ι (PowerSeries.C a))) := by
    have h := congrArg (PowerSeries.coeff k) (map_eval_rhoL hR c s (PowerSeries.C a) ζ)
    rw [PowerSeries.coeff_map] at h
    exact h
  rw [h1, hC, AlgHom.commutes, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.coeff_C,
    PowerSeries.coeff_C]
  split_ifs <;> rfl

end Formalism.MainNotions.N.Ln03.Pf
