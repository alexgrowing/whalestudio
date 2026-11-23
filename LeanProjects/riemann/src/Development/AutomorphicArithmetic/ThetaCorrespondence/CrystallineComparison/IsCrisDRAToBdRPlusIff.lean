import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IsCrisDRAIff
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (Ideal.span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

theorem isCrisDRA_toBdRPlus_iff (f : Bcris p R →+* BdR p R) :
    IsCrisDRA (Acris.toBdRPlus p R) f ↔ f = Bcris.toBdR p R := by
  constructor
  · intro hf
    refine Bcris.hom_ext fun x => ?_
    have h := BcrisPlus.hom_ext (f := f.comp (algebraMap (BcrisPlus p R) (Bcris p R)))
      (g := (Bcris.toBdR p R).comp (algebraMap (BcrisPlus p R) (Bcris p R))) (fun y => by
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply, hf y, Bcris.toBdR_algebraMap_acris])
    exact RingHom.congr_fun h x
  · rintro rfl x
    exact Bcris.toBdR_algebraMap_acris x

end Formalism.BasicNotions.CmpTie.Incl
