import Formalism.SharpRestriction.Divisibility.ChainOperators.PerCol
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSx
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSy

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem sgAtG_of {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) : Formalism.MainNotions.WeightDegreeSizes.SgAtG D L Xe C1 :=
  fun i w hwi u hw => sumFE_atG_le hF hE hC1 hC i w hwi u hw

theorem periodBound_at_type_of_local {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 C2 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) (h : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2)
    (hN : Formalism.MainNotions.WeightDegreeSizes.NuInM D L) : PeriodBoundAtTypePrimes D L := by
  intro u w hw hgm φ hφ F hF1 _
  obtain ⟨i, hwi⟩ : ∃ i : Fin 2, D.what₂.places.resChar w = D.host.g i := by
    rcases Finset.mem_insert.1 hgm with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, Finset.mem_singleton.1 h1⟩
  exact Formalism.MainNotions.WeightDegreeSizes.period_integral_at_typePrime h (sgAtG_of hF hE hC1 hC) hN (Formalism.MainNotions.DIV.perColSmul D) u w i hwi hw φ hφ F hF1

theorem period_conditions_of_pairing_twist {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
    {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : Formalism.MainNotions.WeightDegreeSizes.PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hET : Formalism.MainNotions.WeightDegreeSizes.LevelPrimeSizes D L)
    (ht : Ties9 D L X Y c) (hS : c.NuServedDef X Y K) (hNT : NuAtTDef D L) (hN : Formalism.MainNotions.WeightDegreeSizes.NuInM D L)
    (hGI : Formalism.MainNotions.WeightDegreeSizes.ServedHasModel X K) (hF : ∀ w, ParametersFill X K w)
    (hcs : ∀ p : ℕ, p.Prime → IsCs D p → p ∈ L.drop) (hG : Formalism.MainNotions.WeightDegreeSizes.LevelPrimeCoprimeStabiliser D)
    (h1 : Formalism.MainNotions.WeilJacquetShalikaLaw.Conclusion1 D L X Y K c Dx T lev Xe ce 1) (h5 : Formalism.MainNotions.WeightDegreeSizes.ValuationAtLevelPrime D Dx T) {C1 C2 : ℝ}
    (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) : Formalism.MainNotions.LocalQuadraticParts.adm2 D L :=
  period_conditions_of_pairing hP hE hET ht hS hNT hN hGI hF hcs hG h1 h5 hCL (sgAtG_of ht.fdef hE hC1 hC) (Formalism.MainNotions.DIV.perColSmul D)

theorem no_gain_condition_of_local {K : Consts} {Dx : DivX D} {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC}
    (hP : Formalism.MainNotions.WeightDegreeSizes.PairingAtEveryPlace D Dx T) (hE : ErrDefs D L Xe lev K ce) (hF : L.FDef)
    (h : Formalism.MainNotions.WeilJacquetShalikaLaw.ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce 1) {C1 C2 : ℝ} (hCL : Formalism.MainNotions.LiftErrorLocal.PropositionCLatticeBound D L Xe C1 C2)
    (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) : Formalism.MainNotions.LocalQuadraticParts.adm12 D L :=
  no_gain_condition_of_pairing_sign hP hE hF h hCL (sgAtG_of hF hE hC1 hC)

theorem family_type_prime_loss {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {C1 : ℝ} (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ Fm.cX.err.g) :
    Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 :=
  ⟨0, fun x hx _ i => sgAtG_of (local_compatibility_family Fm x hx i).fdef (Fm.ex x hx i).err hC1 hC⟩

end Formalism.MainNotions.J

end
