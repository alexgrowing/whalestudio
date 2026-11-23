import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LiftInvariantsFinrankEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoeffXMulPart
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MonomialOneMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaximalIdealLeFiltOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiltLePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NoethLocalHausdorff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Imports
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqXMulShiftAdd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemPowOfCoeffMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsBis

noncomputable section

open MvPowerSeries IsLocalRing Formalism.BasicNotions.V1

namespace GlobalTheory.PsCNL

section Division

variable {σ : Type} {O : Type} [CommRing O]

def divX (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O := fun m => coeff (Finsupp.single i 1 + m) f

def remX (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O := fun m => if m i = 0 then coeff m f else 0

end Division

section

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem mem_max_iff (f : MvPowerSeries (Fin a) O) :
    f ∈ maximalIdeal (MvPowerSeries (Fin a) O) ↔ constantCoeff f ∈ maximalIdeal O :=
  _root_.GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff f

theorem ps_isPrecomplete [IsPrecomplete (maximalIdeal O) O] (a : ℕ) :
    IsPrecomplete (maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) :=
  _root_.GlobalTheory.PowerSeriesIdealPowers.main a

end

theorem haus_of_noeth (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    IsHausdorff (maximalIdeal B) B :=
  _root_.GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff B

theorem psCNL : ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : TR O) (n : ℕ),
    ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) C.C)), IsCNL O (MvPowerSeries (Fin n) C.C) ∧
      ∀ x : MvPowerSeries (Fin n) C.C, x ∈ maximalIdeal (MvPowerSeries (Fin n) C.C) ↔
        MvPowerSeries.constantCoeff x ∈ maximalIdeal C.C := by
  intro O _ _ A n
  refine ⟨inferInstance, ?_, fun x => mem_max_iff x⟩
  exact
    { noeth := inferInstance
      complete :=
        { toIsHausdorff := haus_of_noeth _
          toIsPrecomplete := ps_isPrecomplete n }
      localHom := ⟨fun a ha => by
        rw [MvPowerSeries.algebraMap_apply, isUnit_iff_constantCoeff, constantCoeff_C] at ha
        exact isUnit_of_map_unit _ _ ha⟩
      resSurj := by
        intro y
        obtain ⟨f, rfl⟩ := residue_surjective y
        obtain ⟨a, ha⟩ := IsCNL.resSurj (O := O) (A := A.C) (residue A.C (constantCoeff f))
        have ha' : residue A.C (algebraMap O A.C a) = residue A.C (constantCoeff f) := ha
        refine ⟨a, ?_⟩
        show residue _ (algebraMap O (MvPowerSeries (Fin n) A.C) a) = residue _ f
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
          isUnit_iff_constantCoeff, map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C]
        show algebraMap O A.C a - constantCoeff f ∈ maximalIdeal A.C
        rw [← residue_eq_zero_iff, map_sub, ha', sub_self] }

end GlobalTheory.PsCNL

open Formalism.BasicNotions.V1 IsLocalRing in
example : ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : TR O) (n : ℕ), ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) C.C)), IsCNL O (MvPowerSeries (Fin n) C.C) ∧ ∀ x : MvPowerSeries (Fin n) C.C, x ∈ maximalIdeal (MvPowerSeries (Fin n) C.C) ↔ MvPowerSeries.constantCoeff x ∈ maximalIdeal C.C := GlobalTheory.PsCNL.psCNL
