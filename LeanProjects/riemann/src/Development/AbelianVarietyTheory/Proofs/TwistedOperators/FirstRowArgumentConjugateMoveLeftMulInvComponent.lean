import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOChiRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FirstRowCoord

open GlobalTheory.RowMoveAt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem actO_chi_small (i : ℕ) (M : GA D (G.V (.grid i D.R.m)))
    (x : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi i D.R.m) M 1).1⁻¹ (G.toPair (.chi i D.R.m) M 1).2⁻¹ x =
      mt (G.V (.grid i D.R.m)) M⁻¹ * (x : Matrix _ _ (AE D)) := by
  simp only [actO, GridData.toPair, inv_inv, map_one, inv_one]
  rw [show mt (G.pS (.chi i D.R.m : Pair T)) 1 = 1 from rfl, Matrix.mul_one]

theorem rowAt_first_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ w ∈ locPl G t, ∀ (k : FinPt G (.grid 0 D.R.m))
      (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ (ys (GlobalTheory.FirstRowVertex.firstIx D)))) =
      Function.update (S.rowAt t w ys) 0 (((GlobalTheory.FirstRowTermLaw.kapAt S t w k)⁻¹ : GL (Fin ((locGrid G t w).rank (0, (locGrid G t w).m))) (Kw w)).val * S.rowAt t w ys 0) := by
  intro D T L sc G W U S t ht w hw k ys
  have hX : DefNode D.R.m (.grid 0 D.R.m) := ⟨Nat.zero_le _, rfl⟩
  obtain ⟨P, e, he, hsupp, hoff⟩ := S.N.u_supp _ hX
  have hn := notOff S ht hw
  have hu := map_mt_eq_one hn he hoff hsupp
  have hu' := map_mt_eq_one hn he hoff (GlobalTheory.StdHalfLat.suppAt_inv' hsupp)
  have hM' : (mt _ ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1⁻¹).map ((cpt w).comp (toEAf D)) =
      (loc w (finG (G.V (.grid 0 D.R.m)) k⁻¹)).val := by
    rw [show mt _ ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1⁻¹ =
        mt _ (S.N.u (.grid 0 D.R.m)).1⁻¹ * mt _ k.1⁻¹ * mt _ (S.N.u (.grid 0 D.R.m)).1 from by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]; rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  have h0 : 0 < D.R.m := (GlobalTheory.FirstRowVertex.firstIx D).2
  funext i
  by_cases h1 : i = 0
  · subst h1
    rw [Function.update_self]
    simp only [GridChoice.rowAt, dif_pos h0, Frames.coord]
    erw [Function.update_self, actO_chi_small 0, Matrix.map_mul, hM']
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose]
    rw [GlobalTheory.FirstRowTermLaw.kapAt]
    erw [← map_inv (inBasis _ (S.B.β 0 D.R.m) w)]
    rw [map_inv (finG (G.V (Node.grid 0 D.R.m))) k]
    erw [inBasis_val, mul_sub_cast]
    rfl
  · rw [Function.update_of_ne h1]
    simp only [GridChoice.rowAt]
    by_cases hi : i < D.R.m
    · rw [dif_pos hi, dif_pos hi, Function.update_of_ne (fun h => h1 (congrArg Fin.val h))]
    · rw [dif_neg hi, dif_neg hi]

end GlobalTheory.FirstRowCoord
