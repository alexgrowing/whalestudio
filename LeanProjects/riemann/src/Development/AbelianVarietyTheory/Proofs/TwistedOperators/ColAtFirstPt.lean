import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.TopZeroInv GlobalTheory.TopLevelInv GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroFirst
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem zero_lt_m (D : D7) : 0 < D.R.m := by
  have h2 := D.R.two_le_m
  omega

private theorem inBasis_val_eq_submatrix_conj {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) :
    (inBasis h β w x).val = ((loc w β)⁻¹ * loc w x * loc w β).val.submatrix (Fin.cast h) (Fin.cast h) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

def kapTop0 (S : GridChoice W U) (t : T) (k : FinPt G (.top 0)) (w : Pl D.host.E) :
    GL (Fin (topRank (locGrid G t w) 0)) (Kw w) :=
  inBasis (topRank_eq G t w (Nat.zero_le _)) (S.βp 0) w (finG (G.V (.top 0)) k)

def firstPt (t : T) (g : FinPt G (.top 0)) (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) :=
  Function.update x ⟨0, zero_lt_m D⟩ (actO _ _ (g : GA D (G.V (.top 0)))⁻¹ 1⁻¹ (x ⟨0, zero_lt_m D⟩))

def datFn {t : T} (d : PureDat G t) : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ
  | .inl j => (d.1 j).fn
  | .inr i => (d.2 i).fn

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem colAt_firstPt (S : GridChoice W U) {t : T} (ht : t ∈ U) (k : FinPt G (.top 0)) {w : Pl D.host.E}
    (hw : w ∈ locPl G t) (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    S.colAt t w (firstPt t ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) x) =
      Function.update (S.colAt t w x) 0 (S.colAt t w x 0 * (kapTop0 S t k w).val) := by
  funext j
  by_cases hj : j < D.R.m
  · by_cases h0 : j = 0
    · subst h0
      have hu := loc_finE_u_colCoord S ht (X := .top 0) (Nat.zero_le _) hw
      rw [Function.update_self, colAt_eq S t w _ hj, colAt_eq S t w _ hj]
      unfold firstPt
      rw [Function.update_self, frAt_actO_colCoord]
      simp only [inv_one, map_one, mul_one, inv_mul_cancel, Units.val_one, Matrix.one_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv, hu, _root_.inv_inv, _root_.mul_inv_rev, one_mul]
      unfold kapTop0
      rw [inBasis_val_eq_submatrix_conj, submatrix_cast_mul_colCoord]
      simp only [_root_.mul_assoc]
      rfl
    · rw [Function.update_of_ne h0, colAt_eq S t w _ hj, colAt_eq S t w _ hj]
      unfold firstPt
      rw [Function.update_of_ne (fun h => h0 (congrArg Fin.val h))]
  · have h0 : j ≠ 0 := by
      have := zero_lt_m D
      omega
    rw [Function.update_of_ne h0]
    simp only [GridChoice.colAt, dif_neg hj]

end GlobalTheory.TopZeroFirst

end
