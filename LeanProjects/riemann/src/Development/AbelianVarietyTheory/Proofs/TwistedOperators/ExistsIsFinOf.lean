import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def locAt (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) :
    GA D (G.V (.grid D.R.m j)) →* GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w) :=
  (inBasis (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w).comp (Lev.finE _)

theorem locAt_inf (B : Frames G) (t : T) (w : Pl D.host.E) (j : ℕ) (hj : j ≤ D.R.m) {a : GA D (G.V (.grid D.R.m j))}
    (ha : a ∈ GinfC _) : locAt B t w j hj a = 1 := by
  have h : Lev.finE (G.V (.grid D.R.m j)) a = 1 := by
    simp only [Lev.finE, GinfC, MonoidHom.mem_ker] at ha ⊢
    rw [MonoidHom.comp_apply, ha, map_one]
  simp only [locAt, MonoidHom.comp_apply, h, map_one]

theorem exists_isFinOf (V : HSp D) (g : GA D V) : ∃ b, GlobalTheory.RowVal.IsFinOf g b := by
  obtain ⟨-, -, -, ⟨e, he⟩, -⟩ := GlobalTheory.AdelicSplit.adelic_split D V
  obtain ⟨p, rfl⟩ := e.surjective g
  exact ⟨p.2, p.2.2, p.1, p.1.2, (he p).symm⟩

theorem elt_succ (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (i : Fin ((locGrid G t w).m - 2)) :
    (repsAt G t w).elt β ((locGrid G t w).m, i.1 + 1) = (repsAt G t w).rep i (β i) := by
  simp only [Reps.elt]
  rw [onColumn_apply]
  simp only [dif_pos i.2]

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem loc_rep (B : Frames G) (t : T) (s : ℤˣ) (β : CosFam G t) (w : locPl G t) (i : Fin ((locGrid G t w.1).m - 2))
    (hj : i.1 + 1 ≤ D.R.m) (r : GA D (G.V (.grid D.R.m (i.1 + 1))))
    (ρ : GL (Fin ((locGrid G t w.1).rank (D.R.m, i.1 + 1))) (Kw w.1)) (hρ : ρ = (repsAt G t w.1).rep i (β w i))
    (hr : (inBasis (rank_vertex G t w.1 (X := (D.R.m, i.1 + 1)) ⟨le_rfl, hj⟩) (B.β D.R.m (i.1 + 1)) w.1)
      (Lev.finE (G.V (.grid D.R.m (i.1 + 1))) r) =
      GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * (repsAt G t w.1).elt (β w) (D.R.m, i.1 + 1)) :
    locAt B t w.1 (i.1 + 1) hj r = GlobalTheory.RowVal.sgnAt G t s w.1 (i.1 + 1) * ρ := by
  rw [hρ, ← elt_succ]
  exact hr

theorem mk_eq_of {Gp : Type} [Group Gp] (H K : Subgroup Gp) {A A' S X Y ρ ρ' : Gp}
    (e : A' * (S * ρ') = X * (A * (S * ρ)) * Y) (hN : (A' * S)⁻¹ * X * (A * S) ∈ H) (hY : Y ∈ K) :
    DoubleCoset.mk H K ρ = DoubleCoset.mk H K ρ' := by
  rw [DoubleCoset.eq]
  refine ⟨_, hN, Y, hY, ?_⟩
  rw [show (A' * S)⁻¹ * X * (A * S) * ρ * Y = (A' * S)⁻¹ * (X * (A * (S * ρ)) * Y) by group, ← e]
  group

theorem idx_le {j : ℕ} (h : j ∈ GlobalTheory.RowVal.idx D) : 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  simp only [GlobalTheory.RowVal.idx, List.mem_range'_1] at h
  omega

end GlobalTheory.RowRep
