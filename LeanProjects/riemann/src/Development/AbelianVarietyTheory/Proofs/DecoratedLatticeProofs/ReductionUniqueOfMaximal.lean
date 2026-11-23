import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.StepData ValuativeRel

namespace GlobalTheory.LevelComb

variable {D : D7} {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}
  {PP : Formalism.L2.DIV.Pl D.host.E}

theorem mem_of_rho_lt (G : GAt d τ PP) {z : 𝓞 D.host.E} (hz : valuation G.k (rho G z) < 1) : z ∈ PP.asIdeal := by
  by_cases h0 : z = 0
  · subst h0; exact PP.asIdeal.zero_mem
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  refine (G.idem.2 z h0).2 ?_
  rw [← G.q.sec_pr, ← G.q.int_iff]
  change (G.q.pr.comp (incA D)) _ ∉ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).2 hz

end GlobalTheory.LevelComb

theorem GlobalTheory.LevelComb.red_uniq : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (x x' : G.S.P.J) (g g' : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)), G.Red x g → G.Red x' g' → GlobalTheory.StepData.MaxM ((x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val) → g' = g := by
  intro D u d τ PP G x x' g g' hx hx' hm
  rw [GlobalTheory.LevelComb.red_iff] at hx hx'
  ext a' b'
  obtain ⟨a, rfl⟩ := (GlobalTheory.LevelComb.pos G).surjective a'
  obtain ⟨b, rfl⟩ := (GlobalTheory.LevelComb.pos G).surjective b'
  have h := (valuation G.k).map_sub_lt ((valuation G.k).map_add_lt (hx a b) (hm a b)) (hx' a b)
  have e : ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - GlobalTheory.LevelComb.lift G g.val) a b +
      (((x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val) a b) -
      ((x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - GlobalTheory.LevelComb.lift G g'.val) a b =
      GlobalTheory.LevelComb.rho G (GlobalTheory.LevelComb.out (g'.val (GlobalTheory.LevelComb.pos G a) (GlobalTheory.LevelComb.pos G b)) -
        GlobalTheory.LevelComb.out (g.val (GlobalTheory.LevelComb.pos G a) (GlobalTheory.LevelComb.pos G b))) := by
    simp only [Matrix.sub_apply, GlobalTheory.LevelComb.lift, map_sub]; ring
  rw [e] at h
  have hm' := GlobalTheory.LevelComb.mem_of_rho_lt G h
  rw [← GlobalTheory.LevelComb.mk_out (g'.val _ _), ← GlobalTheory.LevelComb.mk_out (g.val _ _)]
  exact (Ideal.Quotient.eq.2 hm')
