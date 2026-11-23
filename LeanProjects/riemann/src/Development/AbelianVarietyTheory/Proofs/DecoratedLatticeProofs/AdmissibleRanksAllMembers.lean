import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionTypingsCompare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnStabilizerTrivialLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealTiedSetDiv
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberRanks

theorem typePrimesLarge_of_val {C} {cD ch : ℝ} {D : D7} (L : SizeData₂ D) (hv : Val C cD ch L) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers.TypePrimesLarge D := by
  intro i
  have h1 : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) := (hv.host.2.2.2.2.1 i).1
  have hb : 1 ≤ L.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _)
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h2 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 :=
    pow_le_pow_left₀ hk0 (le_mul_of_one_le_right hk0 hb) 8
  have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2.trans h1
  have hf : D.R.f ≤ D.R.k := D.R.f_le_k
  have hk : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have h4 : D.R.k ^ 3 ≤ D.R.k ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h5 : 2 * D.R.f * D.R.k + 1 < D.R.k ^ 3 := by
    have : D.R.f * D.R.k ≤ D.R.k * D.R.k := Nat.mul_le_mul_right _ hf
    have h6 : 5 * (D.R.k * D.R.k) ≤ D.R.k ^ 3 := by
      rw [pow_succ, pow_two, mul_comm 5]; exact Nat.mul_le_mul_left _ hk
    have h7 : 25 ≤ D.R.k * D.R.k := Nat.mul_le_mul hk hk
    rw [mul_assoc]; omega
  omega

theorem dstar_mass (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    X.toD7.what₂.Dstar =
      StandardLattice.DstarP X.toD7 (X.toD7.host.g 0) (X.toD7.host.g 1) (StandardLattice.massI X.toD7 X.toD7.R.r) X.toD7.dsig := by
  have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
  rw [e, hO.sizes.2]
  unfold DsPre StandardLattice.DstarP
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

theorem columnRowRanks_admissible_of_massFormula (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D)
    (hD : D.what₂.Dstar = StandardLattice.DstarP D (D.host.g 0) (D.host.g 1) (StandardLattice.massI D D.R.r) D.dsig)
    (hG : StandardLattice.GBig D) (hT : ∀ u, Formalism.MainNotions.S.SplitsE D (D.mem u).A.T) : LocalBesselAndTopKernel.FamilyMidVolume D := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  intro V _ _ _ _ h L _
  refine ⟨fun hL u => ?_, fun hL => ?_⟩
  · have e := h4 hG (Formalism.MainNotions.J.splitsF_g D) u (Formalism.MainNotions.J.splitsF_of_splitsE D _ (D.mem u).A.T_prime (hT u))
      (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
    have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.k := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.k)
    rw [em, ← Formalism.MainNotions.J.idxColTie_holds D]
    exact e
  · have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.r := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.r)
    rw [em, ← Formalism.MainNotions.J.idxRowTie_holds D, hD]
    rfl

theorem admissible_ranks_at_member : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  intro hL p
  refine GlobalTheory.Fc.RowE.of_all fun κ K β c b h0 h1 h2 => ?_
  obtain ⟨hv, -⟩ :=
    GlobalTheory.Fc.built_val GlobalTheory.Fc.Bundle (Bl.IsGoodE p.s) (Bl.IsLinked p) κ β.D β.O c b (GlobalTheory.Fc.Built.intro h0 h1 h2)
  exact columnRowRanks_admissible_of_massFormula β.D β.O.lev b.R.T.cols (dstar_mass K β.X β.c.isOver β.c.dsig_eq)
    (GlobalTheory.Proof.ColumnStabilizerTrivialLocal.gBig_of_large (typePrimesLarge_of_val β.O.L hv)) (fun u => GlobalTheory.CollCompare.splits_level β.D u)

end GlobalTheory.MemberRanks
