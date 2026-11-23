import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
import Formalism.LocalToGlobal.InertKernelTheory.DefsInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticesSelfDualMovedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableIntertwiningPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeCoordsRationalPointMulEqCoordMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableThetaLocalSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankSelfDualUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.RatMoveJets

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {a b : ℂ} (ha : Mod1All a) (hb : Mod1All b) (hua : GlobalTheory.MovedKappaEx.UnitAt q a)
    (hub : GlobalTheory.MovedKappaEx.UnitAt q b) : GlobalTheory.MovedKappaEx.UnitAt q (a * b) := by
  obtain ⟨ha', -⟩ := ha
  obtain ⟨hb', -⟩ := hb
  intro lam
  have hab : a * b ∈ Qbar := mul_mem ha' hb'
  have e : lamC lam (a * b) = lamC lam a * lamC lam b := by
    unfold lamC
    rw [dif_pos hab, dif_pos ha', dif_pos hb', ← map_mul]
    rfl
  rw [e, norm_mul, hua lam, hub lam, one_mul]

theorem exists_rat_move : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (r : FinPt ch.G p.small) (r' : FinPt ch.G p.big), GlobalTheory.MovedKappaEx.RatFin _ r → GlobalTheory.MovedKappaEx.RatFin _ r' →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime],
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small (r * x)) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big (r' * y)) (stdL D _) →
        GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (r * x) (r' * y) (c * κ) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hJ r r' hr hr'
  obtain ⟨hns, hnb⟩ := hp.nodes
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_unitaryCoordinate_of_rationalPoint_definiteVertex ch.S.toGridChoice _ hns r hr
  obtain ⟨U', hU'⟩ := GlobalTheory.T.exists_unitaryCoordinate_of_rationalPoint_definiteVertex ch.S.toGridChoice _ hnb r' hr'
  have hlx := GlobalTheory.T.vertexLatticeCoords_rationalPoint_mul_eq_coordMatrix ch.S.toGridChoice _ r U hU x
  have hly := GlobalTheory.T.vertexLatticeCoords_rationalPoint_mul_eq_coordMatrix ch.S.toGridChoice _ r' U' hU' y
  have hd := GlobalTheory.MovedDict.Entire.differentiable_intertwining_moved hP hI ch hch p hp x y
  obtain ⟨ε, hm, hu, hj⟩ := GlobalTheory.T.differentiable_theta_local_sum hP hI ch hch p hp x y _ (hd.const_mul κ) ((jetKap_iff ch p x y κ).1 hJ) r r' U U' hU hU'
  obtain ⟨hsd, hsd'⟩ := GlobalTheory.MovedSD.sd_srcLat_tgtLat hP hI ch hch p hp x y
  obtain ⟨ε', hm', hu', hB⟩ := GlobalTheory.T.even_rank_self_dual_unitary hP hI ch.S.Z.crv ch.S.Z.pt0 (ch.S.Z.e0_is p hp) (GlobalTheory.FunObj.even_rank_mul ch.G p hp) _ _
    hsd hsd' (srcU p U U') (tgtU p U U')
  have hst : GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p (r * x) (r' * y) =
        SDLat.smulLat (srcU p U U').1 (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) ∧
      GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p (r * x) (r' * y) =
        SDLat.smulLat (tgtU p U U').1 (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y) := by
    cases p <;> exact ⟨by first | exact hlx | exact hly, by first | exact hlx | exact hly⟩
  have hq : ∀ (q : ℕ) [Fact q.Prime],
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small (r * x)) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big (r' * y)) (stdL D _) →
      GlobalTheory.MovedKappaEx.UnitAt q ε' := by
    intro q _ h1 h2 h3 h4
    rw [hlx] at h3
    rw [hly] at h4
    cases p <;> first
      | exact hu' q h2 h1 h4 h3
      | exact hu' q h1 h2 h3 h4
  refine ⟨ε * ε', GlobalTheory.FamilyTieProof.mod1All_mul' hm hm', fun q _ h1 h2 h3 h4 => unitAt_mul hm hm' (hu q h1 h2 h3 h4) (hq q h1 h2 h3 h4), ?_⟩
  rw [jetKap_iff, hst.1, hst.2]
  have e : (fun z => ε * ((fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)
        (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)
        (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK ch.S.Z.δ) (srcU p U U').1 (tgtU p U U').1 z))) =
      fun z => ε * ε' * κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
        (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (SDLat.smulLat (srcU p U U').1 (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y))
          (SDLat.smulLat (tgtU p U U').1 (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))) (ch.S.Z.e0 p) z := by
    funext z
    simp only
    rw [hB z]
    ring
  rw [e] at hj
  intro k
  rw [hj k]

end GlobalTheory.RatMoveJets
