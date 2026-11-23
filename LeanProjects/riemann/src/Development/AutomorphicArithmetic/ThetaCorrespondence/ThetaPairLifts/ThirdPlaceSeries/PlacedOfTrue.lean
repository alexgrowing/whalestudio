import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChartZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeEqBaseOffTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevTraceMemStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceChiStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.FamPlaced
section Prim
open GlobalTheory.FinPl
end Prim
theorem placedP_of_allTrue : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → _root_.GlobalTheory.MiTop.PlacedConditions (a.fam row col) a.d.B := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hT' row col hc
  refine ⟨a.k, a.fld, a.val, a.top, a.loc, a.ι, a.v, a.o, a.n, a.G, a.pl, hc, ha.vis, (ha.tie row col).1, ha.shape, ha.gpin,
    (ha.tie row col).2, ?_, ?_⟩
  swap
  · intro p hp b hb
    have hx := (hT'.pinX.xs B.R.m le_rfl).2.2
    have hTp : (((B.T u : ℕ) : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
      intro h; apply hp; rw [(ha.tie row col).1.tP p]; exact_mod_cast h
    have hpos : 0 < B.R.N B.R.m := B.R.N_pos _
    refine prim_std _ _ hx p _ (fun i => ?_)
      (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl).symm ⟨B.R.N B.R.m - 1, Nat.sub_lt hpos one_pos⟩)
      (B.host.conj (X.piT u : B.host.E)) (map_isIntegral_int (B.host.conj : B.host.E →+* B.host.E) (X.piT u).2)
      ((B.T u : ℕ) : ℤ) ?_ hTp b hb
    · refine (hT'.z0 i).symm ▸ ?_
      show IsIntegral ℤ (TC.z0 X u _)
      unfold TC.z0
      split_ifs
      · exact (X.piT u).2
      · exact isIntegral_zero
    · have h0 : TC.z0 X u ⟨B.R.N B.R.m - 1, Nat.sub_lt hpos one_pos⟩ = (X.piT u : B.host.E) :=
        if_pos (Nat.sub_add_cancel hpos)
      have h1 := (hT'.z0 (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl).symm
        ⟨B.R.N B.R.m - 1, Nat.sub_lt hpos one_pos⟩)).trans h0
      have h2 : (X.piT u : B.host.E) * B.host.conj (X.piT u : B.host.E) = (((B.T u : ℕ) : ℤ) : B.host.E) := by
        rw [Int.cast_natCast]; exact X.piT_norm u
      exact (congrArg (fun t : B.host.E => t * B.host.conj (X.piT u : B.host.E)) h1).trans h2
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  constructor
  · exact ha.bot.1
  · exact ha.bot.2.2.1
  · refine ⟨1, -(I.rec7 l Z).host.xi0 ^ ((I.rec7 l Z).R.m / 2), by simp, ?_, ?_⟩
    · intro r; rw [one_mul]; exact ha.bot.2.2.2 r
    · exact ha.norm.2
  · exact fun i => (ha.stdG i).2.2
  · exact _root_.GlobalTheory.Fam.lattice_eq_base_off_twist_alt W hA u a ha hT' row col hc
  · intro κ hκ y e
    exact ⟨_root_.GlobalTheory.T.true_geometry_local_data_alt W hA u a ha hT' row col hc κ hκ y e, _root_.GlobalTheory.T.true_geometry_reduction_level_alt W hA u a ha hT' row col hc κ hκ y e⟩
end GlobalTheory.FamPlaced
end
end
