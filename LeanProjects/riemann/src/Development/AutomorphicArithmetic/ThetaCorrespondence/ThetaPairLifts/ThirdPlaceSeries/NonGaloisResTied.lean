import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsReading
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedConditionOfLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LambdaPosOfTwistedMu
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalizationAtMember
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointsOfTiedLattices
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalRead
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
set_option maxHeartbeats 1000000 in
theorem resTied_of_tied_alt (hP : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hH : GlobalTheory.Published.HarishChandraFinite) (hD : GlobalTheory.Published.CuspRapidDecay)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) (X : _root_.GlobalTheory.NRows.LinkedData hL D) (hO : SumRepresentations.hypO D) (hd : DV.LamDef D)
    (hpos : ∀ v, TwistedAt D v → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP (D.what₂.muTw v) j σ)
    (hloc : ∀ v, TwistedAt D v → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∃ i : D.nd.Loc, D.nd.w i = v ∧ D.nd.j i = j)
    (Rw : RowSide D) (hRw : HEq Rw.locR b.A.row.locR) : _root_.GlobalTheory.EigTie.ResTiedAlt D Rw := by
  obtain ⟨a1, a2, a3, a4⟩ := _root_.GlobalTheory.ResLoc.exists_paired_point_of_thetaT_ne_zero hP hH hD X
  have hpt : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      ∃ (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i), D.nd.w i = w ∧ GlobalTheory.ThetaExh.Pairs D.nd D.naut i σ P ∧
        D.naut.ptV i P = some x := by
    intro j h1 h2 σ hσ w hw
    obtain ⟨i, rfl, rfl⟩ := hloc w hw j h1 h2 σ hσ
    obtain ⟨i', P, x, -, e, h⟩ := a4 i σ (exists_thetaT_ne hd h1 h2 hσ (by rw [D.nd.mu_w i]; exact hpos _ hw _ h1 h2 σ hσ))
    exact ⟨i', P, x, e, h⟩
  clear X hd hpos hloc a4
  obtain ⟨D₀, cf, jE, A, _, _, _, _, _, _, _, _, _, _, _, M, C, tp, _, _, big, L, Sp, Au, _, rfl⟩ := b
  exact _root_.GlobalTheory.ResLoc.resTied_of_points_alt_alt (D := withLoc L) (GlobalTheory.ChebSplitDense.chebSplit hP.cheb D₀.nd) Rw (plL L A.pl) A.iota Au.iotaQC Au.kFbar
    (fun i σ w => (Au.locW i σ w).trans (congrFun (congrFun (eq_of_heq hRw) σ) w).symm) a1 hO a2 a3 hpt
end GlobalTheory.ResLoc
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem residual_ties_of_membership : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → _root_.GlobalTheory.EigTie.ResTiedAlt (w.D Z) Rw := by
  intro hP hL
  refine EvG.imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_linked_data_pinned_at_layer hP hL) (_root_.GlobalTheory.T.lamP_muTw_pos_at_members hP hL)) (_root_.GlobalTheory.T.exists_loc_with_place_and_index_at_member hP hL))
    fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hE hX hp Rw hRw => ?_
  obtain ⟨⟨⟨X, -⟩, hpos⟩, hloc⟩ := H kp w Z Wt p0 t nch n xd c hE hX hp
  obtain ⟨e⟩ := hE
  exact _root_.GlobalTheory.ResLoc.resTied_of_tied_alt hP.what₂ hP.hc hP.decay c.a.nt.toNBuilt X
    (e : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd).large.1 t.r.Y.lam hpos hloc Rw hRw
end GlobalTheory.ResLoc
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_galois_residual_ties : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → _root_.GlobalTheory.EigTie.ResTiedAlt (w.D Z) Rw := by
  first | exact @_root_.GlobalTheory.ResLoc.residual_ties_of_membership | exact _root_.GlobalTheory.ResLoc.residual_ties_of_membership | (intros; apply _root_.GlobalTheory.ResLoc.residual_ties_of_membership <;> assumption)
end
end
