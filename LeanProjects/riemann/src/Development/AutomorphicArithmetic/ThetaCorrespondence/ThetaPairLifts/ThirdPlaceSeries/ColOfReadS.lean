import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistRelation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColNone
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
namespace GlobalTheory.Fam
theorem colOf_readS_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a),
    ∃ S' : ∀ (t : W.P.T) j, type_of% (k.ε 0) → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j,
    ∀ t, (∀ j, j ≤ B.R.m → ∀ η φ, (J t).A.RamL (J t).ι j φ → (J t).A.RamL (J t).ι j (S' t j η φ)) ∧
      ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ),
        @ReadS _ _ _ a.fld a.val a.top a.loc _ a.o ((a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP)).t t) k.ε (S' t 0) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ha hat J hJ k
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  choose S hS using fun t => GlobalTheory.T.levelPrimeOperators_act_ramifiedColumns_vanishing I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) _ _ (J t).A (J t).ι (hJ t).is (_root_.GlobalTheory.Fam.pk_z W).θ
    hat.pinX.inf a.k a.ι a.o.p a.o.β a.o.Q (fun j => (a.g.x j).L) hat.std a.o.I a.o.q a.o.χ a.o.hχ
  refine ⟨S, fun t => ⟨fun j hj η φ hφ => ((hS t j hj φ hφ).2 η).1, fun row kom dd s cV cK cP => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j hj ψ hψ α y
    have h := (hS t j hj ψ hψ).1 ((J t).ι j α) y
    change (if hj' : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j hj' ((J t).ι j α) ψ y else 0) ∈ a.o.Ram j
    have hj2 : j ≤ B.R.m := hj
    rw [dif_pos hj2]
    exact h
  · intro j hj ψ hψ α y
    have hj' : j ≤ B.R.m := by change j + 2 ≤ B.R.m at hj; omega
    change (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) (S t j (k.ε j) ψ) y else 0) =
      a.o.S k.ε j (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) ψ y else 0)
    rw [dif_pos hj', dif_pos hj']
    exact ((hS t j hj' ψ hψ).2 (k.ε j)).2 _ y
  · intro η ψ hψ
    have h0 : (0 : ℕ) ≤ B.R.m := Nat.zero_le _
    refine ⟨((hS t 0 h0 ψ hψ).2 η).1, fun α y => ?_⟩
    change (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) (S t 0 η ψ) y else 0) =
      a.o.S (fun _ => η) 0 (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) ψ y else 0)
    rw [dif_pos h0, dif_pos h0]
    exact ((hS t 0 h0 ψ hψ).2 η).2 _ y
end GlobalTheory.Fam
end
