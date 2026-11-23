import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitNontrivialAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.FrameTypes
open ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.CenFrame
set_option maxHeartbeats 4000000 in
theorem mtInput_of_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (M' : MtFam D') (hM : HEq (mtL nt.L nt.M) M') :
    ∃ tup Q, MtInput D' M' tup Q := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have hm : mtL L M = M' := eq_of_heq hM
  subst hm
  exact ⟨tp.tup, C.Q, { mt with }⟩
variable {D : D7}
section Read
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}
end Read
set_option maxHeartbeats 1000000 in
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        ∃ (f : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV → ℂ) (J : Subgroup (Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV)) (χ : J →* ℂˣ)
          (ψ₀ : AddChar (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E)) ℂ)
          (ξ : (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E))ˣ →* ℂˣ),
          f ≠ 0 ∧ Formalism.L2.NG.IsPsi0 s' ψ₀ ∧ Formalism.L2.NG.LevelUni J χ s' (w.st Z).toD7.R.r ψ₀ ξ ∧
          (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
          (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV, ReciprocityTheory.Aut.TrivOutside {s'.v} κ → ∀ y : GL (Fin (w.st Z).toD7.R.nV) (GlobalTheory.CenFrame.Os s'),
        GlobalTheory.CenFrame.IsCompOf s' κ y →
      ((∀ i j : Fin (w.st Z).toD7.R.nV, ((w.st Z).toD7.R.r ≤ i.val → j.val < (w.st Z).toD7.R.r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE hR hP => ?_
  intro ad i s k hs hnt s' φ b hPg _ hfr
  obtain ⟨tup, Q, hin⟩ := _root_.GlobalTheory.FrameTypes.mtInput_of_alt c.a.nt c.a.all.gal.mt c.a.mt_eq
  obtain ⟨plg, iso, h1, -⟩ := t.r.z.pins.keep.grp
  exact types_of (D := (w.st Z).toD7) ad hin t.r.z.pins.char.base.lev t.r.z.pins.char.base.grp.levels i _ k hs hnt s' φ b hPg
    ⟨(plg.symm ⟨s'.w, hPg⟩).1, (plg.symm ⟨s'.w, hPg⟩).2, by rw [← h1, plg.apply_symm_apply]⟩ hfr
end GlobalTheory.FrameTypes
end
end
