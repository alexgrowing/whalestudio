import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadingInMovedRowData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSideReadingLevelZeroMoved
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowIdentificationsRealRowSideOfChainComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdentificationTypeRepresentativesClasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.CopyRead

theorem occ_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {y : Hd R} {Φ : Type}
    {rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r} (h : Reps y F rep) : y.occ F = {ρ | ∃ π, (rep π).Iso ρ} := by
  refine Set.ext fun ρ => ⟨h.all ρ, fun ⟨π, hi⟩ => ?_⟩
  obtain ⟨b, hb⟩ := h.mem π
  refine ⟨b, ?_⟩
  unfold principalLevelFrame.isotE at hb ⊢
  rw [← principalLevelFrame.isotL_iso _ _ _ _ _ _ (principalLevelFrame.conjT_iso hi)]
  exact hb

theorem rep_eq {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {S S' U : Set (Formalism.L2.NG.FinTyp L n)} (e : S = U) (e' : S' = U)
    {c : Formalism.L2.Col.FinTypCls S} {c' : Formalism.L2.Col.FinTypCls S'} {ρ : Formalism.L2.NG.FinTyp L n}
    (h : (Formalism.L2.Col.finTypRep S c).Iso ρ) (h' : (Formalism.L2.Col.finTypRep S' c').Iso ρ) :
    Formalism.L2.Col.finTypRep S c = Formalism.L2.Col.finTypRep S' c' := by
  subst e e'
  exact congrArg _ (Formalism.L2.Col.finTypRep_inj (Formalism.L2.NG.IsoRep.trans h (Formalism.L2.NG.IsoRep.symm (Formalism.L2.Col.finTypRep _ c').stable h')))

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀}

set_option maxHeartbeats 2000000 in

theorem rep_pin {o : q.Over} {m : Moved o} (hco : m.Coh) {s : Side0 o} (r : ReadPk m s) (hp : r.Pin) (π : q.p.Φ) :
    ∃ (S : Set (Formalism.L2.NG.FinTyp (w.st Z₀).toD7.host.E (w.st Z₀).toD7.R.r)) (c : Formalism.L2.Col.FinTypCls S),
      S = {ρ | ∃ π', (q.t.rep π').Iso ρ} ∧ (Formalism.L2.Col.finTypRep S c).Iso (q.t.rep π) ∧
        HEq (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT ((π)))) (Formalism.L2.Col.finTypRep S c) := by
  have e : ((by with_unfolding_all exact (m.t.rep :)) : type_of% q.t.rep) = q.t.rep := eq_of_heq ((by with_unfolding_all exact (hco.rep :)))
  have h1 := occ_iff m.t.reps
  have h2 := congrArg (fun P : type_of% m.y.PY => principalLevelFrame.OccRows m.z.R.θ P (m.z.R.MY 0)
    (fun b => levS _ (m.z.R.βY 0) (m.z.R.dat0 (m.z.R.toRealDat.levR m.z.F.lv2 b)))
    (fun b => levChi _ (m.z.R.βY 0) (m.z.R.dat0 (m.z.R.toRealDat.levR m.z.F.lv2 b))) (fun _ => m.z.R.toRealDat.e0)) r.PY
  have h3 := h2.trans h1
  have h4 := hp.rep ((by with_unfolding_all exact (π :)))
  rw [← e]
  have h5 : ∃ (S : Set (Formalism.L2.NG.FinTyp (w.st o.Z).toD7.host.E (w.st o.Z).toD7.R.r)) (c : Formalism.L2.Col.FinTypCls S),
      S = {ρ | ∃ π', (m.t.rep π').Iso ρ} ∧ (Formalism.L2.Col.finTypRep S c).Iso (m.t.rep π) ∧
        HEq (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT ((by with_unfolding_all exact (π :))))) (Formalism.L2.Col.finTypRep S c) := ⟨_, r.Y.eFT π, h3, h4, HEq.rfl⟩
  exact (by with_unfolding_all exact (h5 :))

set_option maxHeartbeats 2000000 in

theorem repOf_heq {o o' : q.Over} {m : Moved o} (hco : m.Coh) {s : Side0 o} (r : ReadPk m s) (hp : r.Pin)
    {m' : Moved o'} (hco' : m'.Coh) {s' : Side0 o'} (r' : ReadPk m' s') (hp' : r'.Pin) :
    HEq (GlobalTheory.HeightCounting.repOf r'.Y) (GlobalTheory.HeightCounting.repOf r.Y) := by
  have h : ∀ π : q.p.Φ, ((by with_unfolding_all exact ((GlobalTheory.HeightCounting.repOf r'.Y ((π))) : _)) : Formalism.L2.NG.FinTyp (w.st Z₀).toD7.host.E (w.st Z₀).toD7.R.r) =
      (by with_unfolding_all exact ((GlobalTheory.HeightCounting.repOf r.Y ((π))) : _)) := fun π => by
    obtain ⟨S, c, h1, h2, h3⟩ := rep_pin hco r hp π
    obtain ⟨S', c', h1', h2', h3'⟩ := rep_pin hco' r' hp' π
    exact eq_of_heq ((by with_unfolding_all exact ((h3'.trans ((heq_of_eq (rep_eq h1' h1 h2' h2)).trans h3.symm)) :)))
  exact (by with_unfolding_all exact ((heq_of_eq (funext h)) :))

end GlobalTheory.Mem.R3.Rw.CopyRead

end
