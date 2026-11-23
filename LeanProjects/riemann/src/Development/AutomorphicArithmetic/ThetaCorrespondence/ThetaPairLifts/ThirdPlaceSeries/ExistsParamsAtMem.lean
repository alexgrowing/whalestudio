import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2
open Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField GlobalTheory.EX GlobalTheory.EX.OB
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SizePar
theorem exists_params_atMem_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L) := by
  refine (evG_of_ev GlobalTheory.PrimIn.AtData.ev_params).imp fun K _ _ _ _ hK => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
    fun B f T hO _ _ _ _ w Z Wt p0 t nch n xd c _ _ _ => ?_⟩
  obtain ⟨L, -, -, hp, -⟩ := hK (w.st Z) hO t.etaF fun v hv j h1 h2 => by
    have key : ∀ v', (w.D Z).what₂.muAt v' = (w.D Z).what₂.mu0 → v' ∉ Wt := by
      intro v' he hw
      have he' : (w.st Z).W.muAt v' = (w.st Z).C.mu0 := he
      rw [t.mu.on v' hw] at he'
      have h1 := t.mu.tw v'
      rw [he', t.mu.mu0] at h1
      exact (TwFin.tw_fin B f T).2.1 v' h1.symm
    change (w.D Z).what₂.Aj j v = 0
    replace hv : (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 := hv
    have a := t.untw v (key v hv) j h1 h2
    have b := t.untw _ (key _ (((w.D Z).what₂.muAt_conj v).trans hv)) j h1 h2
    unfold Formalism.BasicNotions.Rows.Data.Aj
    rw [hv, a.1, a.2, b.1]
    rfl
  exact ⟨L, hp⟩
end GlobalTheory.HeightCounting.Up.SizePar
namespace GlobalTheory.HeightCounting.Up.SizePar
end GlobalTheory.HeightCounting.Up.SizePar
namespace GlobalTheory.HeightCounting.Up.SizePar
theorem exists_params_alt :
    (∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧
      AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧
        ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) :=
  ⟨_root_.GlobalTheory.HeightCounting.Up.SizePar.exists_params_atMem_alt, exists_params_allSt⟩
end GlobalTheory.HeightCounting.Up.SizePar
end
end
