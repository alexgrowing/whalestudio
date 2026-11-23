import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesCharacterInverse
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.StateLevel
theorem level_char_allSt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ _ w _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x, (∀ g : Gc B w.px, x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U ↔ g ∈ x.m.z.F.P0) ∧
  ∀ i b (g : x.m.z.F.P0) (h : x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U), l.b.ser.ex.ρ.e i b ((Dof x).nexp.psiU i b ⟨_, h⟩ : (FractionRing ((Dof x).ntw.O i))ˣ) = ((Dof x).what₂.embLL (x.m.z.F.ψ0 g : (Dof x).what₂.LLˣ))⁻¹ := by
  intro hL
  refine StepW.of_all fun _ _ _ _ _ _ _ _ _ x l => ?_
  have hU : (Dof x).nexp.U = Formalism.IndefR.NX.U (Dof x).nd := l.b.Bs.exp.U_eq
  refine ⟨fun g => ?_, fun i b g h => ?_⟩
  · rw [hU]
    exact (l.rat.rat.lvl g).symm
  · have hu' : (x.m.z.R.eG.trans x.m.z.cG) g ∈ Formalism.IndefR.NX.U (Dof x).nd := hU ▸ h
    have e := l.b.Bs.psiU i b _ h hu'
    have e2 := l.rat.rat.psi g hu'
    have h1 := l.b.ser.ex.good.e_LL0 i b (psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩)
    refine (congrArg (l.b.ser.ex.ρ.e i b) e).trans (h1.trans ?_)
    change (Dof x).what₂.embLL ((psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩ : (↥(Dof x).LL0)ˣ) : (Dof x).what₂.LL) = _
    rw [e2, Units.val_inv_eq_inv_val, map_inv₀]
end GlobalTheory.StateLevel
end
