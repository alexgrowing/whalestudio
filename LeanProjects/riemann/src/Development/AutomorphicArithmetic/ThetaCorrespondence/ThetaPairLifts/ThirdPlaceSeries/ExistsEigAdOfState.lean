import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigSpanOfIsotInternal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAdOfRowEig
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.RatSide
theorem exists_eigAd_of_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∃ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig := by
  intro hL
  refine (StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.eigAd_of_rowEig_alt hL) GlobalTheory.HeckeField.Gap.rowEig_mem_fixedField).trans (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx hL' h3 h5
  classical
  refine ⟨fun j σ k Pl => if h : ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) =
      hkNorm x.m.z.R (idxOf (Dof x) j) k Pl *
        GlobalTheory.EigRows.rowEig x.r.Y (idxOf (Dof x) j) σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) then h.choose else 0,
    H.1 P x hx _ ?_⟩
  intro i σ k Pl α Rr hk hg h0
  have t2 := H.2 P x hL' h3 h5 i σ k Pl α Rr hk h0
  have hI := congrArg (fun i' : Fin (Dof x).R.m => hkNorm x.m.z.R i' k Pl *
      GlobalTheory.EigRows.rowEig x.r.Y i' σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k)) (NX.idxOf_succ (Dof x) i)
  have hex : ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) =
      hkNorm x.m.z.R (idxOf (Dof x) (i.1 + 1)) k Pl *
        GlobalTheory.EigRows.rowEig x.r.Y (idxOf (Dof x) (i.1 + 1)) σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) :=
    let ⟨c, hc⟩ := t2; ⟨c, hc.trans hI.symm⟩
  refine Eq.trans ?_ (hex.choose_spec.trans hI)
  simp only [dif_pos hex]
end GlobalTheory.HeightCounting.RatSide
end
