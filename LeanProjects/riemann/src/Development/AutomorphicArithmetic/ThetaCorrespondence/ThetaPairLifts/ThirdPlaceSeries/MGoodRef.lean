import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodRef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M.B
end UpperTheory.One.M.B
open UpperTheory.One.M.B in
theorem UpperTheory.One.M.goodRef_alt :
    _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → UpperTheory.One.M.GoodAU (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS) := by
  intro _ hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters
  refine GlobalTheory.LiftRef.overRows_and_mono levSplit levSplit (fun K B f T w Z Wt hX z p0 Y h' _ => ?_)
  intro Rw a M tup Q hMA _ j h1 h2 S hS hne s σ hσ
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, i.1 + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hry : (M _ _ h1 h2).real y ≠ 0 := fun e =>
    hy0 ((M _ _ h1 h2).real_inj (e.trans (map_zero _).symm))
  obtain ⟨f', hf', hf0', hff'⟩ := GlobalTheory.AutUnr.exists_fixed_of_isoTyp _ hS.1.stable
    {κ | κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV ∧ TrivOutside {s.v} κ ∧ (s.v ∈ gPl (w.st Z).toD7 → IsPrincipalCongruenceAt s κ)} hy hry
    (fun κ hκ => GlobalTheory.SphInertRef.rt_real_eq_of_lev hMA i y κ (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).1
      (h' i (hMA.PV i) (hMA.std i) s κ hκ.1 hκ.2.1 hκ.2.2).2)
  exact good_of_fix _ S hS s (fun hg => GlobalTheory.SplitTypeCompl.exists_padic_equiv _ s hg) f' hf' hf0'
    (fun κ a b c => hff' κ ⟨a, b, c⟩) σ hσ
end
end
