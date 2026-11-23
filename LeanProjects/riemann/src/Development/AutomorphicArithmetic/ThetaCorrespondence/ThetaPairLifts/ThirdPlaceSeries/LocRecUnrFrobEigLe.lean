import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowSphSmall
open GlobalTheory.CuspRep.ParLaws GlobalTheory.LocLanglands
theorem reciprocity_unramified_and_norm_frobenius_eigenvalue_le (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : Formalism.ConjugateSelfDual.IsPlaceOver A w)
    {n : ℕ} (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))) (hs : GlobalTheory.SmGL.IsSpherical σ.ρ)
    (hu : GlobalTheory.SmGL.IsUnitarisable σ.ρ) :
    (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).unr ∧
      ∀ α ∈ (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).frobEig, ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have H := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h
  have hunr : (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h (cls σ)).unr := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical H σ).2 hs
  refine ⟨hunr, ?_⟩
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt H hunr
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hα, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  have h1 := GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake E w n (GlobalTheory.SplitRead.Irr.ofIrrRep σ) α hα hu
  have h2 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n
      ((Finset.univ.val.map fun i => (α i : ℂ)).map (·⁻¹)) := by
    have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.SatakeInv.isUnitarySatake_map_inv _ _ _ _ h1
  intro b hb
  apply h2.norm_le
  simpa [Multiset.map_map, Function.comp_def] using hb
end GlobalTheory.RowSphSmall
section FormSec
namespace GlobalTheory.RowSphSmall
end GlobalTheory.RowSphSmall
end FormSec
namespace GlobalTheory.RowSphSmall
end GlobalTheory.RowSphSmall
end
