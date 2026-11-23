import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinitesimalWeightOfDual
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
namespace GlobalTheory.LocInfWt
theorem infWt_eq_infOf_alt : ∀ (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), _root_.GlobalTheory.HeightCounting.HeckeOpenStatements D M tup → ∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam := by
  intro D M tup hH i a τ lam hd hw
  obtain ⟨P, -⟩ := D.naut.pt_surj i (Classical.arbitrary (D.nd.X i))
  rw [D.nbc.embAV_inf i P, hH.emb i P,
    hH.au.wt (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (hH.av.rep i P) a hd]
  exact hH.au.infW (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 a τ lam hw
end GlobalTheory.LocInfWt
end
