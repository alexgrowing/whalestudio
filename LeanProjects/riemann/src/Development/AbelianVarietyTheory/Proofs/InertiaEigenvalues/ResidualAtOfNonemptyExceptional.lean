import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OverNEOfNEb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtraBoundOfTwistingEigenFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingEigenOfDepthZeroSupportStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowClosureAtPrimeStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.NLink.CloseMem

theorem main : GlobalTheory.NLink.Hypotheses₂ → GlobalTheory.HeightCounting.HtCard → PrN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), WitMv (prmR N S Γ).s → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → (AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => GlobalTheory.NFacts.Facts (w.D Z) nch) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  intro hPr hHt hPrN hW hS hL N S Γ hWit hNE hFacts hAt23
  obtain ⟨C, CT, hC, hEx⟩ := GlobalTheory.T.extra_bound_of_twisting_eigen_facts hPr
  have hTf := GlobalTheory.T.twisting_eigen_of_depth_zero_support hHt hPrN hW hS hL
  have hExM : AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => GlobalTheory.NLink.Extra (w.D Z) C CT :=
    GlobalTheory.HeightCounting.Up.Model.AtMem.imp (GlobalTheory.HeightCounting.Up.Model.AtMem.and hFacts hTf)
      fun _ _ _ _ w Z _ _ _ nch _ _ h => hEx (w.D Z) nch h.1 h.2
  have hTr := (GlobalTheory.Mem.AtPtTransport.atMem_at_wit hL N S Γ hWit hNE).2
  exact GlobalTheory.T.row_closure_at_prime hPr hL (prmR N S Γ) C CT hC
    (hTr (fun D nch => GlobalTheory.NFacts.Facts D nch) hFacts)
    (hTr (fun D _ => GlobalTheory.NLink.Extra D C CT) hExM) hAt23

end GlobalTheory.NLink.CloseMem
