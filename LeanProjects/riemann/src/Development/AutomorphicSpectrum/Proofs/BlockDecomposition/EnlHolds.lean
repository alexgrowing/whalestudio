import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.TTRANS
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBCBaseChange
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.BaseChangeData

theorem enl_holds : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.Th.ENL K := by
  intro K _ _ _ c S hS
  classical
  have hB : ({w : PlK K | w.asIdeal ∣ differentIdeal ℤ (𝓞 K)}).Finite :=
    Ideal.finite_factors GroundTheory.Global.differentIdeal_ne_bot
  refine ⟨(S ∪ hB.toFinset).image below, fun v hv w _ => ?_⟩
  have hvw : v = below w := eq_below v w
  have hw : w ∉ S ∪ hB.toFinset := fun h => hv (hvw ▸ Finset.mem_image_of_mem below h)
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hw
  refine ⟨hS w hw.1, ?_⟩
  by_contra hne
  exact hw.2 ((dvd_different_iff w).2 hne)

end GlobalTheory.CompanionTheory.BaseChangeData
