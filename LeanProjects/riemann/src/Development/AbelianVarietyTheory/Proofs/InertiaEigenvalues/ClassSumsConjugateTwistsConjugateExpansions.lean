import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaSeriesFlatVectorsTwistedWeilStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemGfCOfSuppAtIdem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceClassSum

theorem classSum_conj_place : ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → B.admitted ψ.Q →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j B ψ ψ' →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u → ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc → κ ≠ 0 →
  ∀ τ : ℂ ≃+* ℂ, FixBase X.core X.R.toRealDat j τ → FixDat B τ → ConjChar τ ψ ψ' → ∀ ω ω' : PairRep (Vc D j) (Wc D j), B.IsWeil ψ.chi ω → B.IsWeil ψ'.chi ω' →
  ∃ ζ : ℂ, IsRoot1 ζ ∧ ∀ (I : Type) [Fintype I] (rep : I → GA D (Vc D j)), (∀ a, rep a ∈ GfC (Vc D j)) → ∀ F F' : Amb D j,
    ConjAt (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ τ F F' →
    ConjFun (X.geo.O j) (X.geo.κ j) τ ζ (κ • B.classSum ω ψ rep F) (κ • B.classSum ω' ψ' rep F') := by
  intro D X j B hB ψ ψ' hψ hψ' hadm hT u cc κ hu hc hκ τ hτ hfd hcc ω ω' hω hω'
  obtain ⟨T0', A', R', F', v₀', O', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, t, t', ht, ht'⟩ := hT
  obtain ⟨c', u', hc', hu', hio⟩ := h11 cc u hc hu
  obtain ⟨ζ, hζ, H⟩ := GlobalTheory.T.conjugate_thetaSeries_flatVectors_twistedWeil GlobalTheory.chartIndependence_unconditional D _ _ T0' A' X.core R' F' X.geo.κ v₀' O' (fun _ => 1) X.size
    h1 h2 h3 h4 h5 j h6 h7 c' hc' u' hu' B hB h8 τ (h9 τ hτ) hfd ω ω' ψ ψ' t t' hω hω' hψ hψ' hadm ht ht' hcc
  have hz : GlobalTheory.ConjSpan.RelConj (O' j) (X.geo.κ j) τ :=
    GlobalTheory.ConjRelation.expands_zero_conj D _ _ T0' A' X.core R' F' X.geo.κ v₀' h1 h3 j Unit _ (O' j) h6.2 τ hτ.core
  refine ⟨ζ, hζ, fun I _ rep hrep F F' hF => h10 _ _ _ _ ?_⟩
  have := GlobalTheory.ConjSpan.classSum_conj (R'.ioP j (PiTensorProduct.tprod ℂ u')) c' hz hκ hcc.1 H I rep hrep F F' fun h => by
    obtain ⟨x, x', hx, e, e'⟩ := hF h
    exact ⟨x, x', hx, e.trans (hio x).symm, e'.trans (hio _).symm⟩
  rwa [one_mul] at this

end GlobalTheory.PlaceClassSum
