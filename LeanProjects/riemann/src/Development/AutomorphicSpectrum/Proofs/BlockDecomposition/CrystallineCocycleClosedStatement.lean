import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosed
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_cocycle_closed : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X)
    {R : Type} [CommRing R] (c : R →+* b.R) (N : ℕ),
    (∀ T k, N ≤ k → ∀ x ∈ (G.obj T).J, (k.factorial : (G.obj T).B) * (G.obj T).δ.dpow (k + 1) x = 0) →
    (∀ Λ : B.CLift G D, CH.d _ 2 (Λ.coc c N) = 0) ∧
    ∀ (Λ Λ' : B.CLift G D) hz hz', (CH.cx _).cls (Λ.coc c N) hz = (CH.cx _).cls (Λ'.coc c N) hz' := by
  first | exact @GlobalTheory.CompanionTheory.CocCls.coc_cls | exact GlobalTheory.CompanionTheory.CocCls.coc_cls | (intros; apply GlobalTheory.CompanionTheory.CocCls.coc_cls <;> assumption)
