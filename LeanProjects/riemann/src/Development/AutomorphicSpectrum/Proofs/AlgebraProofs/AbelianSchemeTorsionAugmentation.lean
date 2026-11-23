import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAddEquiv
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsFiniteFlatSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsIsogenyHopfOrderStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHomomorphismCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrderStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderPullbackAlongHomStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenerationAlongInvariantsStatement

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem one_comp_monHom {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    [IsMonHom f] : (1 : T ⟶ G) ≫ f = 1 := by
  simp [Hom.one_def]

theorem sub_abelianScheme : QuotientByFiniteFlatStatement → ZarhinStatement →
    HodgeTateDatumStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R →
    v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R →
    ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A →
    L.IsLB → Out.RelAmple A L → ∀ (T : TorsRep A p) (N : Type) [AddCommGroup N] [Fintype N]
    [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt →
    ∀ K : AddSubgroup N, GenAF p (torsFun C T pt) K := by
  intro hQ hZ hD p _ C _ _ _ v R _ _ hint hp hc A _ L hA hL hamp T N _ _ _ pt hpt K
  haveI : IsCommMonObj A := hA.comm
  have hsub := GlobalTheory.T.torsion_points_finite_flat_subgroup p C v R hint hp A T N pt hpt K
  obtain ⟨A', _, L', q, hA', hL', hamp', hq, -, -, -, hker⟩ := hQ R A L hA hL hamp _ _ hsub
  obtain ⟨P, i, r, hi, hr, hir⟩ := hZ C v R hint A' L' hA' hL' hamp'
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI := hq
  haveI := hi
  haveI := hr
  have hj : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A),
      z ≫ (q ≫ i) = 1 ↔ ∃ φ : (T.A ⧸ vanIdeal T pt K) →ₐ[R] S,
        spMap φ ≫ (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) = z := by
    intro S _ _ z
    rw [← hker S z]
    constructor
    · intro h
      have h1 : (z ≫ q ≫ i) ≫ r = z ≫ q := by simp [hir]
      rw [← h1, h, one_comp_monHom]
    · intro h
      rw [← Category.assoc, h, one_comp_monHom]
  letI : Algebra ℤ_[p] R := (Av.zpLift p R hc).toAlgebra
  obtain ⟨⟨T'⟩, cp, -, -, pt', hpt', -⟩ := hD p C v R hint hp hc P
  have hjm : IsMonHom (q ≫ i) := inferInstance
  obtain ⟨jN, -, hjN, -, hpull⟩ := GlobalTheory.T.torsion_points_isogeny_hopf_order p C v R hint hp A P.A T N pt hpt T' _ pt' hpt'
    (q ≫ i) hjm
  obtain ⟨hK, hid⟩ := GlobalTheory.T.torsion_points_homomorphism_compatible p C v R hint hp A P.A T N pt hpt T' _ pt' hpt' (q ≫ i) hjm K
    hj jN hjN
  obtain ⟨⟨AA, hAA⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hint hp A T N pt hpt
  obtain ⟨⟨AP, hAP⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hint hp P.A T' _ pt' hpt'
  have hinv := GlobalTheory.T.hopf_order_pullback_along_hom p C v R hint hp N AA _ AP jN
    (by rw [hAA, hAP]; exact hpull) (by rw [hAA, hAP]; exact hid)
  rw [hAA, hAP, hK] at hinv
  exact GlobalTheory.T.generation_along_invariants p C R N _ _ _ jN K hinv (gp_polAV hD p C v R hint hp hc P T' _ pt' hpt').1

end GlobalTheory.CompanionTheory.Ar.GR
