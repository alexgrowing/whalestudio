import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianGenericExtendsOverOpen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_generic_extends_over_open : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → ∀ (O : Type) [CommRing O] (c : O →+* O) (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C → ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct O G), AbGen c i → ∃ (U : C.Opens) (A : Over U.toScheme) (_ : GrpObj A) (j : OAct O A) (φ : A.left ⟶ G.left) (h : IsGrpPullback A G U.ι φ) (P : LB (A ⊗ A).left) (g : ℕ) (hg : IsVB (omega G) g) (d₀ : DieuDatumOn q k c i g U.ι), genericPoint C ∈ U ∧ IsAbelianScheme A ∧ IsActPull j i U.ι φ ∧ IsSelfDual c j P ∧ IsDRDatumOn q k c i j h P hg d₀ := by
  first | exact @GlobalTheory.AbDatum.main | exact GlobalTheory.AbDatum.main | (intros; apply GlobalTheory.AbDatum.main <;> assumption)
