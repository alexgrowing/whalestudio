import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianGenericIsogenyExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_generic_isogeny_extension : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.Published.BarsottiTateDieudonne → GlobalTheory.CovTop.Hypotheses2 → ∀ (O : Type) [CommRing O] (c : O →+* O) (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C → ∀ (G₀ : Over C) [GrpObj G₀] [IsSemiAbelian G₀] (i₀ : OAct O G₀), AbGen c i₀ → ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct O G) (φ₀ : G.left ⟶ G₀.left), IsActPull i i₀ (frob C q (natCast_eq_zero C q k)) φ₀ → ∀ (U : C.Opens) (A : Over U.toScheme) [GrpObj A] (j : OAct O A) (φ : A.left ⟶ G.left) (h : IsGrpPullback A G U.ι φ), genericPoint C ∈ U → IsAbelianScheme A → IsActPull j i U.ι φ → ∀ P : LB (A ⊗ A).left, IsSelfDual c j P → ∀ (g : ℕ) (hg : IsVB (omega G) g) (d₀ : DieuDatumOn q k c i g U.ι), IsDRDatumOn q k c i j h P hg d₀ → ∀ x : C, x ∉ U → ∃ V : C.Opens, x ∈ V ∧ (∀ y ∈ V, y ≠ x → y ∈ U) ∧ ∃ d : DieuDatumOn q k c i g V.ι, ∃ ψ, Agree (b := C.homOfLE (inf_le_left : V ⊓ U ≤ V)) (c := C.homOfLE (inf_le_right : V ⊓ U ≤ U)) d d₀ (by simp) ψ := by
  first | exact @GlobalTheory.BadPt.exists_datum_near | exact GlobalTheory.BadPt.exists_datum_near | (intros; apply GlobalTheory.BadPt.exists_datum_near <;> assumption)
