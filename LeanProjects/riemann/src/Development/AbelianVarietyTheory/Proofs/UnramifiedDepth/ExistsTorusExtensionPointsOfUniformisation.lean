import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.QRelExistsUniqueMulNat
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsStruct
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThickeningQuotientImageOneIffExistsTorusImageStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartLiftSquareZeroUnitPointStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ThickMapCompFstG
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorusPointRelationSuccThickeningStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AppTopCharUnitOfTorusEndOf

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem kills_mono {R : Type} [CommRing R] {I : Ideal R} {k l : ℕ} (hkl : k ≤ l) {S : Type} [CommRing S]
    [Algebra R S] (h : Kills I k S) : Kills I l S :=
  fun t ht => h t (Ideal.pow_le_pow_right (by omega) ht)

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
  {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : Out.UnifPre I D A G) (S : Type) [CommRing S] [Algebra R S]

private theorem qRel_mono {k l : ℕ} (hkl : k ≤ l) {z y} (h : QRel (U.gt k) S z y) : QRel (U.gt l) S z y := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact GlobalTheory.ChF.qRel_succ R I D A G U n S z y ih

private theorem iRel_mono {k l : ℕ} (hkl : k ≤ l) {χ z} (h : IRel (U.gt k) S χ z) : IRel (U.gt l) S χ z := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact GlobalTheory.T.torus_point_relation_succ_thickening R I D A G U n S χ z ih

private def qFun (h : ∃ k, Kills I k S) (z : sp (R₀ := R) S ⟶ G) : sp (R₀ := R) S ⟶ D.toPre.P.A :=
  (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 z).exists.choose

private theorem qFun_spec (h : ∃ k, Kills I k S) (z : sp (R₀ := R) S ⟶ G) :
    QRel (U.gt h.choose) S z (qFun U S h z) :=
  (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 z).exists.choose_spec

private theorem qFun_eq (h : ∃ k, Kills I k S) {k : ℕ} {z y} (hq : QRel (U.gt k) S z y) : qFun U S h z = y :=
  (((qRel_existsUnique_mul_nat R I _ _ G (U.gt (max h.choose k))).1 S
    (kills_mono (le_max_left _ _) h.choose_spec)).1 z).unique
    (qRel_mono U S (le_max_left _ _) (qFun_spec U S h z)) (qRel_mono U S (le_max_right _ _) hq)

private def iFun (h : ∃ k, Kills I k S) (χ : Multiplicative D.toPre.X →* Sˣ) : sp (R₀ := R) S ⟶ G :=
  (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 χ).exists.choose

private theorem iFun_spec (h : ∃ k, Kills I k S) (χ : Multiplicative D.toPre.X →* Sˣ) :
    IRel (U.gt h.choose) S χ (iFun U S h χ) :=
  (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 χ).exists.choose_spec

private theorem iFun_eq (h : ∃ k, Kills I k S) {k : ℕ} {χ z} (hq : IRel (U.gt k) S χ z) : iFun U S h χ = z :=
  (((GlobalTheory.irel_points R I _ _ G (U.gt (max h.choose k))).1 S
    (kills_mono (le_max_left _ _) h.choose_spec)).1 χ).unique
    (iRel_mono U S (le_max_left _ _) (iFun_spec U S h χ)) (iRel_mono U S (le_max_right _ _) hq)

end

private def ptExt {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
    {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Out.UnifPre I D A G) : PtExt I G D.toPre.P.A D.toPre.X where
  q S _ _ h := MonoidHom.mk' (qFun U S h) fun z z' => qFun_eq U S h
    (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2 _ _ _ _
      (qFun_spec U S h z) (qFun_spec U S h z'))
  i S _ _ h := MonoidHom.mk' (iFun U S h) fun χ χ' => iFun_eq U S h
    (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2.1 _ _ _ _
      (iFun_spec U S h χ) (iFun_spec U S h χ'))
  q_nat S _ _ S' _ _ φ h h' z := qFun_eq U S' h'
    ((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).2 S S' φ _ _ (qFun_spec U S h z))
  i_nat S _ _ S' _ _ φ h h' χ := iFun_eq U S' h'
    ((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).2 S S' φ _ _ (iFun_spec U S h χ))
  i_inj S _ _ h χ χ' e := by
    have e' : iFun U S h χ = iFun U S h χ' := e
    exact ((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2.2 _ _ _
      (iFun_spec U S h χ) (e' ▸ iFun_spec U S h χ')
  exact S _ _ h z := by
    have key := GlobalTheory.T.thickeningQuotientImage_one_iff_exists_torusImage R I _ h.choose G (U.gt h.choose) S h.choose_spec z
    constructor
    · intro e
      have e' : qFun U S h z = 1 := e
      obtain ⟨χ, hχ⟩ := key.1 (e' ▸ qFun_spec U S h z)
      exact ⟨χ, iFun_eq U S h hχ⟩
    · rintro ⟨χ, e⟩
      have e' : iFun U S h χ = z := e
      exact qFun_eq U S h (key.2 ⟨χ, e' ▸ iFun_spec U S h χ⟩)
  lift S _ _ h S' _ _ ρ σ h1 h2 y hy := by
    obtain ⟨z, hz, hq⟩ := GlobalTheory.T.abelianPart_lift_square_zero_unit_point R I _ h.choose G (U.gt h.choose) S h.choose_spec S' ρ σ h1 h2 y hy
    exact ⟨z, hz, qFun_eq U S h hq⟩

theorem exists_ptExt_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G), ∃ E : PtExt I G D.toPre.P.A D.toPre.X, ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (a : OE) (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S), (∀ z, E.q S h (z ≫ io.act a) = E.q S h z ≫ oD.onB.act a) ∧ ∀ χ χ', (∀ x, χ' (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd (star a • x))) → E.i S h χ ≫ io.act a = E.i S h χ' := by
  intro R _ _ I D A G _ _ U
  refine ⟨ptExt U, ?_⟩
  intro OE _ _ _ io oD oA hL a S _ _ h
  have key := qRel_iRel_equivariant R I D A G U OE io oD oA hL h.choose a S
  refine ⟨fun z => qFun_eq U S h (key.1 _ _ (qFun_spec U S h z)), fun χ χ' e => ?_⟩
  exact (iFun_eq U S h (key.2 _ _ _ e (iFun_spec U S h χ))).symm

end GlobalTheory.ChF
