import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegeneratingMonomialFamilyAlgClosedResidueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalChartVersalityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem exists_tautB_chart_at : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTautB C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hB, hac, hnt, hC, hV⟩ :=
    GlobalTheory.T.exists_degenerating_monomialFamily_algClosed_residue Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨k, _, m, e, C₁, ξ, θ, hT, hC₁, hθ, hξ⟩ :=
    GlobalTheory.T.exists_tautological_chart_versality Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS V hB hac C ξV hnt hC
  refine ⟨k, inferInstance, m, e, C₁, ξ, hT, hC₁, ?_⟩
  rw [← hV, ← hξ]
  change _ = ξ.base ((spMap θ).base (closedPoint V))
  have h0 : (spMap θ).base (closedPoint V) = closedPoint (ChartRing k m e) := by
    haveI := hθ
    exact IsLocalRing.comap_closedPoint θ
  rw [h0]

end GlobalTheory.UCanon
