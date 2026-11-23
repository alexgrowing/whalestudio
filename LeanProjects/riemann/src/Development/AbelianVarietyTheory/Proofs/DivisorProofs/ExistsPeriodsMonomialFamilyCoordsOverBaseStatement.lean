import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsMonomialFamilyCoordsOverBase
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periods_monomialFamily_coords_over_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (β : C.P.D.toPre.P.A.left ⟶ L.D.P.A.left), IsGrpPullback C.P.D.toPre.P.A L.D.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (C.P.oD.onB.act a).left ≫ β = β ≫ (L.oa.onB.act a).left) → LBIso C.P.D.toPre.P.L (L.D.P.L.pull β) → (∀ y, (C.P.D.toPre.c y).left ≫ β = spMap θ₀ ≫ (L.D.c (l.M' • e y)).left) → ∀ (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)), (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) → ∃ s : Fin C.m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  first | exact @GlobalTheory.UCanon.Periods.exists_divFrom | exact GlobalTheory.UCanon.Periods.exists_divFrom | (intros; apply GlobalTheory.UCanon.Periods.exists_divFrom <;> assumption)
