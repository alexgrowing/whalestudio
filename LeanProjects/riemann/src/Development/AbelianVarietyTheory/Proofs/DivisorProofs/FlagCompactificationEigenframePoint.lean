import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentTriEquation
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieSmooth

theorem coord_eqn_inv_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) {k : Type} [Field k] [NumberField k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (p : Sp k ⟶ Y.Y.X) (g : EigFrame Z φ x) (n : Letter Dw → ℤ), Y.Carries p g → ∃ a : k, a ≠ 0 ∧ IsCoord Y p g n (((eqn (divOf Y n) (below p))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) a := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y k _ _ φ x p g n hC
  obtain ⟨y, ψ, φ₁, f, t, t', h₁, h₂, h₃⟩ := hC
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  haveI : IsLocalHom ψ := CoordUniq.isLocalHom_of_algebraic φ₁ ψ
  have hb : below p = y := by
    rw [h₁]
    change Y.Y.X.fromSpecStalk y (spMap ψ (IsLocalRing.closedPoint k)) = y
    rw [show spMap ψ (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint (Y.Y.X.presheaf.stalk y) from
      IsLocalRing.comap_closedPoint ψ, Scheme.fromSpecStalk_closedPoint]
  have ht : ∀ τ i, (Y.gr τ i).IsEqn y (t τ i) := GalCarry.triEqn _ _ _ _ _ _ _ _ _ _ _ Y y φ₁ f t h₂
  have hE : ∀ s : Finset (Letter Dw), (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn y (∏ z ∈ s, t z.1 z.2 ^ n z) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using GlobalTheory.Cartier.CartierDiv.isEqn_zero y
    | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht _ _).zsmul _).add ih
  obtain ⟨r, hr, hr'⟩ := (isEqn_eqn (divOf Y n) y).iff_unitAt.1 (hE Finset.univ)
  refine ⟨ψ r * ((∏ z : Letter Dw, t' z.1 z.2 ^ (-n z) : kˣ) : k), mul_ne_zero (hr.map ψ).ne_zero (Units.ne_zero _),
    y, ψ, φ₁, f, t, t', r, h₁, h₂, h₃, ?_, rfl⟩
  rw [hb, hr', Units.val_inv_eq_inv_val, div_eq_inv_mul]

end GlobalTheory.LieSmooth
