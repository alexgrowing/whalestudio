import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

namespace GlobalTheory.BaseDim

theorem two_card_psi (E : Type) [Field E] [NumberField E] [IsCMField E] {r : ℕ} (D : ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    2 * D.Ψ.card = Module.finrank ℚ E := Formalism.L2.Pj.DatLin.two_card D.cmType

theorem eq_of_smooth_two {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    (m n : ℕ) (hm : SmoothOfRelativeDimension m f) (hn : SmoothOfRelativeDimension n f) : m = n := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := genericPoint X) trivial
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  obtain ⟨α, hα⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  algebraize [α.hom]
  have t₁ := trdeg_eq_of_smoothOfRelativeDimension K X f m hm Γ(X, U) hU.fromSpec inferInstance hα.symm
  have t₂ := trdeg_eq_of_smoothOfRelativeDimension K X f n hn Γ(X, U) hU.fromSpec inferInstance hα.symm
  exact_mod_cast t₁.symm.trans t₂

theorem card_eq_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ Φ k X j f f₀ Eb A₀ hj hL
  have hoi : IsOpenImmersion j := hL.1
  have hs : SmoothOfRelativeDimension Dw.dim (genStr T.Z) := T.smooth
  have hi : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have h0 : SmoothOfRelativeDimension 0 (spMap e.toRingHom) := inferInstance
  have h2 : SmoothOfRelativeDimension (Dw.dim + 0) (genStr T.Z ≫ spMap e.toRingHom) := inferInstance
  rw [Nat.add_zero] at h2
  have h1 : SmoothOfRelativeDimension (0 + Dw.dim) (j ≫ genStr T.Z ≫ spMap e.toRingHom) := inferInstance
  rw [hj, Nat.zero_add] at h1
  have hd : Dw.dim = X.dim := eq_of_smooth_two X.X X.str Dw.dim X.dim h1 X.smooth
  rw [← hd, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim, ← two_card_psi E (U.X k), Nat.mul_div_cancel_left _ two_pos]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.add_sub_cancel_left, Nat.mul_assoc]

end GlobalTheory.BaseDim
