import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingDominatesPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusFrameSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusEigenFrameCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointExtendsCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusFrameSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusFrameTransitionStatement
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

theorem inComp_of_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}, ∀ (Φ : FlagTor Z e U) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (i : U.Comp) (t t' : PrimeSpectrum (MvPolynomial (Cell.Coord Dw) Γ(gen Z, V))), t ≤ t' → Cell.InComp Φ hV f₀ w i t → Cell.InComp Φ hV f₀ w i t' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ V hV φV f₀ hstr w i t t' hle hIn
  obtain ⟨R, _, _, _, _, _, χR, hχ, hker⟩ := GlobalTheory.T.valuation_ring_dominates_point t t' hle
  have hIn' : Lands Φ hV f₀ w i ((algebraMap R (GeoF t)).comp (χR.comp MvPolynomial.C))
      (algebraMap R (GeoF t) ∘ (fun j => χR (MvPolynomial.X j))) := by
    have h1 : (algebraMap R (GeoF t)).comp (χR.comp MvPolynomial.C) = (geoHom t).comp MvPolynomial.C := by
      rw [← hχ]; rfl
    have h2 : (algebraMap R (GeoF t) ∘ (fun j => χR (MvPolynomial.X j))) = (fun j => geoHom t (MvPolynomial.X j)) := by
      rw [← hχ]; rfl
    rw [h1, h2]; exact hIn
  have hk := GlobalTheory.T.flag_torus_frame_smooth Φ hV f₀ w i R (GeoF t) (χR.comp MvPolynomial.C) (fun j => χR (MvPolynomial.X j)) hIn'
  set k := IsLocalRing.ResidueField R
  set em := algebraMap k (AlgebraicClosure k)
  have hΩ := GlobalTheory.T.flag_torus_eigen_frame_compat Φ hV f₀ w i em _ _ hk
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.geometric_point_extends_character t' (AlgebraicClosure k) (em.comp ((IsLocalRing.residue R).comp χR)) (by
    rw [RingHom.ker_comp_of_injective _ em.injective, hker])
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_cell_lands_of_eigFrame Φ hV f₀ hstr w (GeoF t') ((geoHom t').comp MvPolynomial.C) (fun j => geoHom t' (MvPolynomial.X j))
  have hj' := GlobalTheory.T.flag_torus_eigen_frame_compat Φ hV f₀ w j κ _ _ hj
  have e1 : κ.comp ((geoHom t').comp MvPolynomial.C) = em.comp ((IsLocalRing.residue R).comp (χR.comp MvPolynomial.C)) := by
    rw [← RingHom.comp_assoc, hκ]; rfl
  have e2 : (κ ∘ fun j => geoHom t' (MvPolynomial.X j)) = em ∘ (IsLocalRing.residue R ∘ fun j => χR (MvPolynomial.X j)) := by
    funext x; exact congrArg (fun f => f (MvPolynomial.X x)) hκ
  rw [e1, e2] at hj'
  obtain ⟨g, hg, p, hp, hc⟩ := hj'
  have hji := GlobalTheory.T.flag_torus_frame_transition Φ hV f₀ hstr w i _ _ _ hΩ _ rfl g hg j p hp hc
  subst hji
  exact hj

end GlobalTheory.ShFam.Cell
