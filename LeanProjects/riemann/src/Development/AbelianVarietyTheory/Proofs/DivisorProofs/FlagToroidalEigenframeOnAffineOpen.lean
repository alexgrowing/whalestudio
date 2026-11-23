import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusFrameSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusFrameUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointExtendsCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusEigenFrameCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusFrameTransitionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTorusFrameComponentStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

theorem mem_comp_of_frameIn : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}, ∀ {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (k : U.Comp) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → IsIntegral V.toScheme → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (y : (Φ.C k).Y.X), y ∈ Cell.cellOpen (Φ.C k) hV f₀ w → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ψ : Γ(gen Z, V) →+* Ω) (x : Sp Ω ⟶ gen Z) (hx : spMap ψ ≫ hV.fromSpec = x) (g : EigFrame Z (ψ.comp φV) (x ≫ genι Z)) (a : Cell.Coord Dw → Ω), Cell.FrameIn hV f₀ w ψ hx g a → ∀ (i : U.Comp) (p : Sp Ω ⟶ (Φ.C i).Y.X), p ≫ (Φ.C i).π = x → (Φ.C i).Carries p g → i = k := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ k V hV φV f₀ hstr hint w y hy Ω _ _ ψ x hx g a hg i p hp hc

  haveI : Nonempty V.toScheme := inferInstance
  haveI : IsDomain Γ(V.toScheme, ⊤) := inferInstance
  haveI : IsDomain Γ(gen Z, V) := (V.topIso.commRingCatIsoToRingEquiv).symm.toMulEquiv.isDomain
  let t₀ : PrimeSpectrum (MvPolynomial (Coord Dw) Γ(gen Z, V)) := ⟨⊥, Ideal.bot_prime⟩
  obtain ⟨i₀, h₀⟩ := GlobalTheory.T.exists_cell_lands_of_eigFrame Φ hV f₀ hstr w (GeoF t₀) ((geoHom t₀).comp MvPolynomial.C)
    (fun j => geoHom t₀ (MvPolynomial.X j))
  have hall : ∀ t, InComp Φ hV f₀ w i₀ t := fun t => GlobalTheory.T.flag_torus_frame_unique Φ hV f₀ hstr w i₀ t₀ t bot_le h₀

  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (ψ' : Γ(gen Z, V) →+* K) (a' : Coord Dw → K)
      (x' : Sp K ⟶ gen Z) (hx' : spMap ψ' ≫ hV.fromSpec = x') (g' : EigFrame Z (ψ'.comp φV) (x' ≫ genι Z)),
      FrameIn hV f₀ w ψ' hx' g' a' → ∀ (j : U.Comp) (p' : Sp K ⟶ (Φ.C j).Y.X), p' ≫ (Φ.C j).π = x' →
      (Φ.C j).Carries p' g' → j = i₀ := by
    intro K _ _ ψ' a' x' hx' g' hg' j p' hp' hc'
    let χ : MvPolynomial (Coord Dw) Γ(gen Z, V) →+* K := MvPolynomial.eval₂Hom ψ' a'
    let t : PrimeSpectrum (MvPolynomial (Coord Dw) Γ(gen Z, V)) := ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩
    obtain ⟨em, hem⟩ := GlobalTheory.T.geometric_point_extends_character t K χ rfl
    have h1 := GlobalTheory.T.flag_torus_eigen_frame_compat Φ hV f₀ w i₀ em _ _ (hall t)
    have e1 : em.comp ((geoHom t).comp MvPolynomial.C) = ψ' := by
      rw [← RingHom.comp_assoc, hem]; exact MvPolynomial.eval₂Hom_comp_C ψ' a'
    have e2 : (em ∘ fun j => geoHom t (MvPolynomial.X j)) = a' := by
      funext j; show (em.comp (geoHom t)) (MvPolynomial.X j) = a' j
      rw [hem]; exact MvPolynomial.eval₂Hom_X' ψ' a' j
    rw [e1, e2] at h1
    exact GlobalTheory.T.flag_torus_frame_transition Φ hV f₀ hstr w i₀ K ψ' a' h1 x' hx' g' hg' j p' hp' hc'
  obtain ⟨Ω₁, _, _, ψ₁, a₁, g₁, hg₁, p₁, hp₁, hc₁⟩ := GlobalTheory.T.flag_torus_frame_component Φ k hV f₀ hstr w y hy
  have hk := key Ω₁ ψ₁ a₁ _ rfl g₁ hg₁ k p₁ hp₁ hc₁
  have hi := key Ω ψ a x hx g hg i p hp hc
  rw [hi, hk]

end GlobalTheory.ShFam.Cell
