import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem exists_matches : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : A →+* ℂ), x ≫ genStr Z = spMap φ → ψ.comp φ = σ → (∀ s, (spMap ψ ≫ x) s ∉ genBd Z) → ∃ y : FrPt Xo c (CAt σ), Matches fr ψ y := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ hx hψ hb
  subst hψ
  have := Z.jQ_open
  have : IsLocalRing (CAt (ψ.comp φ)) := inferInstanceAs (IsLocalRing ℂ)
  let ψ' : A →+* CAt (ψ.comp φ) := ψ
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_eigFrame_baseChange' E H Dw l Xo c O β Z A (CAt (ψ.comp φ)) φ (x ≫ genι Z) fr ψ'
  have hr : Set.range (spMap ψ' ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨s, rfl⟩
    exact not_not.1 (hb s)
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = spMap ψ' ≫ x := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (CAt (ψ.comp φ))) := by
    rw [← Z.jQ_over, ← Category.assoc, hxF, Category.assoc]
    exact (congrArg (spMap ψ' ≫ ·) hx).trans (OpenReg.spMap_comp _ _)
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (R := CAt (ψ.comp φ)) xF hs
    (x := spMap ψ' ≫ x ≫ genι Z) (by rw [← Category.assoc, hxF, Category.assoc]) g
  have hp : GlobalTheory.AllWt.ptF y = xF := by
    apply pullback.hom_ext
    · rw [← hy]; exact pullback.lift_fst _ _ _
    · rw [hs]; exact pullback.lift_snd _ _ _
  refine ⟨y, by rw [hp]; exact hxF, fun τ i => ⟨w τ i, by rw [hp]; exact (hw τ i).1, (hw τ i).2.1, ?_⟩⟩
  exact (hw τ i).2.2.trans (hg τ i)

end GlobalTheory.ShFam.BdArc
