import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtFJQOver
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.FD

set_option autoImplicit false

namespace GlobalTheory.ShFam.Horiz

theorem frameCast_v {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x x' : Sp R ⟶ Z.X} (h : x = x')
    (g : EigFrame Z φ x) : (frameCast h g).v = g.v := by
  subst h; rfl

theorem per_cxOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (r g : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (k : U.Comp) (i : Fin Fu.n) (y : (U.X k).dom) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)), IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm → (U.un k y).x = Fu.u i Pm → (∀ τ (a : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fu.ex i Pm z).left) (Pi.single (e.symm ⟨τ, a⟩) 1) ((U.un k y).u τ a)) → ∀ Q : (Fu.Di i).La →+ (Letter Dw → ℂ), (∀ v z, Q v z = Pm v (e.symm z)) → Per Fu (GlobalTheory.ShFam.Horiz.cxOf Z (U.un k y)) i Q := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ r g U e Fu k i y Pm hP hx hd Q hQ
  refine ⟨Pm, fun z => Pi.single (e.symm z) 1, GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k y), hP, ?_, rfl, ?_, ?_⟩
  · exact (GlobalTheory.ShFam.Descent.ptF_fst (U.un k y)).trans hx
  · intro z
    obtain ⟨w, h1, h2, h3⟩ := (tie_frameOf Z (U.un k y)).2.2 z.1 z.2
    refine ⟨w, h1, ?_, ?_⟩
    · refine h3.trans ?_
      have := frameCast_v (φ := σ) (Category.assoc (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k y)) Z.jQ (genι Z)).symm
        (frameOf (R := CAt σ) Z (U.un k y))
      exact (congrFun (congrFun this z.1) z.2).symm
    · have := hd z.1 z.2
      rw [← h2] at this
      exact this
  · intro v
    simp only [hQ]
    rw [Fintype.sum_equiv e.symm (fun z => Pm v (e.symm z) • (Pi.single (e.symm z) 1 : Fin g → ℂ))
      (fun j => Pm v j • (Pi.single j 1 : Fin g → ℂ)) (fun _ => rfl)]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]

end GlobalTheory.ShFam.Horiz
