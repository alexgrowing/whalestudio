import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigMet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem gram_eq_of_isMap {σ : c.F →+* ℂ} (G : EigMet Z σ) {y : CxPts (genStr Z) σ} {R : Type} [CommRing R]
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {F : EigFrame Z φ x} {ψ : R →+* ℂ} {f f' : EigFrame Z σ (y.1 ≫ genι Z)}
    (hf : F.IsMap ψ f) (hf' : F.IsMap ψ f') (τ : E →+* ℂ) : G.gram y f' τ = G.gram y f τ := by
  have hc : f.co f' τ = 1 := by
    rw [← f.co_self τ]
    exact EigFrame.co_eq fun i => by rw [hf' τ i, ← hf τ i]; exact f.co_spec f τ i
  rw [G.change y f f' τ, hc, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem eq_comp_evHom {σ : c.F →+* ℂ} {V : (gen Z).affineOpens} {φ : c.F →+* Γ(gen Z, V.1)}
    (hV : LogKS.chart V ≫ genStr Z = spMap φ) {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1) :
    σ = (evHom h).comp φ := by
  have e : spMap σ = spMap ((evHom h).comp φ) := by
    rw [← y.2, ← spMap_evHom h, Category.assoc, hV, ← Spec.map_comp]
    rfl
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

theorem smoothOn_of_locally {σ : c.F →+* ℂ} (G : EigMet Z σ) (S : Set (CxPts (genStr Z) σ))
    (hloc : ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z))
      (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ y₀ ∈ S,
      y₀ ∈ ptsIn (genStr Z) σ V.1 → ∃ (T : Set (CxPts (genStr Z) σ)) (g : CxPts (genStr Z) σ → ℂ),
        IsOpen T ∧ y₀ ∈ T ∧ (manifold Z σ).SmoothOn T (fun y => (g y).re) ∧
        (manifold Z σ).SmoothOn T (fun y => (g y).im) ∧
        ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)),
          F.IsMap (evHom hy) f → G.gram y f τ a b = g y) :
    G.SmoothOn (manifold Z σ) S := by
  classical
  intro V φ F τ a b hV
  have hx : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1),
      y.1 ≫ genι Z = spMap (evHom h) ≫ LogKS.chart V ≫ genι Z := fun h => by
    rw [← Category.assoc, spMap_evHom h]
  have hex : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), F.IsMap (evHom h) f := fun h =>
    F.exists_isMap (evHom h) (eq_comp_evHom hV h) (hx h)
  let g : CxPts (genStr Z) σ → ℂ := fun y =>
    if h : y ∈ ptsIn (genStr Z) σ V.1 then G.gram y (hex h).choose τ a b else 0
  have hg : ∀ y (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)),
      F.IsMap (evHom hy) f → G.gram y f τ a b = g y := fun y hy f hf => by
    simp only [g, dif_pos hy]
    rw [gram_eq_of_isMap G (hex hy).choose_spec hf τ]
  let ι := {y₀ // y₀ ∈ S ∧ y₀ ∈ ptsIn (genStr Z) σ V.1}
  choose T gl hT hmem hre him hagree using fun j : ι => hloc V φ F τ a b hV j.1 j.2.1 j.2.2
  have hc : ∀ y ∈ S ∩ ptsIn (genStr Z) σ V.1, ∃ j, y ∈ T j := fun y hy => ⟨⟨y, hy⟩, hmem _⟩
  have heq : ∀ j, ∀ y ∈ (S ∩ ptsIn (genStr Z) σ V.1) ∩ T j, g y = gl j y := fun j y hy =>
    (hg y hy.1.2 _ (hex hy.1.2).choose_spec).symm.trans (hagree j y hy.2 hy.1.2 _ (hex hy.1.2).choose_spec)
  refine ⟨g, AnRead.smoothOn_of_cover hT hc fun j => ((hre j).mono Set.inter_subset_right).congr fun y hy => ?_,
    AnRead.smoothOn_of_cover hT hc fun j => ((him j).mono Set.inter_subset_right).congr fun y hy => ?_,
    fun y _ hy f hf => hg y hy f hf⟩
  · exact congrArg Complex.re (heq j y hy)
  · exact congrArg Complex.im (heq j y hy)

example : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} [SmoothOfRelativeDimension Dw.dim (genStr Z)] {σ : c.F →+* ℂ} (G : EigMet Z σ) (S : Set (CxPts (genStr Z) σ)), (∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ y₀ ∈ S, y₀ ∈ ptsIn (genStr Z) σ V.1 → ∃ (T : Set (CxPts (genStr Z) σ)) (g : CxPts (genStr Z) σ → ℂ), IsOpen T ∧ y₀ ∈ T ∧ (manifold Z σ).SmoothOn T (fun y => (g y).re) ∧ (manifold Z σ).SmoothOn T (fun y => (g y).im) ∧ ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)), F.IsMap (evHom hy) f → G.gram y f τ a b = g y) → G.SmoothOn (manifold Z σ) S := fun G S h => smoothOn_of_locally G S h

end GlobalTheory.ShFam.EigMet
