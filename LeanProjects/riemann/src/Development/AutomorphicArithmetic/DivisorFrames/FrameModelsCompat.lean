import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

section
open GlobalTheory.ShFam.Pad.Pull GlobalTheory.LieMet MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)

attribute [local instance] Over.cartesianMonoidalCategory

private theorem frame_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l}
    {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)
    {f : c.F →+* R} {u : Vecs Dw t R} (h : GlobalTheory.LocM.IsFrame t f x u) :
    ∃ v : Vecs Dw t' R, GlobalTheory.LocM.IsFrame t' f x' v ∧ ∀ τ i, v τ i ≫ mu.φ = u τ i := by
  have ex : ∀ τ i, ∃ V : TanM x' t'.G, pushE mu x' hx V = tanOf (h.1 τ i).1 := fun τ i =>
    (pushE mu x' hx).surjective _
  choose V hV using ex
  have e : ∀ τ i, (tv (V τ i)).left ≫ mu.φ = u τ i := fun τ i => congrArg (fun z => (tv z).left) (hV τ i)
  refine ⟨fun τ i => (tv (V τ i)).left, ⟨fun τ i => ⟨isTan_tv _, fun a => ?_⟩, fun τ w hw he => ?_⟩, e⟩
  · refine (eig_iff (V τ i) a _).2 ((pushE mu x' hx).injective ?_)
    rw [pushE_act, map_smul, hV]
    exact (eig_iff _ a _).1 ((h.1 τ i).2 a)
  · have := h.2 τ (w ≫ mu.φ) (isTan_push mu x' hx hw) fun a => by
      rw [Category.assoc, ← mu.act, ← Category.assoc, he, Category.assoc]
    refine (existsUnique_congr fun cf => comb_push mu hx (fun i => isTan_tv (V τ i)) hw cf).1 ?_
    simpa only [e] using this

end

theorem UpperTheory.frame_models_compat :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O₁ O₂ : Type) [CommRing O₁] [CommRing O₂] (β₁ : O₁ →+* c.F) (β₂ : O₂ →+* c.F) (Z₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β₁) (Z₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β₂) (R : Type) [CommRing R] (y : Sp R ⟶ Xo.XF c) (f : c.F →+* R) (u₂ : Vecs Dw Z₂.t R), LocM.IsFrame Z₂.t f (y ≫ Z₂.j) u₂ → ∃ u₁ : Vecs Dw Z₁.t R, LocM.IsFrame Z₁.t f (y ≫ Z₁.j) u₁ ∧ ∀ σ i, Transp Z₁ Z₂ y (u₁ σ i) (u₂ σ i) := by
  intro E _ _ _ H Dw l Xo c O₁ O₂ _ _ β₁ β₂ Z₁ Z₂ R _ y f u₂ h₂
  obtain ⟨w₂, F₂, e₂⟩ := frame_pull Z₂.m (x' := y) rfl h₂
  have F₀ := GlobalTheory.ShFam.Pad.Pull.frame_push (c := c) (f := f) Z₂.m0.toSABMap rfl (fun _ _ => rfl) F₂
  obtain ⟨w₁, F₁, e₁⟩ := frame_pull Z₁.m0.toSABMap (x' := y) rfl F₀
  exact ⟨_, GlobalTheory.ShFam.Pad.Pull.frame_push (c := c) (f := f) Z₁.m rfl (fun _ _ => rfl) F₁,
    fun σ i => ⟨w₁ σ i, w₂ σ i, (F₁.1 σ i).1.1, (F₂.1 σ i).1.1, e₁ σ i, rfl, e₂ σ i⟩⟩
