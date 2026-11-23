import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwTan
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem fm_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext a <;> simp [dualMap]

theorem fm_flagStep_map {Ω : Type} [Field Ω] {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (φ : V →ₗ[Ω] V') {r : ℕ} (b : Fin r → V) (k : ℕ) :
    (flagStep Ω b k).map φ = flagStep Ω (fun a => φ (b a)) k := by
  simp only [flagStep, Submodule.map_span, Set.image_image]

theorem fm_over {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {U : Over S'} (v w : U ⟶ t'.G)
    (h : v.left ≫ m.φ = w.left ≫ m.φ) : v = w :=
  Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w v, Over.w w]))
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
  {g : HostAut H} {Φ : Xo.X ⟶ Xo.X} {n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ} {Y : Model Xo c β}
  {Y' : Model Xo c β'} {T T' : Scheme.{0}} {u₁ : T ⟶ Y.t.G.left} {u₂ u₂' : T ⟶ Y'.t.G.left}

theorem fm_pre (a : T' ⟶ T) (h : TwTan n Y Y' u₁ u₂) : TwTan n Y Y' (a ≫ u₁) (a ≫ u₂) := by
  obtain ⟨u, u', h1, h2, h3, h4⟩ := h
  refine ⟨a ≫ u, a ≫ u', ?_, ?_, ?_, ?_⟩ <;> simp only [Category.assoc, h1, h2, h3, h4]

theorem fm_fun (hβ : Mono (spMap β)) (h : TwTan n Y Y' u₁ u₂) (h' : TwTan n Y Y' u₁ u₂') : u₂ = u₂' := by
  obtain ⟨u, u', h1, h2, h3, h4⟩ := h
  obtain ⟨v, v', k1, k2, k3, k4⟩ := h'
  have hmono : Mono (Y.jQ ≫ pullback.fst Y.s (spMap β)) := by
    have : IsOpenImmersion Y.jQ := Y.jQ_open
    infer_instance
  have e1 : ∀ z : T ⟶ Y.oF.t.G.left,
      z ≫ Y.oF.t.G.hom ≫ (Y.jQ ≫ pullback.fst Y.s (spMap β)) = (z ≫ Y.m.φ) ≫ Y.t.G.hom := by
    intro z
    rw [Category.assoc, Y.m.cart.1.w]
  have huv : u = v := by
    apply Y.m.cart.1.hom_ext
    · exact h1.trans k1.symm
    · rw [← cancel_mono (Y.jQ ≫ pullback.fst Y.s (spMap β)), Category.assoc, Category.assoc, e1, e1, h1, k1]
  subst huv
  have e2 : ∀ z : T ⟶ Y'.oF.t.G.left,
      z ≫ Y'.oF.t.G.hom ≫ pullback.fst _ _ = (z ≫ Y'.m0.φ) ≫ Xo.univ.t.G.hom := by
    intro z
    rw [Category.assoc, Y'.m0.cart.1.w]
  have hu' : u' = v' := by
    apply Y'.m0.cart.1.hom_ext
    · exact h3.trans k3.symm
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, e2, e2, h3, k3]
      · rw [Category.assoc, Category.assoc]
        exact h4.trans k4.symm
  rw [← h2, ← k2, hu']
end

theorem flag_data_match_under_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (θ : Fl.Li₀ ≃+ Fl'.Li₀) (φ : A.Li ≃ₗ[Ω] A'.Li), Mono (spMap β) → Mono (spMap β') → A.fn.comp ψ.toRingHom = A'.fn → (∀ w, TwTan n Y Y' ((A.M.pt w).left ≫ A.m.φ) ((A'.M.pt (φ w)).left ≫ A'.m.φ)) → (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) → (∀ e, φ (Fl.j e) = Fl'.j (θ e)) ∧ ∀ s s' (r : ℕ) (b : Fin r → Fl.Li₀) (u : Matrix (Fin r) (Fin r) Ω), (∀ k, flagStep Ω (Fl.b s) k = flagStep Ω (fun a => ∑ q, u q a • Fl.j (b q)) k) → (∀ k, flagStep Ω (Fl'.b s') k = flagStep Ω (fun a => ∑ q, u q a • Fl'.j (θ (b q))) k) → ∀ k, (flagStep Ω (Fl.b s) k).map φ.toLinearMap = flagStep Ω (Fl'.b s') k := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J y A A' Fl Fl' ψ θ φ hβ hβ' hfn hw he
  have hsp : spMap ((dualMap A.fn).comp (dualMap ψ.toRingHom)) =
      spMap (dualMap A.fn) ≫ spMap (dualMap ψ.toRingHom) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hj : ∀ e, φ (Fl.j e) = Fl'.j (θ e) := by
    intro e
    apply A'.M.inj
    apply fm_over A'.m
    apply fm_fun hβ (hw (Fl.j e))
    rw [Fl.j_pt e, Fl'.j_pt (θ e), ← hfn, fm_dualMap_comp, hsp, Category.assoc]
    exact fm_pre _ (he e)
  refine ⟨hj, ?_⟩
  intro s s' r b u h1 h2 k
  rw [h1 k, h2 k, fm_flagStep_map]
  congr 1
  funext a
  simp [map_sum, map_smul, hj]

end PositivityTheory.UnitarySelfGeneration
