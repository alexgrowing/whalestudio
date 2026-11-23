import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DRFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem initSpan_eq_transport {Y : Scheme.{0}} {t : SAB H Y} {K : Type} [Field K] {p p' : Sp K ⟶ Y} (h : p = p')
    {m n : ℕ} (u : Fin m → TanM p t.G) (v : Fin n → TanM p t.G) (u' : Fin m → TanM p' t.G)
    (v' : Fin n → TanM p' t.G) (hu : ∀ i, (tv (u i)).left = (tv (u' i)).left)
    (hv : ∀ i, (tv (v i)).left = (tv (v' i)).left) {j : ℕ} (e : initSpan K u j = initSpan K v j) :
    initSpan K u' j = initSpan K v' j := by
  subst h
  have h1 : u = u' := funext fun i => GlobalTheory.FlagMod.tan_ext_left (hu i)
  have h2 : v = v' := funext fun i => GlobalTheory.FlagMod.tan_ext_left (hv i)
  subst h1 h2
  exact e

theorem IntStep.pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (X' : Scheme.{0}) (f : X' ⟶ X) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw M.t K), A'.FlagAt w u → A.FlagAt (w ≫ f) u) → IntStep A σ k → IntStep A' σ k := by
  intro E _ _ _ H Dw l Xo c V M X π ty A σ k X' f ty' A' hfl hI x
  obtain ⟨U, hU, m, b, hxU, hb⟩ := hI (f x)
  obtain ⟨_, ⟨U', hU', rfl⟩, hx, hle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((f ⁻¹ᵁ U : X'.Opens) : Set X') from hxU) (f ⁻¹ᵁ U).isOpen
  have hle' : U' ≤ f ⁻¹ᵁ U := fun y hy => hle hy
  have h0 : ⊤ ≤ (tau hU' ≫ f) ⁻¹ᵁ U := le_preimage_map f hle' (tau_le hU' le_rfl)
  have e0 : spMap (ev (tau hU' ≫ f) U h0) ≫ tau hU ≫ π = tau hU' ≫ f ≫ π := by
    rw [← Category.assoc]
    exact (congrArg (· ≫ π) (spMap_ev (tau hU' ≫ f) hU h0)).trans (Category.assoc _ _ _)
  refine ⟨U', hU', m, basPull (ev (tau hU' ≫ f) U h0) e0 b, hx, ?_⟩
  intro K _ w hw u hu j hj
  have hw' : ⊤ ≤ (w ≫ f) ⁻¹ᵁ U := le_preimage_map f hle' hw
  obtain ⟨U₁, hU₁⟩ := Atlas.FlagAt.exists_up (hfl K w _ hu)
  have key := hb K (w ≫ f) hw' U₁ (hU₁ ▸ hfl K w _ hu) j hj
  have e1 : spMap (ev w U' hw) ≫ tau hU' ≫ f = w ≫ f := by
    rw [← Category.assoc]
    exact congrArg (· ≫ f) (spMap_ev w hU' hw)
  have e2 : ev (w ≫ f) U hw' = (ev w U' hw).comp (ev (tau hU' ≫ f) U h0) :=
    (GlobalTheory.FlagMod.ev_congr e1.symm U hw' (le_preimage_comp _ h0)).trans (ev_spMap _ _ U h0 _)
  refine initSpan_eq_transport (Category.assoc w f π) _ _ _ _ (fun i => ?_) (fun i => ?_) key
  · exact congrFun (congrFun hU₁ σ) i
  · rw [basAt_left b, basAt_left (basPull (ev (tau hU' ≫ f) U h0) e0 b) w hw, basPull_apply, GlobalTheory.FlagMod.tanPull_left, e2, GlobalTheory.FlagMod.dualMap_comp,
      ← spMap_comp', Category.assoc]
    exact Category.assoc _ _ _

end GlobalTheory.DRFlag
