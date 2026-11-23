import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

namespace GlobalTheory.ShFam.GalCarry.LocCarry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem spMap_comp' {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem spMap_dualMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (dualMap (ψ.comp φ)) = spMap (dualMap ψ) ≫ spMap (dualMap φ) := by
  rw [dualMap_comp', spMap_comp']

theorem tri_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {g : EigFrame Z φ' x'} {h : EigFrame Z φ'' x''} {ψ : R →+* R'} {ψ' : R' →+* R''}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ} {t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R''ˣ}
    (h1 : f.Tri ψ g t) (h2 : g.Tri ψ' h t') :
    f.Tri (ψ'.comp ψ) h (fun τ i => Units.map (ψ' : R' →* R'') (t τ i) * t' τ i) := by
  have hx1 := h1.1
  have hφ1 := h1.2.1
  have hx2 := h2.1
  have hφ2 := h2.2.1
  have hx : x'' = spMap (ψ'.comp ψ) ≫ x := by rw [hx2, hx1, spMap_comp', Category.assoc]
  have hφ : φ'' = (ψ'.comp ψ).comp φ := by rw [hφ2, hφ1]; rfl
  obtain ⟨f1, hf1⟩ := f.exists_isMap ψ hφ1 hx1
  obtain ⟨f2, hf2⟩ := f1.exists_isMap ψ' hφ2 hx2
  obtain ⟨g2, hg2⟩ := g.exists_isMap ψ' hφ2 hx2
  refine ⟨hx, hφ, fun τ i => ?_⟩
  have hco : f2.co h τ = f2.co g2 τ * g2.co h τ := (EigFrame.co_mul f2 g2 h τ).symm
  have hA : f2.co g2 τ = (f1.co g τ).map ψ' := EigFrame.IsMap.co τ hf2 hg2 hx2
  have hB := EigFrame.Tri.co τ h1 hf1
  have hC := EigFrame.Tri.co τ h2 hg2
  refine ⟨fun k => f2.co h τ k i, ?_, ?_, ?_⟩
  · dsimp only
    rw [hco, hA, Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [Matrix.map_apply, hB.2, hC.2]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with hb | hb
      · simp [Matrix.map_apply, hB.1 i b hb]
      · simp [hC.1 b i hb]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · intro k hk
    dsimp only
    rw [hco, hA, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b < k
    · simp [Matrix.map_apply, hB.1 k b hb]
    · simp [hC.1 b i (lt_of_lt_of_le hk (not_lt.1 hb))]
  · have e : (fun k => spMap (dualMap (ψ'.comp ψ)) ≫ f.v τ k) = f2.v τ := funext fun k => by
      rw [hf2 τ k, hf1 τ k, spMap_dualMap_comp, Category.assoc]
    rw [e]
    exact f2.co_spec h τ i

theorem tri_of_isMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {k : EigFrame Z φ' x'} {g : EigFrame Z φ'' x''} {a : R →+* R'} {b : R' →+* R''}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R''ˣ} (hk : f.IsMap a k) (hx : x' = spMap a ≫ x) (hφ : φ' = a.comp φ)
    (h : f.Tri (b.comp a) g t) : k.Tri b g t := by
  refine ⟨by rw [h.1, spMap_comp', Category.assoc, hx], by rw [h.2.1, hφ]; rfl, fun τ i => ?_⟩
  obtain ⟨cf, h1, h2, h3⟩ := h.2.2 τ i
  refine ⟨cf, h1, h2, ?_⟩
  have e : (fun j => spMap (dualMap b) ≫ k.v τ j) = fun j => spMap (dualMap (b.comp a)) ≫ f.v τ j :=
    funext fun j => by rw [hk τ j, spMap_dualMap_comp, Category.assoc]
  rw [e]
  exact h3

end GlobalTheory.ShFam.GalCarry.LocCarry

namespace GlobalTheory.ShFam.GalCarry.Tw

open GlobalTheory.ShFam.GalCarry.LocCarry

theorem locRel_of_genRel (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] (e : F ≃+* c.F) (C C' : FlagCpt Z e)
    (φ : C.Y.X ≅ C'.Y.X) (ψ : C'.Y.Fn →+* C.Y.Fn) (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ) :
    T.GenRel C C' φ ψ t₀ → T.LocRel C C' φ ψ t₀ := by
  rintro ⟨hπ, hgen, g₀, hpush, htri⟩
  refine ⟨hπ, hgen, fun y y' χ' f' t' hy hf' => ?_⟩
  subst hy
  let a : C'.Y.X.presheaf.stalk (φ.hom y) →+* C.Y.X.presheaf.stalk y := (φ.hom.stalkMap y).hom
  have ha : stalkPt C.Y y ≫ φ.hom = spMap a ≫ stalkPt C'.Y (φ.hom y) :=
    (Scheme.SpecMap_stalkMap_fromSpecStalk φ.hom).symm
  have hmap := map_alg hgen y
  have hring : ψ.comp (algebraMap (C'.Y.X.presheaf.stalk (φ.hom y)) C'.Y.X.functionField) =
      (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField).comp a := RingHom.ext hmap
  obtain ⟨k', hk'⟩ := f'.exists_isMap a (φ' := a.comp χ')
    (x' := spMap a ≫ stalkPt C'.Y (φ.hom y) ≫ C'.π ≫ genι Z) rfl rfl
  have hx : spMap a ≫ stalkPt C'.Y (φ.hom y) ≫ C'.π ≫ genι Z = (stalkPt C.Y y ≫ C.π ≫ genι Z) ≫ T.ρ.hom := by
    rw [← Category.assoc (spMap a), ← ha, Category.assoc, reassoc_of% hπ, T.g_ι]
    simp only [Category.assoc]
  obtain ⟨f, hf⟩ := T.exists_pull k' rfl hx
  obtain ⟨t, ht⟩ := T.exists_relab (fun τ i => Units.map (ψ : C'.Y.Fn →* C.Y.Fn) (t' τ i) * t₀ τ i)
  refine ⟨a, a.comp χ', f, t, ha, rfl, hmap, ?_, ht, fun τ i => ?_⟩
  · refine (Push.tri_iff hf hpush ht).2 ?_
    have h3 := tri_trans hf' htri
    rw [hring] at h3
    exact tri_of_isMap hk' rfl rfl h3
  · rw [← hk' τ i]
    exact hf.2.2 τ i

end GlobalTheory.ShFam.GalCarry.Tw
