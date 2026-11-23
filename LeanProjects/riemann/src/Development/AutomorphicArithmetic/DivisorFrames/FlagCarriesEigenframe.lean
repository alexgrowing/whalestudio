import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueRuleOfRegular
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

namespace UpperTheory.TriangularFrameMaps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
  {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X} {φ'' : c.F →+* R''} {x'' : Sp R'' ⟶ Z.X}

private def UT (f g : EigFrame Z φ x) : Prop := ∀ τ, (f.co g τ).BlockTriangular id

private theorem UT.trans {f g k : EigFrame Z φ x} (h : UT f g) (h' : UT g k) : UT f k := fun τ => by
  rw [← f.co_mul g k τ]
  exact (h τ).mul (h' τ)

private theorem UT.symm {f g : EigFrame Z φ x} (h : UT f g) : UT g f := fun τ => by
  have e : f.co g τ * g.co f τ = 1 := (f.co_mul g f τ).trans (f.co_self τ)
  obtain ⟨I⟩ := ((Matrix.isUnit_iff_isUnit_det _).2 (f.isUnit_det_co g τ)).nonempty_invertible
  rw [← Matrix.inv_eq_right_inv e]
  exact Matrix.blockTriangular_inv_of_blockTriangular (h τ)

private theorem ut_of_tri {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'}
    (h : ∃ t, f.Tri ψ g t) (hf : f.IsMap ψ f') : UT f' g := fun τ a i hi =>
  (h.choose_spec.co τ hf).1 a i hi

private theorem tri_of_ut {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'}
    (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (hf : f.IsMap ψ f') (h : UT f' g) : ∃ t, f.Tri ψ g t := by
  have hu : ∀ τ i, IsUnit (f'.co g τ i i) := fun τ i => by
    have := f'.isUnit_det_co g τ
    rw [Matrix.det_of_upperTriangular (h τ)] at this
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => f'.co g τ i i) (Finset.mem_univ i)) this
  refine ⟨fun τ i => (hu τ i).unit, hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, rfl, fun k hk => h τ hk, ?_⟩⟩
  rw [← funext (hf τ)]
  exact f'.co_spec g τ i

private theorem isMap_comp {f : EigFrame Z φ x} {ψ : R →+* R'} {χ : R' →+* R''} {f' : EigFrame Z φ' x'}
    {f'' : EigFrame Z φ'' x''} (h : f.IsMap ψ f') (h' : f'.IsMap χ f'') : f.IsMap (χ.comp ψ) f'' := fun τ i => by
  rw [h' τ i, h τ i, ← Category.assoc, Descent.dual_comp]

private theorem isMap_id (f : EigFrame Z φ x) : f.IsMap (RingHom.id R) f := fun τ i => by
  have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  rw [h1, Category.id_comp]

private theorem sp_comp' (f : R →+* R') (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

private theorem tri_comp {f : EigFrame Z φ x} {ψ : R →+* R'} {χ : R' →+* R''} {g : EigFrame Z φ' x'}
    {k : EigFrame Z φ'' x''} (h : ∃ t, f.Tri ψ g t) (h' : ∃ t, g.Tri χ k t) : ∃ t, f.Tri (χ.comp ψ) k t := by
  obtain ⟨hx, hφ, -⟩ := h.choose_spec
  obtain ⟨hx', hφ', -⟩ := h'.choose_spec
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hφ hx
  obtain ⟨f'', hf''⟩ := f'.exists_isMap χ hφ' hx'
  obtain ⟨g', hg'⟩ := g.exists_isMap χ hφ' hx'
  refine tri_of_ut (by rw [hx', hx, ← Category.assoc, sp_comp']) (by rw [hφ', hφ, RingHom.comp_assoc])
    (isMap_comp hf' hf'') (UT.trans (g := g') (fun τ => ?_) (ut_of_tri h' hg'))
  rw [hf''.co τ hg' hx']
  exact (ut_of_tri h hf' τ).map χ

private theorem tri_cancel {f : EigFrame Z φ x} {ψ : R →+* R'} {χ : R' →+* R''} {g : EigFrame Z φ' x'}
    {k : EigFrame Z φ'' x''} (hχ : Function.Injective χ) (hx : x' = spMap ψ ≫ x)
    (h : ∃ t, f.Tri (χ.comp ψ) k t) (h' : ∃ t, g.Tri χ k t) : ∃ t, f.Tri ψ g t := by
  obtain ⟨hx', hφ', -⟩ := h'.choose_spec
  have hφ : φ' = ψ.comp φ := RingHom.ext fun a => hχ
    ((DFunLike.congr_fun hφ' a).symm.trans (DFunLike.congr_fun h.choose_spec.2.1 a))
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hφ hx
  obtain ⟨f'', hf''⟩ := f'.exists_isMap χ hφ' hx'
  obtain ⟨g', hg'⟩ := g.exists_isMap χ hφ' hx'
  refine tri_of_ut hx hφ hf' fun τ a i hi => hχ ?_
  have := ((ut_of_tri h (isMap_comp hf' hf'')).trans (ut_of_tri h' hg').symm) τ hi
  rw [hf''.co τ hg' hx'] at this
  exact this.trans (map_zero χ).symm

private theorem tri_two {f : EigFrame Z φ x} {ψ : R →+* R'} {g : EigFrame Z φ' x'} {φ₂ : c.F →+* R'}
    {x₂ : Sp R' ⟶ Z.X} {g₂ : EigFrame Z φ₂ x₂} (h : ∃ t, f.Tri ψ g t) (h' : ∃ t, f.Tri ψ g₂ t) :
    ∃ t, g.Tri (RingHom.id R') g₂ t := by
  obtain ⟨hx, hφ, -⟩ := h.choose_spec
  obtain ⟨hx', hφ', -⟩ := h'.choose_spec
  obtain rfl : x₂ = x' := hx'.trans hx.symm
  obtain rfl : φ₂ = φ' := hφ'.trans hφ.symm
  obtain ⟨f', hf'⟩ := f.exists_isMap ψ hφ hx
  exact tri_of_ut g.tri_refl.1 rfl (isMap_id g) ((ut_of_tri h hf').symm.trans (ut_of_tri h' hf'))

open GlobalTheory.ShFam.Descent in
private theorem tri_of_carries {F : Type} [Field F] {e : F ≃+* c.F} {C : FlagCpt Z e} {k : Type} [Field k]
    {q : Sp k ⟶ C.Y.X} {y₀ : C.Y.X} (hy : q (closedPoint k) = y₀) {χ : St C y₀ →+* k} (hχ : spMap χ ≫ pt C y₀ = q)
    {φ₀ : c.F →+* St C y₀} {f₀ : EigFrame Z φ₀ (pt C y₀ ≫ C.π ≫ genι Z)}
    (h₀ : ∃ t, f₀.Tri (toFk C y₀).toRingHom (rationalEigenFrame C) t) {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x}
    (h : C.Carries q g) : ∃ t, f₀.Tri χ g t := by
  obtain ⟨y, ψ, φ₁, f, t, t', e0, h1, h2⟩ := carries_iff.1 h
  obtain ⟨sp, s1, s2⟩ := exists_spec (show y₀ ⤳ y by rw [← hy]; exact specializes_of e0.symm (closedPoint k))
  have e1 : χ.comp sp.toRingHom = ψ := hom_eq (by rw [← sp_comp', Category.assoc, s1, hχ, e0])
  have e2 : (toFk C y₀).toRingHom.comp sp.toRingHom = (toFk C y).toRingHom := RingHom.ext s2
  have k1 : ∃ t, f.Tri sp.toRingHom f₀ t :=
    tri_cancel (toFk_injective C y₀) (by rw [← Category.assoc (spMap _), s1]) ⟨t, by rw [e2]; exact h1⟩ h₀
  obtain ⟨g₀, hg₀⟩ := f₀.exists_isMap χ rfl rfl
  have k2 : ∃ t, f₀.Tri χ g₀ t := ⟨_, hg₀.tri rfl rfl⟩
  have k3 : ∃ t, f.Tri (χ.comp sp.toRingHom) g t := ⟨t', by rw [e1]; exact h2⟩
  have k4 := tri_comp k2 (tri_two (tri_comp k1 k2) k3)
  rwa [RingHom.id_comp] at k4

end UpperTheory.TriangularFrameMaps

open UpperTheory.TriangularFrameMaps GlobalTheory.ShFam.Descent in
theorem UpperTheory.flag_carries_eigenframe :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt T e) (k : Type) [Field k] (q : Sp k ⟶ C.Y.X), (∃ (φ : c.F →+* k) (g : EigFrame T φ (q ≫ C.π ≫ genι T)), C.Carries q g) ∧ ∀ (φ : c.F →+* k) (x : Sp k ⟶ T.X) (g : EigFrame T φ x), C.Carries q g → x = q ≫ C.π ≫ genι T ∧ q ≫ C.π ≫ genStr T = spMap φ ∧ ∀ (φ' : c.F →+* k) (x' : Sp k ⟶ T.X) (g' : EigFrame T φ' x'), C.Carries q g' ↔ ∃ t, g.Tri (RingHom.id k) g' t := by
  intro E _ _ _ H Dw l Xo c O _ β T F _ e C k _ q
  obtain ⟨y₀, χ, hχ, hy⟩ : ∃ (y : C.Y.X) (χ : St C y →+* k), spMap χ ≫ pt C y = q ∧ q (closedPoint k) = y :=
    ⟨_, (Scheme.stalkClosedPointTo q).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk q, rfl⟩
  obtain ⟨φ₀, f₀, t₀, h₀⟩ : ∃ (φ₀ : c.F →+* St C y₀) (f₀ : EigFrame T φ₀ (pt C y₀ ≫ C.π ≫ genι T)),
      ∃ t, f₀.Tri (toFk C y₀).toRingHom (rationalEigenFrame C) t := by
    obtain ⟨φ₀, f₀, t₀, h₀, -⟩ := C.gr_spec y₀
    exact ⟨φ₀, f₀, t₀, h₀⟩
  obtain rfl : φ₀ = algebraMap c.F (St C y₀) := RingHom.ext fun a => toFk_injective C y₀
    ((DFunLike.congr_fun h₀.2.1 a).symm.trans ((toFk C y₀).commutes a).symm)
  have hq : q ≫ C.π ≫ genι T = spMap χ ≫ pt C y₀ ≫ C.π ≫ genι T := by rw [← hχ, Category.assoc]
  refine ⟨?_, fun φ x g hg => ?_⟩
  · obtain ⟨g, hg⟩ := f₀.exists_isMap χ rfl hq
    exact ⟨_, g, carries_iff.2 ⟨y₀, χ, _, f₀, t₀, 1, hχ.symm, h₀, hg.tri rfl hq⟩⟩
  · have k1 := tri_of_carries hy hχ ⟨t₀, h₀⟩ hg
    refine ⟨k1.choose_spec.1.trans hq.symm, ?_, fun φ' x' g' => ⟨fun hg' => tri_two k1 (tri_of_carries hy hχ ⟨t₀, h₀⟩ hg'),
      fun h => ?_⟩⟩
    · rw [k1.choose_spec.2.1, ← sp_comp', ← pt_str, ← hχ, Category.assoc]
    · obtain ⟨t, ht⟩ := tri_comp k1 h
      exact carries_iff.2 ⟨y₀, χ, _, f₀, t₀, t, hχ.symm, h₀, ht⟩
