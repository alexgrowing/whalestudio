import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

namespace GlobalTheory.ShFam.GalCarry.Partner

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem co_tri {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {φ' : c.F →+* R'}
    {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ} (h : f.Tri ψ g t) (hf : f.IsMap ψ f') (τ : E →+* ℂ) :
    (f'.co g τ).BlockTriangular id :=
  fun a i hia => (h.co τ hf).1 a i hia

theorem tri_of_co {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {φ' : c.F →+* R'}
    {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' b : EigFrame Z φ' x'} (hf : f.IsMap ψ f')
    (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) (hb : ∀ τ, (f'.co b τ).BlockTriangular id) :
    ∃ t, f.Tri ψ b t := by
  have hu : ∀ τ i, IsUnit (f'.co b τ i i) := fun τ i =>
    GlobalTheory.ShFam.CarriesAt.isUnit_diag_of_blockTriangular (hb τ) (f'.isUnit_det_co b τ) i
  refine ⟨fun τ i => (hu τ i).unit, hx, hφ, fun τ i => ⟨fun a => f'.co b τ a i, (hu τ i).unit_spec.symm,
    fun k hk => hb τ hk, ?_⟩⟩
  rw [← funext (hf τ)]
  exact f'.co_spec b τ i

theorem co_symm_tri {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f g : EigFrame Z φ x) (τ : E →+* ℂ)
    (h : (f.co g τ).BlockTriangular id) : (g.co f τ).BlockTriangular id := by
  have e : g.co f τ = (f.co g τ)⁻¹ := (Matrix.inv_eq_left_inv ((g.co_mul f g τ).trans (g.co_self τ))).symm
  have := Matrix.invertibleOfIsUnitDet _ (f.isUnit_det_co g τ)
  rw [e]
  exact Matrix.blockTriangular_inv_of_blockTriangular h

theorem carries_of_tri {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {K : Type} [Field K] {χ : c.F →+* K}
    {x : Sp K ⟶ Z.X} {p : Sp K ⟶ C.Y.X} {a b : EigFrame Z χ x} (hb : ∀ τ, (a.co b τ).BlockTriangular id)
    (ha : C.Carries p a) : C.Carries p b := by
  obtain ⟨y, ψ, φ₁, f, t, t', hp, hT, ha'⟩ := ha
  obtain ⟨fk, hfk⟩ := f.exists_isMap ψ ha'.2.1 ha'.1
  obtain ⟨s, hs⟩ := tri_of_co hfk ha'.2.1 ha'.1 fun τ => by
    rw [← fk.co_mul a b τ]
    exact (co_tri ha' hfk τ).mul (hb τ)
  exact ⟨y, ψ, φ₁, f, t, s, hp, hT, hs⟩

end GlobalTheory.ShFam.GalCarry.Partner

open GlobalTheory.ShFam.GalCarry.Partner in

theorem GlobalTheory.ShFam.GalCarry.exists_unique_ptRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type)
    [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F]
    (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (K : Type) [Field K]
    [IsAlgClosed K] (i : U.Comp) (p : Sp K ⟶ (Φ.C i).Y.X),
    ∃! q : Σ i' : U.Comp, (Sp K ⟶ (Φ.C i').Y.X), T.PtRel (Φ.C i) (Φ.C q.1) p q.2 := by
  intro E _ _ _ H Dw l Xo c O _ β Z T F _ e σ N U Φ K _ _ i p
  obtain ⟨y, ψ, hp⟩ : ∃ (y : (Φ.C i).Y.X) (ψ : (Φ.C i).Y.X.presheaf.stalk y →+* K),
      p = spMap ψ ≫ stalkPt (Φ.C i).Y y :=
    ⟨_, (Scheme.stalkClosedPointTo p).hom, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm⟩
  obtain ⟨φ₁, f, t, hT, -⟩ := (Φ.C i).gr_spec y
  have hs1 : stalkPt (Φ.C i).Y y ≫ (Φ.C i).π ≫ genStr Z = spMap φ₁ :=
    GlobalTheory.Mean4O.CompModel.stalkPt_genStr (Φ.C i) y φ₁ hT.2.1
  obtain ⟨χ, hχ⟩ : ∃ χ : c.F →+* K, χ = ψ.comp φ₁ := ⟨_, rfl⟩
  have hstr : p ≫ (Φ.C i).π ≫ genStr Z = spMap χ := by
    rw [hχ, hp, ← GlobalTheory.Mean4O.CompModel.sp_comp, ← hs1]
    simp only [Category.assoc]
  have hx : p ≫ (Φ.C i).π ≫ genι Z = spMap ψ ≫ stalkPt (Φ.C i).Y y ≫ (Φ.C i).π ≫ genι Z := by
    rw [hp]; simp only [Category.assoc]
  obtain ⟨g, hg⟩ := f.exists_isMap ψ hχ hx
  have hcg : (Φ.C i).Carries p g := ⟨y, ψ, φ₁, f, t, 1, hp, hT, hg.tri hχ hx⟩
  obtain ⟨X, hX⟩ : ∃ X : Sp K ⟶ gen Z, X = (p ≫ (Φ.C i).π) ≫ T.g.hom := ⟨_, rfl⟩
  have hXs : X ≫ genStr Z = spMap χ := by
    rw [hX, Category.assoc, T.g_str, Category.assoc, hstr]
  have hXι : X ≫ genι Z = (p ≫ (Φ.C i).π ≫ genι Z) ≫ T.ρ.hom := by
    rw [hX, Category.assoc, T.g_ι]; simp only [Category.assoc]
  obtain ⟨g', hg'⟩ := T.exists_push g rfl hXι
  obtain ⟨q, ⟨hqπ, hqc⟩, hu⟩ := Φ.lifts K χ X hXs g'
  have mk : ∀ (i' : U.Comp) (p' : Sp K ⟶ (Φ.C i').Y.X) (x₁ : Sp K ⟶ Z.X) (a : EigFrame Z χ x₁),
      x₁ = p' ≫ (Φ.C i').π ≫ genι Z → p' ≫ (Φ.C i').π = X → T.Push g a → (Φ.C i').Carries p' a →
      T.PtRel (Φ.C i) (Φ.C i') p p' := by
    intro i' p' x₁ a hx₁ hπ hP hc
    subst hx₁
    unfold Tw.PtRel
    exact ⟨by rw [hπ, hX, Category.assoc], χ, g, a, hstr, hP, hcg, hc⟩
  refine ⟨q, mk q.1 q.2 _ g' (by rw [← hqπ, Category.assoc]) hqπ hg' hqc, ?_⟩
  rintro ⟨i₁, p₁⟩ hrel
  unfold Tw.PtRel at hrel
  obtain ⟨hπ₁, χ₁, f₁, f₁', hs₁, hP₁, hc₁, hc₁'⟩ := hrel
  have hχ₁ : χ₁ = χ := congrArg CommRingCat.Hom.hom (Spec.map_injective (hs₁.symm.trans hstr))
  subst hχ₁
  obtain ⟨s₁, hs₁'⟩ := GlobalTheory.ShFam.CarriesAt.tri_of_carries _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc₁ y ψ φ₁ f t hp hT
  have hinv : ∀ τ, (f₁.co g τ).BlockTriangular id := fun τ => co_symm_tri g f₁ τ (co_tri hs₁' hg τ)
  have key : ∀ (x₁ : Sp K ⟶ Z.X) (a : EigFrame Z χ₁ x₁), x₁ = X ≫ genι Z → T.Push f₁ a →
      (Φ.C i₁).Carries p₁ a → (Φ.C i₁).Carries p₁ g' := by
    intro x₁ a hx₁ hPa hca
    subst hx₁
    refine carries_of_tri (Φ.C i₁) (fun τ => ?_) hca
    rw [hPa.co hg' τ]
    exact fun a b h => hinv (T.emb τ) (show T.ix b < T.ix a from h)
  refine hu ⟨i₁, p₁⟩ ⟨by rw [hπ₁, hX, Category.assoc], key _ f₁' ?_ hP₁ hc₁'⟩
  rw [hX, ← Category.assoc, hπ₁]
  simp only [Category.assoc]
