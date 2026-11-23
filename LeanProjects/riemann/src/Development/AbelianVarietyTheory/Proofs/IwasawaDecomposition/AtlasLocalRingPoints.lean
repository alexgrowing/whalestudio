import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.Spez

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Flags

variable {X : Scheme.{0}} {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {ty : (E →+* ℂ) → Finset ℕ}

theorem sameFlag_bc (φ : R →+* S) {x : Sp R ⟶ X} {u u' : Vecs Dw t R} (h : SameFlag ty t x u u') :
    SameFlag ty t (spMap φ ≫ x) (u.bc φ) (u'.bc φ) := fun σ j hj i hi => by
  obtain ⟨cf, h1, h2⟩ := h σ j hj i hi
  exact ⟨fun l => φ (cf l), fun l hl => by simp [h1 l hl], comb_bc φ h2⟩

theorem sameFlag_of_bc {l : Level H} {c : Coeff l} {g : c.F →+* R} {φ : R →+* S} (hφ : Function.Injective φ)
    {x : Sp R ⟶ X} {u u' : Vecs Dw t R} (hu : LocM.IsFrame t g x u) (hu' : LocM.IsFrame t g x u')
    (h : SameFlag ty t (spMap φ ≫ x) (u.bc φ) (u'.bc φ)) : SameFlag ty t x u u' := fun σ j hj i hi => by
  obtain ⟨cf, hcf, -⟩ := hu.exists_comb hu' σ i
  obtain ⟨cf', h1, h2⟩ := h σ j hj i hi
  have e := ((GlobalTheory.LocM.isFrame_bc E H Dw l c _ t _ _ _ φ _ _ hu).exists_comb
    (GlobalTheory.LocM.isFrame_bc E H Dw l c _ t _ _ _ φ _ _ hu') σ i).unique (comb_bc φ hcf) h2
  exact ⟨cf, fun m hm => hφ ((congrFun e m).trans ((h1 m hm).trans (map_zero φ).symm)), hcf⟩

end Flags

section Atl

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {K : Type} [Field K]

theorem sameFlag_of_flagAt {w : Sp K ⟶ X} {u u' : Vecs Dw M.t K} (h : A.FlagAt w u) (h' : A.FlagAt w u') :
    SameFlag ty M.t (w ≫ π) u u' := by
  obtain ⟨U, rfl⟩ := h.exists_up
  obtain ⟨U', rfl⟩ := h'.exists_up
  exact (sameFlag_up_iff U U').2 fun σ j hj => (h'.initSpan_eq h σ hj).le

theorem isFrame_of_flagAt {w : Sp K ⟶ X} {u : Vecs Dw M.t K} (h : A.FlagAt w u) {a : A.ch.ι} {φ : A.ch.R a →+* K}
    (e : spMap φ ≫ A.ch.χ a = w) : LocM.IsFrame M.t (φ.comp (A.alg a)) (w ≫ π) u := by
  obtain ⟨a', φ', e', hf, -⟩ := h
  rwa [A.alg_eq e e']

end Atl

theorem ext_of_field {Y : Scheme.{0}} [Y.IsSeparated] {R K : Type} [CommRing R] [Field K] {φ : R →+* K}
    (hφ : Function.Injective φ) {x x' : Sp R ⟶ Y} (h : spMap φ ≫ x = spMap φ ≫ x') : x = x' := by
  have : IsDomain R := hφ.isDomain φ
  have : IsDominant (spMap φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
    (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)⟩
  exact ext_of_isDominant (spMap φ) h

theorem flagAt_specialise {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'}
    {V : ValuationSubring c.F} {V' : ValuationSubring c'.F} {M : Model Xo c V.subtype} {M' : Model Xo' c' V'.subtype}
    {X X' : Scheme.{0}} {π : X ⟶ M.X} {π' : X' ⟶ M'.X} {ty ty' : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty}
    {A' : Atlas M' π' ty'} {τ : M'.X ⟶ M.X} (mu : SABMap M'.t M.t τ) (hc : c.F ≤ c'.F) (hty : ∀ σ, ty σ ⊆ ty' σ)
    {R K k : Type} [CommRing R] [Field K] [Field k] {φ : R →+* K} (hφ : Function.Injective φ) (ψ : R →+* k)
    {z₁ : Sp R ⟶ X'} {z₂ : Sp R ⟶ X} (hR : z₂ ≫ π = (z₁ ≫ π') ≫ τ) {a₁ : A'.ch.ι} {ρ₁ : A'.ch.R a₁ →+* R}
    (e₁ : spMap ρ₁ ≫ A'.ch.χ a₁ = z₁) {a₂ : A.ch.ι} {ρ₂ : A.ch.R a₂ →+* R} (e₂ : spMap ρ₂ ≫ A.ch.χ a₂ = z₂)
    (hg : ρ₂.comp (A.alg a₂) = (ρ₁.comp (A'.alg a₁)).comp (IntermediateField.inclusion hc).toRingHom)
    {u : Vecs Dw M'.t K} (h₁ : A'.FlagAt (spMap φ ≫ z₁) u)
    (h₂ : A.FlagAt (spMap φ ≫ z₂) fun σ j => u σ j ≫ mu.φ) :
    A'.FlagAt (spMap ψ ≫ z₁) ((A'.fr a₁).bc (ψ.comp ρ₁)) ∧
      A.FlagAt (spMap ψ ≫ z₂) fun σ j => (A'.fr a₁).bc (ψ.comp ρ₁) σ j ≫ mu.φ := by
  have f₁ := (A'.isFrame_bc e₁).push hc mu
  rw [← hg, ← hR] at f₁
  have f₂ := A.isFrame_bc e₂
  have bc : ∀ {S : Type} [CommRing S] (χ : R →+* S),
      Vecs.bc (Dw := Dw) (t := M.t) χ (fun σ j => (A'.fr a₁).bc ρ₁ σ j ≫ mu.φ) =
        fun σ j => (A'.fr a₁).bc (χ.comp ρ₁) σ j ≫ mu.φ := fun χ => by
    rw [← Vecs.bc_bc]
    funext σ j
    exact (Category.assoc _ _ _).symm
  have c₁ : ∀ {S : Type} [CommRing S] (χ : R →+* S), spMap (χ.comp ρ₁) ≫ A'.ch.χ a₁ = spMap χ ≫ z₁ :=
    fun χ => by rw [← spMap_comp', Category.assoc, e₁]
  have c₂ : ∀ {S : Type} [CommRing S] (χ : R →+* S), spMap (χ.comp ρ₂) ≫ A.ch.χ a₂ = spMap χ ≫ z₂ :=
    fun χ => by rw [← spMap_comp', Category.assoc, e₂]
  have key : SameFlag ty M.t (z₂ ≫ π) ((A.fr a₂).bc ρ₂) fun σ j => (A'.fr a₁).bc ρ₁ σ j ≫ mu.φ := by
    refine sameFlag_of_bc hφ f₂ f₁ ?_
    rw [Vecs.bc_bc, bc, ← Category.assoc]
    have g₁ := A'.isFrame_bc (c₁ φ)
    have g₂ := A.isFrame_bc (c₂ φ)
    have s₁ := ((sameFlag_of_flagAt h₁ (A'.flagAt_fr (c₁ φ))).push mu
      (fun σ j => ((isFrame_of_flagAt h₁ (c₁ φ)).1 σ j).1) fun σ j => (g₁.1 σ j).1).mono hty
    have hK : ((spMap φ ≫ z₁) ≫ π') ≫ τ = (spMap φ ≫ z₂) ≫ π := by simp only [Category.assoc, hR]
    rw [hK] at s₁
    exact SameFlag.trans (fun σ j => (g₂.1 σ j).1)
      (fun σ j => (g₂.exists_comb (isFrame_of_flagAt h₂ (c₂ φ)) σ j).exists)
      (sameFlag_of_flagAt (A.flagAt_fr (c₂ φ)) h₂) s₁
  have r₁ := GlobalTheory.LocM.isFrame_bc E H Dw l c _ M.t _ _ _ ψ _ _ f₁
  have r₂ := sameFlag_bc ψ key
  rw [bc, ← Category.assoc] at r₁ r₂
  rw [Vecs.bc_bc] at r₂
  exact ⟨A'.flagAt_fr (c₁ ψ), a₂, ψ.comp ρ₂, c₂ ψ, r₁, r₂⟩

theorem natTo_specialise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀) (R K k : Type) [CommRing R] [IsLocalRing R] [Field K] [Field k] (φ : R →+* K) (ψ : R →+* k) (z : Sp R ⟶ Z.X) (z' : Sp R ⟶ X), i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → Function.Injective φ → z (IsLocalRing.closedPoint R) ∈ Z.opn → NatTo Z A (spMap φ ≫ z) (spMap φ ≫ z') → NatTo Z A (spMap ψ ≫ z) (spMap ψ ≫ z') := by
  intro E _ _ _ H Dw Xo p W Y i₀ i X π ty A Z R K k _ _ _ _ φ ψ z z' hc hty hφ hz ⟨τ, mu, u, htr, hK, h₁, h₂⟩
  obtain ⟨b, π', r, hb, hπ₁, hπ₂, -, hj, -⟩ := id htr
  have := projProper _ _ _ (Y i).proj
  have : (Y i).X.IsSeparated := ⟨by rw [← terminal.comp_from (Y i).s]; infer_instance⟩
  have hR : z' ≫ π = (z ≫ Z.π) ≫ τ := ext_of_field hφ (by simpa only [Category.assoc] using hK)
  obtain ⟨a₁, ρ₁, e₁⟩ := (atlasOf Z).ch.exists_fac z (by rw [(atlasOf Z).cover]; exact hz)
  obtain ⟨a₂, ρ₂, e₂⟩ := A.ch.exists_fac z' (by
    obtain ⟨q, hq⟩ := hz
    rw [A.cover]
    exact ⟨r q, ((Scheme.Hom.comp_apply r _ q).symm.trans (congrArg (fun f => f q) hj.symm)).trans
      ((congrArg τ hq).trans (congrArg (fun f => f (IsLocalRing.closedPoint R)) hR.symm))⟩)
  have hs : τ ≫ (Y i).s = (Y Z.i).s ≫ spMap b := by
    rw [← hπ₁, ← hπ₂, Category.assoc, Category.assoc, pullback.condition]
  have hg : ρ₂.comp (A.alg a₂) = (ρ₁.comp ((atlasOf Z).alg a₁)).comp (IntermediateField.inclusion hc).toRingHom := by
    apply coeff_ext (W := W)
    have e : z' ≫ π ≫ (Y i).s = (z ≫ Z.π ≫ (Y Z.i).s) ≫ spMap b := by
      rw [← Category.assoc, hR, Category.assoc, hs]; simp only [Category.assoc]
    rw [← A.affineOpenChart_comp_structure_eq_spMap e₂, e, (atlasOf Z).affineOpenChart_comp_structure_eq_spMap e₁, spMap_comp']
    exact congrArg spMap (RingHom.ext fun x => congrArg (ρ₁.comp ((atlasOf Z).alg a₁)) (Subtype.ext (hb x)))
  obtain ⟨k₁, k₂⟩ := flagAt_specialise (A' := atlasOf Z) mu hc hty hφ ψ hR e₁ e₂ hg h₁ h₂
  exact ⟨τ, mu, _, htr, by simp only [Category.assoc, hR], k₁, k₂⟩

end GlobalTheory.DRFlag.Spez
