import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenSpread

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} (hF : FormEq φ₁ ε₁ φ₂ ε₂)
    {t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)} {t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      (val t₁ r z J * (val t₂ r z J)⁻¹).val = gs r z ⊤ c := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      exact mul_inv_eq_one.2 (hF U h))
    (LB.mulGen L _ _ _ _ t₁ (LB.invGen L _ _ t₂)) (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ (DVR.invGen_isGen _ _ _ _ h₂))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

def fnOn {R : Type} [CommRing R] : R →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem gs_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Sp S) (a : R) :
    gs (spMap f) z ⊤ (fnOn a) = gs (𝟙 (Sp S)) z ⊤ (fnOn (f a)) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have := gs_pull (𝟙 (Sp S)) (spMap f) z ⊤ trivial (fnOn a)
  rw [Category.id_comp] at this
  rw [← this]
  exact congrArg (gs (𝟙 (Sp S)) z ⊤) e.symm

def gsHom {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) : Γ(Y, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ ⊤) z trivial).hom.comp (r.app ⊤).hom

theorem gsHom_apply {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (a : Γ(Y, ⊤)) : gsHom r z a = gs r z ⊤ a :=
  (gs_eq r z ⊤ trivial a).symm

theorem gs_res_fn {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (W : (Sp R).Opens) (r : Sp S ⟶ W.toScheme)
    (hr : r ≫ W.ι = spMap f) (z : Sp S) (a : R) :
    gsHom r z (W.ι.appTop.hom (fnOn a)) = gsHom (𝟙 (Sp S)) z (fnOn (f a)) := by
  rw [gsHom_apply, gsHom_apply, ← gs_spMap, ← hr]
  exact gs_pull r W.ι z ⊤ trivial _

theorem eq_zero_of_generic {R : Type} [CommRing R] [IsDomain R] (W : (Sp R).Opens)
    (lam : Sp (FractionRing R) ⟶ W.toScheme) (hl : lam ≫ W.ι = jK R) (z : Sp (FractionRing R))
    (d : Γ(W.toScheme, ⊤)) (hd : gsHom lam z d = 0) : d = 0 := by
  haveI : AlgebraicGeometry.IsReduced W.toScheme := isReduced_of_isOpenImmersion W.ι
  refine eq_zero_of_basicOpen_eq_bot d ?_
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w, w ∈ W.toScheme.basicOpen d := by
    by_contra h
    exact hne (le_bot_iff.1 fun w hw => h ⟨w, hw⟩)
  have hsp : W.ι (lam z) ⤳ W.ι w := by
    have e : W.ι (lam z) = jK R z := by rw [← hl]; rfl
    rw [e]
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have hz : (z : PrimeSpectrum (FractionRing R)).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (PrimeSpectrum.isPrime z).ne_top
    have ha' : algebraMap R (FractionRing R) a ∈ (z : PrimeSpectrum (FractionRing R)).asIdeal := ha
    rw [hz, Ideal.mem_bot] at ha'
    obtain rfl : a = 0 := IsFractionRing.injective R (FractionRing R) (ha'.trans (map_zero _).symm)
    exact Ideal.zero_mem _
  have hsp' : lam z ⤳ w := W.ι.isOpenEmbedding.isInducing.specializes_iff.1 hsp
  have hm : z ∈ lam ⁻¹ᵁ W.toScheme.basicOpen d := hsp'.mem_open (W.toScheme.basicOpen d).isOpen hw
  rw [Scheme.preimage_basicOpen] at hm
  have hu := (Scheme.mem_basicOpen _ (U := lam ⁻¹ᵁ ⊤) _ z trivial).1 hm
  exact not_isUnit_zero (hd ▸ hu : IsUnit (0 : (Sp (FractionRing R)).presheaf.stalk z))

theorem val_spread : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (W : (Sp R).Opens) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (W.toScheme ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (W.toScheme ⟶ X)) (ε₂ : K₂ → ℤ), (∀ (U : Type) [CommGroup U] (h : (W.toScheme ⟶ X) → U), ∏ i, h (φ₁ i) ^ ε₁ i = ∏ i, h (φ₂ i) ^ ε₂ i) → ∀ (t₁ : LB.Gen (LB.LinComb L φ₁ ε₁)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)), t₁.IsGen → t₂.IsGen → ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good L z J → val t₁ lam z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val t₂ lam z J) → ∀ z J, Good L z J → val t₁ g z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val t₂ g z J := by
  intro R V _ _ _ _ θ W X L hL K₁ K₂ _ _ φ₁ ε₁ φ₂ ε₂ hF t₁ t₂ h₁ h₂ lam hl g hg x y k k' hy hk hk' H z J hJ
  obtain ⟨c, hc⟩ := exists_ratio hL hF h₁ h₂
  have hu : ∀ {F : Type} [Field F] (u : Fˣ) (w : Sp F),
      (gm (𝟙 (Sp F)) w ⊤ (unitOn u)).val = gsHom (𝟙 (Sp F)) w (fnOn (u : F)) := fun u w =>
    ((gsHom_apply _ _ _).trans (gs_unit _ w ⊤ trivial (unitOn u))).symm
  let z₀ : Sp (FractionRing R) := (⊥ : PrimeSpectrum (FractionRing R))
  choose I hI using fun χ : (TK R).left ⟶ X => exists_chart hL (χ z₀)
  have e₀ : gsHom lam z₀ c = gsHom (𝟙 (Sp (FractionRing R))) z₀ (fnOn (k : FractionRing R)) := by
    have := hc _ lam z₀ I hI
    rw [H z₀ I hI, mul_inv_cancel_right] at this
    exact (gsHom_apply _ _ _).trans (this.symm.trans (hu k z₀))
  have e₁ : c * W.ι.appTop.hom (fnOn y) - W.ι.appTop.hom (fnOn x) = 0 := by
    refine eq_zero_of_generic W lam hl z₀ _ ?_
    rw [map_sub, map_mul, gs_res_fn (algebraMap R (FractionRing R)) W lam hl,
      gs_res_fn (algebraMap R (FractionRing R)) W lam hl, ← hk, map_mul, map_mul]
    exact sub_eq_zero.2 (congrArg (· * _) e₀)
  have hg' : g ≫ W.ι = spMap ((algebraMap V (FractionRing V)).comp θ) :=
    hg.trans (Spec.map_comp (CommRingCat.ofHom θ) (CommRingCat.ofHom (algebraMap V (FractionRing V)))).symm
  have e₂ := congrArg (gsHom (Z := Sp (FractionRing V)) g z) (sub_eq_zero.1 e₁)
  rw [map_mul, gs_res_fn _ W g hg', gs_res_fn _ W g hg', RingHom.comp_apply, RingHom.comp_apply, ← hk', map_mul,
    map_mul] at e₂
  have hy' : IsUnit (algebraMap V (FractionRing V) (θ y)) :=
    isUnit_iff_ne_zero.2 fun h => hy (IsFractionRing.injective V (FractionRing V) (h.trans (map_zero _).symm))
  have e₃ := ((hy'.map fnOn).map (gsHom (𝟙 (Sp (FractionRing V))) z)).mul_right_cancel e₂
  refine mul_inv_eq_iff_eq_mul.1 (Units.ext ?_)
  exact (hc _ g z J hJ).trans ((gsHom_apply _ _ _).symm.trans (e₃.trans (hu k' z).symm))

end GlobalTheory.GenSpread

end
