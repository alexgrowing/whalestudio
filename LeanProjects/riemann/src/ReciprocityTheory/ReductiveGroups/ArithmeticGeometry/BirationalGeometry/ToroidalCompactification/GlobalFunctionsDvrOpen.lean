import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvr
import Lemmata.GeneralBFactFurther.Imports

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen

variable {V : Type} [CommRing V] [IsDomain V]

theorem isLocalization_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ (FractionRing V) := by
  first | exact Bl.general_b_fact_further.goal1 .. | (apply Bl.general_b_fact_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_further.goal1 <;> assumption)

theorem isOpenImmersion_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsOpenImmersion (spMap (algebraMap V (FractionRing V))) := by
  have := isLocalization_frac hϖ
  let e := IsLocalization.algEquiv (Submonoid.powers ϖ) (Localization.Away ϖ) (FractionRing V)
  have he : algebraMap V (FractionRing V) =
      (e : Localization.Away ϖ →+* FractionRing V).comp (algebraMap V (Localization.Away ϖ)) :=
    RingHom.ext fun x => (e.commutes x).symm
  have : IsIso (CommRingCat.ofHom (e : Localization.Away ϖ →+* FractionRing V)) :=
    ⟨⟨CommRingCat.ofHom (e.symm : FractionRing V →+* Localization.Away ϖ), by ext x; simp, by ext x; simp⟩⟩
  show IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  rw [he, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

theorem opensRange_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    haveI := isOpenImmersion_frac hϖ
    (spMap (algebraMap V (FractionRing V))).opensRange =
      (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) := by
  have := isLocalization_frac hϖ
  rw [basicOpen_eq_of_affine]
  ext1
  exact PrimeSpectrum.localization_away_comap_range (FractionRing V) ϖ

theorem eq_zero_of_mul {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p] {r : V} (hr : r ≠ 0) (f : Γ(X, ⊤))
    (h : p.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv r) * f = 0) : f = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ f 0 fun x hx => ?_
  show X.presheaf.germ ⊤ x hx f = X.presheaf.germ ⊤ x hx 0
  set r' := (Scheme.ΓSpecIso (CommRingCat.of V)).inv r with hr'def
  have hr' : r' ≠ 0 := by
    intro h0
    apply hr
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom h0
    rwa [hr'def, Iso.inv_hom_id_apply, map_zero] at this
  set g := (Sp V).presheaf.germ ⊤ (p.base x) trivial r' with hgdef
  have hg : g ≠ 0 := fun h0 =>
    hr' (germ_injective_of_isIntegral (Sp V) (U := ⊤) (p.base x) trivial (h0.trans (map_zero _).symm))
  let := (p.stalkMap x).hom.toAlgebra
  have : Module.Flat _ (X.presheaf.stalk x) := Flat.stalkMap p x
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
    (mem_nonZeroDivisors_of_ne_zero hg)
  have key : (p.stalkMap x).hom g * X.presheaf.germ ⊤ x hx f = 0 := by
    have h1 : (p.stalkMap x).hom g = X.presheaf.germ ⊤ x hx (p.appTop r') :=
      Scheme.Hom.germ_stalkMap_apply p ⊤ x trivial r'
    rw [h1]
    show X.presheaf.germ ⊤ x hx (p.appTop r') * X.presheaf.germ ⊤ x hx f = 0
    rw [← map_mul, h, map_zero]
  have h2 : g • X.presheaf.germ ⊤ x hx f = g • 0 := by
    rw [smul_zero, Algebra.smul_def]
    exact key
  rw [hreg h2, map_zero]

theorem restrict_basicOpen_injective {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    (s : Γ(X, ⊤)) (hs : ∀ f : Γ(X, ⊤), s * f = 0 → f = 0) :
    Function.Injective (X.presheaf.map (homOfLE (le_top : X.basicOpen s ≤ ⊤)).op) := by
  have := isLocalization_basicOpen_of_qcqs (X := X) (U := ⊤) (by simpa using isCompact_univ)
    (by simpa using isQuasiSeparated_univ) s
  have hM : Submonoid.powers s ≤ nonZeroDivisors Γ(X, ⊤) :=
    Submonoid.powers_le.2 (mem_nonZeroDivisors_iff_right.2 fun f hf => hs f (by rwa [mul_comm] at hf))
  exact IsLocalization.injective (Γ(X, X.basicOpen s)) hM

theorem appTop_fst_injective [IsDiscreteValuationRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) [Flat p]
    [QuasiCompact p] [QuasiSeparated p] :
    haveI := isOpenImmersion_frac (IsDiscreteValuationRing.exists_irreducible V).choose_spec
    Function.Injective (pullback.fst p (spMap (algebraMap V (FractionRing V)))).appTop := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  haveI := isOpenImmersion_frac hϖ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  set s := p.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ϖ) with hs
  have hrange : (pullback.fst p (spMap (algebraMap V (FractionRing V)))) ''ᵁ ⊤ = X.basicOpen s := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_pullbackFst, opensRange_frac hϖ,
      Scheme.preimage_basicOpen_top]
  have hfac : (pullback.fst p (spMap (algebraMap V (FractionRing V)))).appTop =
      X.presheaf.map (homOfLE le_top : (pullback.fst p (spMap (algebraMap V (FractionRing V)))) ''ᵁ ⊤ ⟶ ⊤).op ≫
        ((pullback.fst p (spMap (algebraMap V (FractionRing V)))).appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    exact Scheme.Hom.app_eq_appLE _
  have hinj := restrict_basicOpen_injective s (fun f hf => eq_zero_of_mul p hϖ.ne_zero f hf)
  have hW : ∀ (W : X.Opens), W = X.basicOpen s →
      Function.Injective (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
    rintro W rfl
    exact hinj
  rw [hfac]
  intro a b hab
  simp only [CategoryTheory.comp_apply] at hab
  exact hW _ hrange ((ConcreteCategory.bijective_of_isIso _).1 hab)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen
