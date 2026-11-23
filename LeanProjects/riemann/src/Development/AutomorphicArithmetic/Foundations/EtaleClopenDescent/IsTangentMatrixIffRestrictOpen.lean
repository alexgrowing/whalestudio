import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

set_option autoImplicit false
noncomputable section
namespace UpperTheory.TanRes

private def Wit {B : Type} [CommRing B] [Algebra ℂ B] (d : ℕ) (ev : B → ℂ) (τ₁ τ₂ : Fin d → B)
    (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
    (∀ (b : B) (ω : Ω[B⁄ℂ]), φ (b • ω) = ev b • φ ω) ∧
    (∀ l, φ (D ℂ B (τ₁ l)) = Pi.single l 1) ∧
    (∀ j, φ (D ℂ B (τ₂ j)) = fun l => A j l) ∧
    ∀ ω : Ω[B⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → B) (ω' : Fin m → Ω[B⁄ℂ]),
      (∀ i, ev (b i) = 0) ∧ ω = ∑ i, b i • ω' i

private theorem Wit.loc {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℂ B] [Algebra ℂ B'] [Algebra B B']
    [IsScalarTower ℂ B B'] (M : Submonoid B) [IsLocalization M B'] (e : B →+* ℂ) (e' : B' →+* ℂ)
    (he : ∀ b, e' (algebraMap B B' b) = e b) (hc : ∀ a : ℂ, e' (algebraMap ℂ B' a) = a)
    {d : ℕ} {τ₁ τ₂ : Fin d → B} {A : Matrix (Fin d) (Fin d) ℂ} (h : Wit d e τ₁ τ₂ A) :
    Wit d e' (fun l => algebraMap B B' (τ₁ l)) (fun l => algebraMap B B' (τ₂ l)) A := by
  obtain ⟨φ, hs, h1, h2, hk⟩ := h
  letI mB' : Module B' (Fin d → ℂ) := Module.compHom _ e'
  letI mB : Module B (Fin d → ℂ) := Module.compHom _ e
  have smulB' : ∀ (b : B') (x : Fin d → ℂ), b • x = e' b • x := fun _ _ => rfl
  have smulB : ∀ (b : B) (x : Fin d → ℂ), b • x = e b • x := fun _ _ => rfl
  haveI : IsScalarTower B B' (Fin d → ℂ) := ⟨fun b b' x => by
    rw [Algebra.smul_def, smulB', smulB', smulB, map_mul, he, mul_smul]⟩
  haveI : IsScalarTower ℂ B' (Fin d → ℂ) := ⟨fun a b' x => by
    rw [Algebra.smul_def, smulB', smulB', map_mul, hc, mul_smul]⟩
  let φB : Ω[B⁄ℂ] →ₗ[B] (Fin d → ℂ) :=
    { toFun := φ, map_add' := φ.map_add, map_smul' := fun b ω => hs b ω }
  haveI hl := KaehlerDifferential.isLocalizedModule_map ℂ B B' M
  have hbc := IsLocalizedModule.isBaseChange M B' (KaehlerDifferential.map ℂ ℂ B B')
  let φ' : Ω[B'⁄ℂ] →ₗ[B'] (Fin d → ℂ) := hbc.lift φB
  have hφ' : ∀ ω, φ' (KaehlerDifferential.map ℂ ℂ B B' ω) = φ ω := fun ω => hbc.lift_eq φB ω
  have hD : ∀ b : B, φ' (D ℂ B' (algebraMap B B' b)) = φ (D ℂ B b) := fun b => by
    rw [← hφ', KaehlerDifferential.map_D]
  refine ⟨φ'.restrictScalars ℂ, fun b ω => φ'.map_smul b ω, fun l => ?_, fun j => ?_, fun ω hω => ?_⟩
  · exact (hD _).trans (h1 l)
  · exact (hD _).trans (h2 j)
  · obtain ⟨⟨ω₀, c⟩, hc'⟩ := IsLocalizedModule.surj M (KaehlerDifferential.map ℂ ℂ B B') ω
    have hω' : φ' ω = 0 := hω
    have hc'' : algebraMap B B' (c : B) • ω = KaehlerDifferential.map ℂ ℂ B B' ω₀ := by
      rw [algebraMap_smul]; exact hc'
    have h0 : φ ω₀ = 0 := by
      rw [← hφ', ← hc'', map_smul, hω', smul_zero]
    obtain ⟨m, b, ω₁, hb, rfl⟩ := hk ω₀ h0
    obtain ⟨u, hu⟩ := IsLocalization.map_units B' c |>.exists_left_inv
    refine ⟨m, fun i => algebraMap B B' (b i),
      fun i => u • KaehlerDifferential.map ℂ ℂ B B' (ω₁ i), fun i => ?_, ?_⟩
    · rw [he]; exact hb i
    · have : ω = u • (algebraMap B B' (c : B) • ω) := by rw [smul_smul, hu, one_smul]
      rw [this, hc'', map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← algebraMap_smul B' (b i), smul_comm]

private theorem Wit.equiv {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℂ B] [Algebra ℂ B'] (ρ : B ≃ₐ[ℂ] B')
    (e : B →+* ℂ) (e' : B' →+* ℂ) (he : ∀ b, e' (ρ b) = e b) (hc : ∀ a : ℂ, e' (algebraMap ℂ B' a) = a)
    {d : ℕ} {τ₁ τ₂ : Fin d → B} {A : Matrix (Fin d) (Fin d) ℂ} (h : Wit d e τ₁ τ₂ A) :
    Wit d e' (fun l => ρ (τ₁ l)) (fun l => ρ (τ₂ l)) A := by
  letI : Algebra B B' := ρ.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ B B' := .of_algebraMap_eq fun a => (ρ.commutes a).symm
  haveI : IsLocalization (⊥ : Submonoid B) B' :=
    { map_units := fun c => by
        obtain ⟨c, hc'⟩ := c
        rw [Submonoid.mem_bot] at hc'
        subst hc'
        simp
      surj := fun z => ⟨(ρ.symm z, 1), by
        change z * ρ 1 = ρ (ρ.symm z)
        simp⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        have : x = y := ρ.injective h
        rw [this]⟩ }
  exact Wit.loc ⊥ e e' he hc h

section Geo

variable {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ}

private theorem exists_basicOpen_two {X : Scheme.{0}} {U O : X.Opens} (hU : IsAffineOpen U) {a b : X} (ha : a ∈ U)
    (hb : b ∈ U) (ha' : a ∈ O) (hb' : b ∈ O) :
    ∃ f : Γ(X, U), X.basicOpen f ≤ O ∧ a ∈ X.basicOpen f ∧ b ∈ X.basicOpen f := by
  obtain ⟨f₁, h₁, a₁⟩ := hU.exists_basicOpen_le ⟨a, ha'⟩ ha
  obtain ⟨f₂, h₂, b₂⟩ := hU.exists_basicOpen_le ⟨b, hb'⟩ hb
  by_cases c₁ : b ∈ X.basicOpen f₁
  · exact ⟨f₁, h₁, a₁, c₁⟩
  by_cases c₂ : a ∈ X.basicOpen f₂
  · exact ⟨f₂, h₂, c₂, b₂⟩
  have key : ∀ (x : X) (hx : x ∈ U), x ∈ X.basicOpen (f₁ + f₂) ↔
      IsUnit ((X.presheaf.germ U x hx).hom f₁ + (X.presheaf.germ U x hx).hom f₂) := fun x hx => by
    rw [Scheme.mem_basicOpen _ _ _ hx, map_add]
  have mix : ∀ {R : Type} [CommRing R] [IsLocalRing R] {u v : R}, IsUnit u → ¬ IsUnit v → IsUnit (u + v) :=
    fun {R} _ _ {u v} hu hv => by
      have h : IsUnit ((u + v) + (-v)) := by simpa using hu
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
      · exact h
      · exact absurd (by simpa using h) hv
  refine ⟨f₁ + f₂, fun x hx => ?_, ?_, ?_⟩
  · have hxU : x ∈ U := X.basicOpen_le _ hx
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add ((key x hxU).1 hx) with h | h
    · exact h₁ ((Scheme.mem_basicOpen _ _ _ hxU).2 h)
    · exact h₂ ((Scheme.mem_basicOpen _ _ _ hxU).2 h)
  · refine (key a ha).2 (mix ((Scheme.mem_basicOpen _ _ _ ha).1 a₁) fun h => c₂ ?_)
    exact (Scheme.mem_basicOpen _ _ _ ha).2 h
  · rw [key b hb, add_comm]
    refine mix ((Scheme.mem_basicOpen _ _ _ hb).1 b₂) fun h => c₁ ?_
    exact (Scheme.mem_basicOpen _ _ _ hb).2 h

private def evS (y : CxPts s' (RingHom.id ℂ)) {V : Y.Opens} (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) : Sec s' V →+* ℂ :=
  CxPts.evHom h

private theorem evS_apply (y : CxPts s' (RingHom.id ℂ)) {V : Y.Opens} (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V)
    (b : Sec s' V) : evS y h b = CxPts.ev s' (RingHom.id ℂ) V b y :=
  (CxPts.ev_eq h b).symm

private theorem evS_algebraMap (y : CxPts s' (RingHom.id ℂ)) {V : Y.Opens} (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V)
    (a : ℂ) : evS y h (algebraMap ℂ (Sec s' V) a) = a := by
  rw [evS_apply]
  exact CxPts.ev_algX h a

private theorem res_app_res (c : Y ⟶ Z) (hc : c ≫ s = s') {U U₂ : Z.Opens} (hU : U₂ ≤ U) {V V₂ : Y.Opens} (hV : V ≤ c ⁻¹ᵁ U)
    (hV₂ : V₂ ≤ c ⁻¹ᵁ U₂) (hVV : V₂ ≤ V) (t : Sec s U) :
    Sec.res s' hV₂ (appSec s s' c U₂ (Sec.res s hU t)) = Sec.res s' hVV (Sec.res s' hV (appSec s s' c U t)) := by
  change (Z.presheaf.map (homOfLE hU).op ≫ c.app U₂ ≫ Y.presheaf.map (homOfLE hV₂).op).hom t =
    (c.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ Y.presheaf.map (homOfLE hVV).op).hom t
  congr 2
  rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  rfl

private theorem image_preimage_ι {X : Scheme.{0}} (O : X.Opens) {U : X.Opens} (h : U ≤ O) : O.ι ''ᵁ O.ι ⁻¹ᵁ U = U := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 h

private theorem isAffineOpen_ι_preimage_iff {X : Scheme.{0}} (O : X.Opens) {U : X.Opens} (h : U ≤ O) :
    IsAffineOpen (O.ι ⁻¹ᵁ U) ↔ IsAffineOpen U := by
  rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion O.ι, image_preimage_ι O h]

private theorem isIso_ι_app {X : Scheme.{0}} (O : X.Opens) {U : X.Opens} (h : U ≤ O) : IsIso (O.ι.app U) := by
  rw [Scheme.Opens.ι_app]
  have key : ∀ {A B : X.Opens} (f : A ⟶ B), A = B → IsIso (X.presheaf.map f.op) := by
    rintro A B f rfl
    rw [Subsingleton.elim f (𝟙 A), op_id, CategoryTheory.Functor.map_id]
    infer_instance
  exact key _ (image_preimage_ι O h)

private def appAlg {X : Scheme.{0}} (p : X ⟶ Sp ℂ) (O : X.Opens) {U : X.Opens} (h : U ≤ O) :
    Sec p U ≃ₐ[ℂ] Sec (O.ι ≫ p) (O.ι ⁻¹ᵁ U) :=
  AlgEquiv.ofBijective
    { appSec p (O.ι ≫ p) O.ι U with
      commutes' := fun r => (semiHom_appSec (rfl : O.ι ≫ p = O.ι ≫ p) U).map_algebraMap r }
    (haveI := isIso_ι_app O h
     ConcreteCategory.bijective_of_isIso (O.ι.app U))

private theorem le_down {Z₂ Y₂ : Scheme.{0}} (i : Z₂ ⟶ Z) (j : Y₂ ⟶ Y) (c : Y ⟶ Z) (c' : Y₂ ⟶ Z₂) (e : c' ≫ i = j ≫ c)
    {U : Z.Opens} {V : Y.Opens} (h : V ≤ c ⁻¹ᵁ U) : j ⁻¹ᵁ V ≤ c' ⁻¹ᵁ (i ⁻¹ᵁ U) := by
  intro x hx
  have key : i (c' x) = c (j x) := congrArg (fun f : Y₂ ⟶ Z => f x) e
  change i (c' x) ∈ U
  rw [key]
  exact h hx

private theorem le_up (FinalForm : Z.Opens) (Wo : Y.Opens) (c : Y ⟶ Z) (c' : Wo.toScheme ⟶ FinalForm.toScheme)
    (e : c' ≫ FinalForm.ι = Wo.ι ≫ c) {U : Z.Opens} {V : Y.Opens} (hV : V ≤ Wo)
    (h : Wo.ι ⁻¹ᵁ V ≤ c' ⁻¹ᵁ (FinalForm.ι ⁻¹ᵁ U)) : V ≤ c ⁻¹ᵁ U := by
  intro x hx
  let x' : Wo.toScheme := ⟨x, hV hx⟩
  have key : FinalForm.ι (c' x') = c (Wo.ι x') := congrArg (fun f : Wo.toScheme ⟶ Z => f x') e
  have hx' : x' ∈ Wo.ι ⁻¹ᵁ V := hx
  have h2 : FinalForm.ι (c' x') ∈ U := h hx'
  rw [key] at h2
  exact h2

private theorem app_res_app {Z₂ Y₂ : Scheme.{0}} {s₂ : Z₂ ⟶ Sp ℂ} {s₂' : Y₂ ⟶ Sp ℂ} (i : Z₂ ⟶ Z) (j : Y₂ ⟶ Y)
    (c : Y ⟶ Z) (c' : Y₂ ⟶ Z₂) (e : c' ≫ i = j ≫ c) {U : Z.Opens} {V : Y.Opens} (hV : V ≤ c ⁻¹ᵁ U)
    (hV' : j ⁻¹ᵁ V ≤ c' ⁻¹ᵁ (i ⁻¹ᵁ U)) (t : Sec s U) :
    appSec s' s₂' j V (Sec.res s' hV (appSec s s' c U t)) =
      Sec.res s₂' hV' (appSec s₂ s₂' c' (i ⁻¹ᵁ U) (appSec s s₂ i U t)) := by
  change (c.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ j.app V).hom t =
    (i.app U ≫ c'.app (i ⁻¹ᵁ U) ≫ Y₂.presheaf.map (homOfLE hV').op).hom t
  have key : ∀ (f g : Y₂ ⟶ Z) (_ : f = g) (h : j ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (h' : j ⁻¹ᵁ V ≤ g ⁻¹ᵁ U),
      f.appLE U (j ⁻¹ᵁ V) h = g.appLE U (j ⁻¹ᵁ V) h' := by
    rintro f g rfl h h'; rfl
  have l : c.app U ≫ Y.presheaf.map (homOfLE hV).op ≫ j.app V =
      (j ≫ c).appLE U (j ⁻¹ᵁ V) (fun x hx => hV hx) := by
    rw [← Category.assoc, ← appLE_comp_app c j V U hV (fun x hx => hV hx)]
    rfl
  have hV'' : j ⁻¹ᵁ V ≤ (c' ≫ i) ⁻¹ᵁ U := hV'
  have r : i.app U ≫ c'.app (i ⁻¹ᵁ U) ≫ Y₂.presheaf.map (homOfLE hV').op =
      (c' ≫ i).appLE U (j ⁻¹ᵁ V) hV'' := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  exact congrArg (fun q => q.hom t) ((l.trans (key _ _ e.symm _ _)).trans r.symm)

private theorem shrink {d : ℕ} {c1 c2 : Y ⟶ Z} (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') {y : CxPts s' (RingHom.id ℂ)}
    {A : Matrix (Fin d) (Fin d) ℂ} (h : IsTan d c1 c2 h1 h2 y A) (FinalForm : Z.Opens) (Wo : Y.Opens)
    (a1 : c1 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ FinalForm) (a2 : c2 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ FinalForm)
    (a3 : y.1 (IsLocalRing.closedPoint ℂ) ∈ Wo) :
    ∃ (U : Z.Opens) (V : Y.Opens) (hV1 : V ≤ c1 ⁻¹ᵁ U) (hV2 : V ≤ c2 ⁻¹ᵁ U) (t : Fin d → Sec s U),
      U ≤ FinalForm ∧ V ≤ Wo ∧ y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V ∧ IsAffineOpen U ∧ IsAffineOpen V ∧
      Wit d (fun b : Sec s' V => CxPts.ev s' (RingHom.id ℂ) V b y)
        (fun l => Sec.res s' hV1 (appSec s s' c1 U (t l)))
        (fun l => Sec.res s' hV2 (appSec s s' c2 U (t l))) A := by
  obtain ⟨U, V, hV1, hV2, t, hy, hU, hV, hw⟩ := h
  have hw' : Wit d (fun b : Sec s' V => CxPts.ev s' (RingHom.id ℂ) V b y)
      (fun l => Sec.res s' hV1 (appSec s s' c1 U (t l)))
      (fun l => Sec.res s' hV2 (appSec s s' c2 U (t l))) A := hw
  have hyV := CxPts.mem_ptsIn.1 hy
  obtain ⟨f, hf, hfa, hfb⟩ := exists_basicOpen_two hU (hV1 hyV) (hV2 hyV) a1 a2
  have hU₂ : Z.basicOpen f ≤ U := Z.basicOpen_le f
  have hyO : y.1 (IsLocalRing.closedPoint ℂ) ∈
      (Wo ⊓ (c1 ⁻¹ᵁ Z.basicOpen f ⊓ c2 ⁻¹ᵁ Z.basicOpen f) : Y.Opens) := ⟨a3, hfa, hfb⟩
  obtain ⟨g, hg, hgy⟩ := hV.exists_basicOpen_le ⟨_, hyO⟩ hyV
  have hVV : Y.basicOpen g ≤ V := Y.basicOpen_le g
  have hy₂ : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen g) := CxPts.mem_ptsIn.2 hgy
  have hV₁ : Y.basicOpen g ≤ c1 ⁻¹ᵁ Z.basicOpen f := fun x hx => (hg hx).2.1
  have hV₂ : Y.basicOpen g ≤ c2 ⁻¹ᵁ Z.basicOpen f := fun x hx => (hg hx).2.2
  refine ⟨Z.basicOpen f, Y.basicOpen g, hV₁, hV₂, fun l => Sec.res s hU₂ (t l), hf, fun x hx => (hg hx).1,
    hy₂, hU.basicOpen f, hV.basicOpen g, ?_⟩
  letI : Algebra (Sec s' V) (Sec s' (Y.basicOpen g)) := (Sec.res s' hVV).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (Sec s' V) (Sec s' (Y.basicOpen g)) :=
    .of_algebraMap_eq fun a => ((Sec.res s' hVV).commutes a).symm
  haveI : IsLocalization (Submonoid.powers (show Sec s' V from g)) (Sec s' (Y.basicOpen g)) :=
    hV.isLocalization_basicOpen g
  have he : ∀ b : Sec s' V, evS y hy₂ (algebraMap (Sec s' V) (Sec s' (Y.basicOpen g)) b) = evS y hy b := fun b => by
    rw [evS_apply, evS_apply]
    exact CxPts.ev_res hVV hy₂ b
  have E₀ : (fun b : Sec s' V => CxPts.ev s' (RingHom.id ℂ) V b y) = ⇑(evS y hy) :=
    funext fun b => (evS_apply y hy b).symm
  have E : (fun b : Sec s' (Y.basicOpen g) => CxPts.ev s' (RingHom.id ℂ) (Y.basicOpen g) b y) = ⇑(evS y hy₂) :=
    funext fun b => (evS_apply y hy₂ b).symm
  rw [E₀] at hw'
  have key := Wit.loc (B := Sec s' V) (B' := Sec s' (Y.basicOpen g)) (Submonoid.powers (show Sec s' V from g)) (evS y hy) (evS y hy₂) he (evS_algebraMap y hy₂) hw'
  rw [E, funext fun l => res_app_res c1 h1 hU₂ hV1 hV₁ hVV (t l),
    funext fun l => res_app_res c2 h2 hU₂ hV2 hV₂ hVV (t l)]
  exact key

private theorem wit_iff {d : ℕ} (FinalForm : Z.Opens) (Wo : Y.Opens) {c1 c2 : Y ⟶ Z} {c1' c2' : Wo.toScheme ⟶ FinalForm.toScheme}
    (e1 : c1' ≫ FinalForm.ι = Wo.ι ≫ c1) (e2 : c2' ≫ FinalForm.ι = Wo.ι ≫ c2) {y : CxPts s' (RingHom.id ℂ)}
    {y' : CxPts (Wo.ι ≫ s') (RingHom.id ℂ)} (hy : y'.1 ≫ Wo.ι = y.1) {U : Z.Opens} {V : Y.Opens} (hV : V ≤ Wo)
    (hyV : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (hV1 : V ≤ c1 ⁻¹ᵁ U) (hV2 : V ≤ c2 ⁻¹ᵁ U)
    (hV1' : Wo.ι ⁻¹ᵁ V ≤ c1' ⁻¹ᵁ (FinalForm.ι ⁻¹ᵁ U)) (hV2' : Wo.ι ⁻¹ᵁ V ≤ c2' ⁻¹ᵁ (FinalForm.ι ⁻¹ᵁ U))
    (t : Fin d → Sec s U) (A : Matrix (Fin d) (Fin d) ℂ) :
    Wit d (fun b : Sec s' V => CxPts.ev s' (RingHom.id ℂ) V b y)
        (fun l => Sec.res s' hV1 (appSec s s' c1 U (t l)))
        (fun l => Sec.res s' hV2 (appSec s s' c2 U (t l))) A ↔
      Wit d (fun b : Sec (Wo.ι ≫ s') (Wo.ι ⁻¹ᵁ V) => CxPts.ev (Wo.ι ≫ s') (RingHom.id ℂ) (Wo.ι ⁻¹ᵁ V) b y')
        (fun l => Sec.res (Wo.ι ≫ s') hV1'
          (appSec (FinalForm.ι ≫ s) (Wo.ι ≫ s') c1' (FinalForm.ι ⁻¹ᵁ U) (appSec s (FinalForm.ι ≫ s) FinalForm.ι U (t l))))
        (fun l => Sec.res (Wo.ι ≫ s') hV2'
          (appSec (FinalForm.ι ≫ s) (Wo.ι ≫ s') c2' (FinalForm.ι ⁻¹ᵁ U) (appSec s (FinalForm.ι ≫ s) FinalForm.ι U (t l)))) A := by
  have hy' : y' ∈ CxPts.ptsIn (Wo.ι ≫ s') (RingHom.id ℂ) (Wo.ι ⁻¹ᵁ V) := by
    rw [CxPts.mem_ptsIn]
    have := CxPts.mem_ptsIn.1 hyV
    rw [← hy] at this
    exact this
  let ρ := appAlg s' Wo hV
  have he : ∀ b, evS y' hy' (ρ b) = evS y hyV b := fun b => by
    rw [evS_apply, evS_apply]
    change valR y'.1 _ _ = valR y.1 _ _
    rw [← hy]
    exact (GlobalTheory.Points.valR_comp y'.1 Wo.ι V (show Γ(Y, V) from b)).symm
  have E₀ : (fun b : Sec s' V => CxPts.ev s' (RingHom.id ℂ) V b y) = ⇑(evS y hyV) :=
    funext fun b => (evS_apply y hyV b).symm
  have E₁ : (fun b : Sec (Wo.ι ≫ s') (Wo.ι ⁻¹ᵁ V) => CxPts.ev (Wo.ι ≫ s') (RingHom.id ℂ) (Wo.ι ⁻¹ᵁ V) b y') =
      ⇑(evS y' hy') := funext fun b => (evS_apply y' hy' b).symm
  have C1 : ∀ l, ρ (Sec.res s' hV1 (appSec s s' c1 U (t l))) = Sec.res (Wo.ι ≫ s') hV1'
      (appSec (FinalForm.ι ≫ s) (Wo.ι ≫ s') c1' (FinalForm.ι ⁻¹ᵁ U) (appSec s (FinalForm.ι ≫ s) FinalForm.ι U (t l))) := fun l =>
    app_res_app FinalForm.ι Wo.ι c1 c1' e1 hV1 hV1' (t l)
  have C2 : ∀ l, ρ (Sec.res s' hV2 (appSec s s' c2 U (t l))) = Sec.res (Wo.ι ≫ s') hV2'
      (appSec (FinalForm.ι ≫ s) (Wo.ι ≫ s') c2' (FinalForm.ι ⁻¹ᵁ U) (appSec s (FinalForm.ι ≫ s) FinalForm.ι U (t l))) := fun l =>
    app_res_app FinalForm.ι Wo.ι c2 c2' e2 hV2 hV2' (t l)
  rw [E₀, E₁, ← funext C1, ← funext C2]
  constructor
  · exact Wit.equiv ρ _ _ he (evS_algebraMap y' hy')
  · intro h
    have key := Wit.equiv ρ.symm (evS y' hy') (evS y hyV) (fun b => by rw [← he, AlgEquiv.apply_symm_apply])
      (evS_algebraMap y hyV) h
    simpa only [AlgEquiv.symm_apply_apply] using key

end Geo

end UpperTheory.TanRes

theorem UpperTheory.Cb.isTangentMatrix_iff_restrict_open :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (d : ℕ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') (V : Z.Opens) (W : Y.Opens) (c1' c2' : W.toScheme ⟶ V.toScheme) (e1 : c1' ≫ V.ι = W.ι ≫ c1) (e2 : c2' ≫ V.ι = W.ι ≫ c2) (y : CxPts s' (RingHom.id ℂ)) (y' : CxPts (W.ι ≫ s') (RingHom.id ℂ)), y'.1 ≫ W.ι = y.1 → ∀ A : Matrix (Fin d) (Fin d) ℂ, (IsTan d c1 c2 h1 h2 y A ↔ IsTan (s := V.ι ≫ s) d c1' c2' (by rw [← Category.assoc, e1, Category.assoc, h1]) (by rw [← Category.assoc, e2, Category.assoc, h2]) y' A) := by
  intro Z Y s s' d c1 c2 h1 h2 V W c1' c2' e1 e2 y y' hy A
  have hpt : W.ι (y'.1 (IsLocalRing.closedPoint ℂ)) = y.1 (IsLocalRing.closedPoint ℂ) := by
    rw [← hy]; rfl
  constructor
  · intro h
    have a3 : y.1 (IsLocalRing.closedPoint ℂ) ∈ W := by
      rw [← hpt]; exact (y'.1 (IsLocalRing.closedPoint ℂ)).2
    have a1 : c1 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ V := by
      rw [← hpt]
      have key : V.ι (c1' (y'.1 (IsLocalRing.closedPoint ℂ))) = c1 (W.ι (y'.1 (IsLocalRing.closedPoint ℂ))) :=
        congrArg (fun f : W.toScheme ⟶ Z => f (y'.1 (IsLocalRing.closedPoint ℂ))) e1
      rw [← key]
      exact (c1' (y'.1 (IsLocalRing.closedPoint ℂ))).2
    have a2 : c2 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ V := by
      rw [← hpt]
      have key : V.ι (c2' (y'.1 (IsLocalRing.closedPoint ℂ))) = c2 (W.ι (y'.1 (IsLocalRing.closedPoint ℂ))) :=
        congrArg (fun f : W.toScheme ⟶ Z => f (y'.1 (IsLocalRing.closedPoint ℂ))) e2
      rw [← key]
      exact (c2' (y'.1 (IsLocalRing.closedPoint ℂ))).2
    obtain ⟨U, V₀, hV1, hV2, t, hUle, hVle, hyV, hUa, hVa, hw⟩ :=
      UpperTheory.TanRes.shrink h1 h2 h V W a1 a2 a3
    have hV1' := UpperTheory.TanRes.le_down V.ι W.ι c1 c1' e1 hV1
    have hV2' := UpperTheory.TanRes.le_down V.ι W.ι c2 c2' e2 hV2
    refine ⟨V.ι ⁻¹ᵁ U, W.ι ⁻¹ᵁ V₀, hV1', hV2', fun l => appSec s (V.ι ≫ s) V.ι U (t l), ?_,
      (UpperTheory.TanRes.isAffineOpen_ι_preimage_iff V hUle).2 hUa,
      (UpperTheory.TanRes.isAffineOpen_ι_preimage_iff W hVle).2 hVa, ?_⟩
    · rw [CxPts.mem_ptsIn]
      have := CxPts.mem_ptsIn.1 hyV
      rw [← hy] at this
      exact this
    · exact (UpperTheory.TanRes.wit_iff V W e1 e2 hy hVle hyV hV1 hV2 hV1' hV2' t A).1 hw
  · rintro ⟨U₁, V₁, hV1', hV2', t₁, hy₁, hU₁, hV₁a, hw⟩
    obtain ⟨U, hU, rfl⟩ : ∃ U : Z.Opens, U ≤ V ∧ U₁ = V.ι ⁻¹ᵁ U :=
      ⟨V.ι ''ᵁ U₁, Scheme.Opens.ι_image_le _ _, (Scheme.Hom.preimage_image_eq _ _).symm⟩
    obtain ⟨V₀, hV₀, rfl⟩ : ∃ V₀ : Y.Opens, V₀ ≤ W ∧ V₁ = W.ι ⁻¹ᵁ V₀ :=
      ⟨W.ι ''ᵁ V₁, Scheme.Opens.ι_image_le _ _, (Scheme.Hom.preimage_image_eq _ _).symm⟩
    obtain ⟨t, rfl⟩ : ∃ t : Fin d → Sec s U, t₁ = fun l => appSec s (V.ι ≫ s) V.ι U (t l) :=
      ⟨fun l => (UpperTheory.TanRes.appAlg s V hU).symm (t₁ l), funext fun l =>
        ((UpperTheory.TanRes.appAlg s V hU).apply_symm_apply (t₁ l)).symm⟩
    have hV1 := UpperTheory.TanRes.le_up V W c1 c1' e1 hV₀ hV1'
    have hV2 := UpperTheory.TanRes.le_up V W c2 c2' e2 hV₀ hV2'
    have hyV : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V₀ := by
      rw [CxPts.mem_ptsIn]
      have := CxPts.mem_ptsIn.1 hy₁
      rw [← hy]
      exact this
    exact ⟨U, V₀, hV1, hV2, t, hyV, (UpperTheory.TanRes.isAffineOpen_ι_preimage_iff V hU).1 hU₁,
      (UpperTheory.TanRes.isAffineOpen_ι_preimage_iff W hV₀).1 hV₁a,
      (UpperTheory.TanRes.wit_iff V W e1 e2 hy hV₀ hyV hV1 hV2 hV1' hV2' t A).2 hw⟩
