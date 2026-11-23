import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcComparisonStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolArc

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {W : ValuationSubring ℂ}

theorem mono_j_of_valuationSubring (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) : Mono Y.j := by
  have : IsPreimmersion (spMap V.subtype) := IsPreimmersion.of_isLocalization (nonZeroDivisors V) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap V.subtype)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  unfold Model.j
  infer_instance

theorem exists_factor (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) {K : Type} [Field K] (x : Sp K ⟶ pullback Z.s (spMap bV))
    (hx : (x ≫ pullback.fst Z.s (spMap bV)) (default : PrimeSpectrum K) ∈ Set.range Z.j) :
    ∃ y : Sp K ⟶ Xo.XF c, y ≫ Z.j = x ≫ pullback.fst Z.s (spMap bV) ∧
      (y ≫ pullback.snd _ _) ≫ spMap (c.V W).subtype = x ≫ pullback.snd Z.s (spMap bV) := by
  haveI : NumberField c.F := { to_finiteDimensional := c.fin }
  have hβ : (c.V W).subtype.comp bV = algebraMap (𝓞 c.F) c.F := RingHom.ext hbV
  have hsp : spMap (c.V W).subtype ≫ spMap bV = spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← hβ]; exact (Geo.Tor.spMap_comp _ _).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : c.V W →+* K, x ≫ pullback.snd Z.s (spMap bV) = spMap φ :=
    ⟨(Spec.preimage (x ≫ pullback.snd Z.s (spMap bV))).hom,
      (Spec.map_preimage (x ≫ pullback.snd Z.s (spMap bV))).symm⟩
  obtain ⟨q, hq⟩ := hx
  have e0 : (x ≫ pullback.fst Z.s (spMap bV)) ≫ Z.s = spMap (φ.comp bV) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hφ, Geo.Tor.spMap_comp]
  have hinj : Function.Injective (φ.comp bV) := by
    obtain ⟨r, e1⟩ : ∃ r : PrimeSpectrum c.F, PrimeSpectrum.comap (φ.comp bV) default =
        PrimeSpectrum.comap (algebraMap (𝓞 c.F) c.F) r := by
      have e2 : ((x ≫ pullback.fst Z.s (spMap bV)) ≫ Z.s) (default : PrimeSpectrum K) = (Z.j ≫ Z.s) q :=
        (congrArg Z.s hq).symm
      rw [e0, Model.j_s] at e2
      exact ⟨_, e2⟩
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap (φ.comp bV) default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.eq_bot_of_prime r.asIdeal] at h1
    exact RingOfIntegers.ext h1
  let ψ : c.F →+* K := IsFractionRing.lift hinj
  have hψ : ∀ a, ψ (algebraMap (𝓞 c.F) c.F a) = φ (bV a) := fun a => IsFractionRing.lift_algebraMap hinj a
  have hψφ : ψ.comp (c.V W).subtype = φ := by
    ext v
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 c.F) (v : c.F)
    have hb0 : algebraMap (𝓞 c.F) c.F b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have h2 : (v : c.F) * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
      rw [← e]; field_simp
    have e' : v * bV b = bV a := Subtype.ext (by
      have := h2
      simpa [hbV] using this)
    have h1 : φ v * φ (bV b) = φ (bV a) := by rw [← map_mul, e']
    have h3 : ψ (v : c.F) * φ (bV b) = φ (bV a) := by rw [← hψ, ← hψ, ← map_mul, h2]
    have hne : φ (bV b) ≠ 0 := fun h => hb0 (by
      have : b = 0 := hinj (by simpa using h)
      simp [this])
    exact mul_right_cancel₀ hne (h3.trans h1.symm)
  have hs : (x ≫ pullback.fst Z.s (spMap bV)) ≫ Z.s = spMap ψ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [e0, ← hsp, ← Category.assoc, ← Geo.Tor.spMap_comp, hψφ, Geo.Tor.spMap_comp]
  let z' : Sp K ⟶ pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift _ _ hs
  have hz₁ : z' ≫ pullback.fst _ _ = x ≫ pullback.fst Z.s (spMap bV) := pullback.lift_fst _ _ _
  have hz₂ : z' ≫ pullback.snd _ _ = spMap ψ := pullback.lift_snd _ _ _
  have := Z.jQ_open
  have hr : Set.range z' ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [← Z.ab_gen]
    have h₁ : Z.jQ q ∈ pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Z.t.G :=
      Z.ab_gen ▸ ⟨q, rfl⟩
    have h₂ : Z.j q ∈ abLocus Z.t.G := h₁
    rw [hq, ← hz₁] at h₂
    exact h₂
  refine ⟨IsOpenImmersion.lift Z.jQ z' hr, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz₁]
  · rw [← Z.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, hz₂, hφ, ← Geo.Tor.spMap_comp, hψφ]

end SlopeTestRemainingChoices

theorem eq_of_comp_eq_of_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype) (bV : 𝓞 c.F →+* c.V W)
    (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (f : pullback Z.s (spMap bV) ⟶ Y.X) (t : SAB H (pullback Z.s (spMap bV)))
    (m₁ : SABMap t Z.t (pullback.fst Z.s (spMap bV))) (m₂ : SABMap t Y.t f),
    f ≫ Y.s = pullback.snd Z.s (spMap bV) →
    (∀ a : Xo.XF c ⟶ pullback Z.s (spMap bV), a ≫ pullback.fst Z.s (spMap bV) = Z.j → a ≫ f = Y.j) →
    (∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y.m.φ) →
    ∀ (R : Type) [CommRing R] [IsDomain R] (g₁ g₂ : Sp R ⟶ pullback Z.s (spMap bV)),
      (∀ x : Sp R, x.asIdeal = ⊥ → pullback.fst Z.s (spMap bV) (g₁ x) ∈ Set.range Z.j) → g₁ ≫ f = g₂ ≫ f → g₁ = g₂ := by
  intro E _ _ _ H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hover hj hc R _ _ g₁ g₂ hgen hgf
  have hrange := GlobalTheory.T.pullback_model_arc_comparison E H D l Xo c p W hp hW Z Y bV hbV f t m₁ m₂ hover hj hc
  have hη : (jK R (default : PrimeSpectrum (FractionRing R))).asIdeal = ⊥ :=
    by
    rw [Subsingleton.elim (default : PrimeSpectrum (FractionRing R)) ⊥]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))
  have h₁ : ((jK R ≫ g₁) ≫ pullback.fst Z.s (spMap bV)) (default : PrimeSpectrum (FractionRing R)) ∈
      Set.range Z.j := hgen _ hη
  have hf : f ((jK R ≫ g₂) (default : PrimeSpectrum (FractionRing R))) =
      f ((jK R ≫ g₁) (default : PrimeSpectrum (FractionRing R))) :=
    congrArg (fun u : Sp R ⟶ Y.X => u (jK R (default : PrimeSpectrum (FractionRing R)))) hgf.symm
  have h₂ : ((jK R ≫ g₂) ≫ pullback.fst Z.s (spMap bV)) (default : PrimeSpectrum (FractionRing R)) ∈
      Set.range Z.j := (hrange _).2 (hf ▸ (hrange _).1 h₁)
  obtain ⟨y₁, a₁, b₁⟩ := exists_factor Z bV hbV (jK R ≫ g₁) h₁
  obtain ⟨y₂, a₂, b₂⟩ := exists_factor Z bV hbV (jK R ≫ g₂) h₂
  have hβ : (c.V W).subtype.comp bV = algebraMap (𝓞 c.F) c.F := RingHom.ext hbV
  have hsp : spMap (c.V W).subtype ≫ spMap bV = spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← hβ]; exact (Geo.Tor.spMap_comp _ _).symm
  let a : Xo.XF c ⟶ pullback Z.s (spMap bV) :=
    pullback.lift Z.j (pullback.snd _ _ ≫ spMap (c.V W).subtype) (by
      rw [Model.j_s, Category.assoc, hsp])
  have ha : a ≫ f = Y.j := hj a (pullback.lift_fst _ _ _)
  have key : ∀ (y : Sp (FractionRing R) ⟶ Xo.XF c) (x : Sp (FractionRing R) ⟶ pullback Z.s (spMap bV)),
      y ≫ Z.j = x ≫ pullback.fst Z.s (spMap bV) →
      (y ≫ pullback.snd _ _) ≫ spMap (c.V W).subtype = x ≫ pullback.snd Z.s (spMap bV) → y ≫ a = x := by
    intro y x e₁ e₂
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, e₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, e₂]
  have k₁ := key y₁ _ a₁ b₁
  have k₂ := key y₂ _ a₂ b₂
  have := mono_j_of_valuationSubring (c.V W) Y
  have hy : y₁ = y₂ := by
    rw [← cancel_mono Y.j, ← ha, ← Category.assoc, ← Category.assoc, k₁, k₂, Category.assoc, Category.assoc, hgf]
  have := isProper_toroidalModel_structureMap Z
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  refine ext_of_isDominant_of_isSeparated (pullback.snd Z.s (spMap bV)) ?_ (jK R) ?_
  · rw [← hover, ← Category.assoc, ← Category.assoc, hgf]
  · rw [← k₁, ← k₂, hy]

end GlobalTheory.PolArc
