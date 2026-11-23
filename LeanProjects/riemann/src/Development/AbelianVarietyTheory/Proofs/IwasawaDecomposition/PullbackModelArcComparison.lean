import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.GlobalLocalRange

theorem mem_range_generic {F : Type} [Field F] [NumberField F] (V : ValuationSubring F) (bV : 𝓞 F →+* V)
    (hbV : ∀ x, ((bV x : V) : F) = (x : F)) (v : Sp V)
    (h : spMap bV v ∈ Set.range (spMap (algebraMap (𝓞 F) F))) : v ∈ Set.range (spMap V.subtype) := by
  obtain ⟨u, hu⟩ := h
  have hu0 : u.asIdeal = ⊥ := (Ideal.eq_bot_or_top u.asIdeal).resolve_right u.isPrime.ne_top
  have hc : Ideal.comap bV v.asIdeal = ⊥ := by
    have : (spMap (algebraMap (𝓞 F) F) u).asIdeal = (spMap bV v).asIdeal := by rw [hu]
    change Ideal.comap (algebraMap (𝓞 F) F) u.asIdeal = Ideal.comap bV v.asIdeal at this
    rw [← this, hu0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have hv0 : v.asIdeal = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (x : F)
    have hb0 : (algebraMap (𝓞 F) F b) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero hb)
    have hax : bV a = x * bV b := by
      apply Subtype.ext
      change ((bV a : V) : F) = ((x : V) : F) * ((bV b : V) : F)
      rw [hbV, hbV, ← hab]
      change (algebraMap (𝓞 F) F a) = _ / _ * (algebraMap (𝓞 F) F b)
      field_simp
    have ha : a ∈ Ideal.comap bV v.asIdeal := by
      rw [Ideal.mem_comap, hax]; exact v.asIdeal.mul_mem_right _ hx
    rw [hc, Ideal.mem_bot] at ha
    rw [ha, map_zero, zero_div] at hab
    rw [Ideal.mem_bot]
    exact Subtype.ext (by simpa using hab.symm)
  refine ⟨u, PrimeSpectrum.ext ?_⟩
  change Ideal.comap V.subtype u.asIdeal = v.asIdeal
  rw [hu0, hv0]
  exact Ideal.comap_bot_of_injective _ Subtype.val_injective

end GlobalTheory.GlobalLocalRange

namespace GlobalTheory.GlobalLocalRange

theorem exists_generic_preimage {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} {W : ValuationSubring ℂ}
    (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (bV : 𝓞 c.F →+* c.V W)
    (hβ : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV)
    (q : (pullback Z.s (spMap bV) : Scheme.{0}))
    (hq : pullback.snd Z.s (spMap bV) q ∈ Set.range (spMap (c.V W).subtype)) :
    ∃ w : (pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) : Scheme.{0}),
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (c.V W).subtype)
        (by rw [pullback.condition, hβ, Category.assoc]) w = q := by
  obtain ⟨u, hu⟩ := hq
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd Z.s (spMap bV))
    (g := spMap (c.V W).subtype) q u hu.symm
  have hw : pullback.fst (pullback.snd Z.s (spMap bV)) (spMap (c.V W).subtype) ≫ pullback.fst _ _ ≫ Z.s =
      pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [pullback.condition, ← Category.assoc, pullback.condition, hβ, Category.assoc]
  let L : pullback (pullback.snd Z.s (spMap bV)) (spMap (c.V W).subtype) ⟶
      pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by rw [Category.assoc, hw])
  refine ⟨L z, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  have : L ≫
      pullback.lift (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) (pullback.snd _ _ ≫ spMap (c.V W).subtype)
        (by rw [pullback.condition, hβ, Category.assoc]) = pullback.fst _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, pullback.condition]
  rw [this, hz1]

end GlobalTheory.GlobalLocalRange

namespace GlobalTheory.GlobalLocalRange

theorem fst_mem_range_j_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
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
    ∀ q : (pullback Z.s (spMap bV) : Scheme.{0}), pullback.fst Z.s (spMap bV) q ∈ Set.range Z.j ↔ f q ∈ Set.range Y.j := by
  intro E _ _ _ H D l Xo c p W _ _ Z Y bV hbV f t m₁ m₂ hf hj _ q
  have hβ : spMap (algebraMap (𝓞 c.F) c.F) = spMap (c.V W).subtype ≫ spMap bV := by
    rw [← spMap_comp]
    congr 1
    exact RingHom.ext fun x => (hbV x).symm
  have hcond : pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ≫ Z.s =
      (pullback.snd Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ≫ spMap (c.V W).subtype) ≫ spMap bV := by
    rw [pullback.condition, hβ, Category.assoc]
  let e : pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ pullback Z.s (spMap bV) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (c.V W).subtype) hcond
  have he : e ≫ pullback.fst Z.s (spMap bV) = pullback.fst _ _ := pullback.lift_fst _ _ _

  have hgen : ∀ w, pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) w ∈ abLocus Z.t.G → w ∈ Set.range Z.jQ := by
    intro w hw
    rw [← Z.ab_gen]; exact hw
  constructor
  · rintro ⟨x, hx⟩
    have hs : pullback.snd Z.s (spMap bV) q ∈ Set.range (spMap (c.V W).subtype) := by
      refine mem_range_generic (c.V W) bV hbV _ ⟨pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) x, ?_⟩
      have e1 : spMap bV (pullback.snd Z.s (spMap bV) q) = Z.s (pullback.fst Z.s (spMap bV) q) := by
        rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      have e2 : Z.s (Z.j x) = spMap (algebraMap (𝓞 c.F) c.F)
          (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) x) := by
        rw [← Scheme.Hom.comp_apply, Model.j_s, Scheme.Hom.comp_apply]
      rw [e1, ← hx, e2]
    obtain ⟨w, hw⟩ := exists_generic_preimage Z bV hβ q hs
    change e w = q at hw
    have hab : pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) w ∈ abLocus Z.t.G := by
      have h1 : Z.jQ x ∈ pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Z.t.G := by
        rw [Z.ab_gen]; exact ⟨x, rfl⟩
      have h2 : pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) w = pullback.fst Z.s (spMap bV) q := by
        rw [← hw, ← Scheme.Hom.comp_apply, he]
      rw [h2, ← hx]
      exact h1
    obtain ⟨x', hx'⟩ := hgen w hab
    refine ⟨x', ?_⟩
    have ha : (Z.jQ ≫ e) ≫ pullback.fst Z.s (spMap bV) = Z.j := by rw [Category.assoc, he]; rfl
    rw [← hj _ ha, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx', hw]
  · rintro ⟨y, hy⟩
    have hs : pullback.snd Z.s (spMap bV) q ∈ Set.range (spMap (c.V W).subtype) := by
      refine ⟨pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) y, ?_⟩
      have e2 : Y.s (Y.j y) = spMap (c.V W).subtype
          (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) y) := by
        rw [← Scheme.Hom.comp_apply, Model.j_s, Scheme.Hom.comp_apply]
      rw [← hf, Scheme.Hom.comp_apply, ← hy, e2]
    obtain ⟨w, hw⟩ := exists_generic_preimage Z bV hβ q hs
    change e w = q at hw
    have hY : f q ∈ abLocus Y.t.G := by
      have h1 : Y.jQ y ∈ pullback.fst Y.s (spMap (c.V W).subtype) ⁻¹' abLocus Y.t.G := by
        rw [Y.ab_gen]; exact ⟨y, rfl⟩
      rw [← hy]; exact h1
    have hq : q ∈ abLocus t.G := (abLocus_pullback abLocusOne Y.t.semi m₂.cart.1 q).1 hY
    have hZ : pullback.fst Z.s (spMap bV) q ∈ abLocus Z.t.G :=
      (abLocus_pullback abLocusOne Z.t.semi m₁.cart.1 q).2 hq
    have h2 : pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) w = pullback.fst Z.s (spMap bV) q := by
      rw [← hw, ← Scheme.Hom.comp_apply, he]
    obtain ⟨x, hx⟩ := hgen w (h2 ▸ hZ)
    refine ⟨x, ?_⟩
    rw [← h2, ← hx]
    rfl

end GlobalTheory.GlobalLocalRange
