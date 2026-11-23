import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitRank

theorem evalZ_comb' {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (a : ℕ)
    (ψ : InvFun O) (b : ℕ) (φ : InvFun O) (β : LinearMap.BilinForm ℤ X) :
    (comb a ψ b φ).evalZ β = a * ψ.evalZ β + b * φ.evalZ β := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  unfold InvFun.evalZ
  rw [(comb a ψ b φ).eval_eq hr, ψ.eval_eq hr, φ.eval_eq hr]
  rfl

theorem exists_generic_of_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (W : Type) [CommRing W] [IsDomain W] [CharZero W]
    (χ : Sp W ⟶ Z.X) (hχ : Set.range (jK W ≫ χ) ⊆ Set.range Z.j) :
    ∃ y : Sp (FractionRing W) ⟶ Xo.XF c, y ≫ Z.j = jK W ≫ χ := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI : CharZero (FractionRing W) := by
    refine ⟨fun a b h => Nat.cast_injective (R := W) (IsFractionRing.injective W (FractionRing W) ?_)⟩
    simpa using h
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (jK W ≫ χ ≫ Z.s)
  let β' : 𝓞 c.F →+* FractionRing W := β₀.hom
  have hinj : Function.Injective β' := GlobalTheory.LieUnif.injective_of_charZero (E := c.F) β'
  let g : c.F →+* FractionRing W := IsFractionRing.lift (K := c.F) hinj
  have hsq : (jK W ≫ χ) ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    have hb : β₀ = CommRingCat.ofHom (g.comp (algebraMap (𝓞 c.F) c.F)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      have := IsFractionRing.lift_algebraMap (K := c.F) hinj a
      exact this.symm
    rw [Category.assoc, ← hβ₀, hb]
    show _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  let u : Sp (FractionRing W) ⟶ pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift (jK W ≫ χ) (spMap g) hsq
  have hu : Set.range u ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Z.ab_gen]
    obtain ⟨v, hv⟩ := hχ ⟨p, rfl⟩
    have e1 : (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) (u p) = (jK W ≫ χ) p := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    show (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) (u p) ∈ abLocus Z.t.G
    rw [e1, ← hv]
    have : Z.jQ v ∈ (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) ⁻¹' abLocus Z.t.G := by
      rw [Z.ab_gen]; exact ⟨v, rfl⟩
    exact this
  haveI := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ u hu, ?_⟩
  show _ ≫ Z.jQ ≫ pullback.fst _ _ = _
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

theorem finrank_le_min_of_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [CharZero R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (m : SABMap t Z.t ξ)
    (P : PELUnif (maximalIdeal R) t) (hξ : Set.range (jK R ≫ ξ) ⊆ Set.range Z.j) :
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q := by
  obtain ⟨y, hy⟩ := exists_generic_of_range Z R ξ hξ
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.XF c := spMap (algebraMap (FractionRing R) K) ≫ y
  have hx : x' ≫ Z.jQ ≫ pullback.fst _ _ = spMap f ≫ ξ := by
    show (spMap (algebraMap (FractionRing R) K) ≫ y) ≫ Z.j = _
    rw [Category.assoc, hy, ← Category.assoc]
    show (Spec.map _ ≫ Spec.map _) ≫ ξ = _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective
    (x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have hβ : x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β₀.hom :=
    hβ₀.symm
  have hdet := (Z.oF.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Z.oF.t.act x' τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback Z.m.cart Z.oF.t.act Z.t.act Z.m.act x' τ N).1 hN
    rw [hx] at h₅
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart t.act Z.t.act m.act (spMap f) τ N).2 h₅
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem order_nat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∃ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX _ _ href _ _ _ _ _ _ W _ _ _ hW _ ϖ _ χ t mt P hχ be
    hbe hmon
  obtain ⟨hdvr, -, hch⟩ := hW
  haveI := hdvr
  haveI := hch
  have hrk := finrank_le_min_of_range Z W χ t mt P hχ
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  have hF := href.1 P.D.toPre.X hrk
  have hbal : be ∈ balForms H.bar P.D.toPre.X := by rw [balForms_eq_levelForms]; exact hbe
  obtain ⟨a, ha⟩ := hF.exists_nat hbal (fun y => hmon.nonneg 0 y)
  refine ⟨n * d' * a, ?_⟩
  rw [evalZ_comb', ha]
  push_cast
  ring

end GlobalTheory.TraitRank
