import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

namespace CoordExtend

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def valC {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalk (centre z) ⟶ CommRingCat.of R :=
  Scheme.stalkClosedPointTo z

abbrev val {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalk (centre z) →+* R :=
  (valC z).hom

instance {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) :
    IsLocalHom (val z) :=
  Scheme.isLocalHom_stalkClosedPointTo' z

def gm (ξ : Spec (CommRingCat.of Ω) ⟶ X) {p : X} (h : genPt ξ ⤳ p) : X.presheaf.stalk p →+* Ω :=
  genMap ξ ⟨p, h⟩

theorem gm_inj {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hG : IsCptGen ξ) {p : X} (h : genPt ξ ⤳ p) :
    Function.Injective (gm ξ h) :=
  hG.inj ⟨p, h⟩

theorem exists_gm {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : X} {h : genPt ξ ⤳ p} {a : Ω}
    (ha : a ∈ regAt ξ ⟨p, h⟩) : ∃ s : X.presheaf.stalk p, gm ξ h s = a :=
  RingHom.mem_range.1 ha

theorem mem_regAt_of_gm {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : X} {h : genPt ξ ⤳ p}
    (s : X.presheaf.stalk p) : gm ξ h s ∈ regAt ξ ⟨p, h⟩ :=
  RingHom.mem_range.2 ⟨s, rfl⟩

theorem spec_germ_fromSpec {R : Type} [CommRing R] [IsLocalRing R] (f : Spec (CommRingCat.of R) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (h : centre f ∈ U) :
    Spec.map (X.presheaf.germ U (centre f) h ≫ valC f) ≫ hU.fromSpec = f := by
  have e : Spec.map (X.presheaf.germ U (centre f) h) ≫ hU.fromSpec = X.fromSpecStalk (centre f) := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk h]; rfl
  rw [Spec.map_comp, Category.assoc, e]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk f

theorem val_specializes {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (τ : CommRingCat.of R ⟶ CommRingCat.of S) (f : Spec (CommRingCat.of R) ⟶ X)
    (w : centre (Spec.map τ ≫ f) ⤳ centre f) (s : X.presheaf.stalk (centre f)) :
    val (Spec.map τ ≫ f) ((X.presheaf.stalkSpecializes w).hom s) = τ.hom (val f s) := by
  obtain ⟨W, hW, g, rfl⟩ := X.presheaf.germ_exist s
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hW W.2
  replace hU : IsAffineOpen U := hU
  have hUW : U ≤ W := hle
  have hmem' : centre (Spec.map τ ≫ f) ∈ U := w.mem_open U.2 hmem
  have h1 := spec_germ_fromSpec f hU hmem
  have h2 := spec_germ_fromSpec (Spec.map τ ≫ f) hU hmem'
  have h3 : X.presheaf.germ U _ hmem' ≫ valC (Spec.map τ ≫ f) =
      (X.presheaf.germ U _ hmem ≫ valC f) ≫ τ := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, h2, Spec.map_comp, Category.assoc, h1]
  have h5 : X.presheaf.germ U _ hmem ≫ X.presheaf.stalkSpecializes w = X.presheaf.germ U _ hmem' :=
    TopCat.Presheaf.germ_stalkSpecializes ..
  rw [← h5, Category.assoc] at h3
  have h6 : X.presheaf.map (homOfLE hUW).op ≫ X.presheaf.germ U _ hmem = X.presheaf.germ W _ hW :=
    X.presheaf.germ_res (homOfLE hUW) _ hmem
  rw [← h6]
  exact congrArg (fun q => q.hom ((X.presheaf.map (homOfLE hUW).op).hom g)) h3

def gpC (ξ : Spec (CommRingCat.of Ω) ⟶ X) : X.presheaf.stalk (genPt ξ) ⟶ CommRingCat.of Ω :=
  Scheme.stalkClosedPointTo ξ

theorem gm_specializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) {p q : X} (hp : genPt ξ ⤳ p) (hq : genPt ξ ⤳ q)
    (w : p ⤳ q) (t : X.presheaf.stalk q) :
    gm ξ hp ((X.presheaf.stalkSpecializes w).hom t) = gm ξ hq t := by
  change (X.presheaf.stalkSpecializes w ≫ X.presheaf.stalkSpecializes hp ≫ gpC ξ).hom t =
    (X.presheaf.stalkSpecializes hq ≫ gpC ξ).hom t
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

theorem gm_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U : X.Opens} {p q : X} (hp : genPt ξ ⤳ p)
    (hq : genPt ξ ⤳ q) (hpU : p ∈ U) (hqU : q ∈ U) (g : Γ(X, U)) :
    gm ξ hp ((X.presheaf.germ U p hpU).hom g) = gm ξ hq ((X.presheaf.germ U q hqU).hom g) := by
  have hg : genPt ξ ∈ U := hp.mem_open U.2 hpU
  have e : ∀ (r : X) (hr : genPt ξ ⤳ r) (hrU : r ∈ U), gm ξ hr ((X.presheaf.germ U r hrU).hom g) =
      (X.presheaf.germ U (genPt ξ) hg ≫ gpC ξ).hom g := by
    intro r hr hrU
    change (X.presheaf.germ U r hrU ≫ X.presheaf.stalkSpecializes hr ≫ gpC ξ).hom g = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
  rw [e p hp hpU, e q hq hqU]

def GoodChart {C : Type} [Field C] (V : ValuationSubring C) (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type}
    (x : κ → Ω) (zC : Spec (CommRingCat.of C) ⟶ X) (h : genPt ξ ⤳ centre zC) (c : κ) : Prop :=
  x c ≠ 0 ∧ ∀ j, ∃ s : X.presheaf.stalk (centre zC), gm ξ h s = x j / x c ∧ val zC s ∈ V

theorem exists_goodChart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} [Finite κ] {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {C : Type} [Field C] (V : ValuationSubring C)
    (zC : Spec (CommRingCat.of C) ⟶ X) (h : genPt ξ ⤳ centre zC) : ∃ c, GoodChart V ξ x zC h c := by
  obtain ⟨c, hc, hreg⟩ := hT.cover ⟨centre zC, h⟩
  choose s hs using fun j => exists_gm (hreg j)
  have : Nonempty κ := ⟨c⟩
  obtain ⟨d, hd⟩ := Finite.exists_max (fun j => V.valuation (val zC (s j)))
  have hsc : s c = 1 := gm_inj hT.gen h (by rw [hs, map_one, div_self hc])
  have hv1 : val zC (s c) = 1 := by rw [hsc, map_one]
  have hr : val zC (s d) ≠ 0 := by
    intro h0
    have h1 := hd c
    rw [hv1, h0] at h1
    simp at h1
  have hunit : IsUnit (s d) := isUnit_of_map_unit (val zC) _ hr.isUnit
  have hne : x d / x c ≠ 0 := by
    rw [← hs d]
    exact (hunit.map (gm ξ h)).ne_zero
  have hxd : x d ≠ 0 := fun h0 => hne (by simp [h0])
  obtain ⟨e, he⟩ := hunit
  refine ⟨d, hxd, fun j => ⟨s j * (↑e⁻¹ : X.presheaf.stalk (centre zC)), ?_, ?_⟩⟩
  · have h1 : gm ξ h (↑e⁻¹ : X.presheaf.stalk (centre zC)) * (x d / x c) = 1 := by
      rw [← hs d, ← he, ← map_mul, Units.inv_mul, map_one]
    have h2 : gm ξ h (↑e⁻¹ : X.presheaf.stalk (centre zC)) = x c / x d := by
      field_simp at h1 ⊢
      exact h1
    rw [map_mul, hs j, h2]
    field_simp
  · have h1 : val zC (↑e⁻¹ : X.presheaf.stalk (centre zC)) * val zC (s d) = 1 := by
      rw [← he, ← map_mul, Units.inv_mul, map_one]
    have h2 : val zC (↑e⁻¹ : X.presheaf.stalk (centre zC)) = (val zC (s d))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    rw [map_mul, h2, ← V.valuation_le_one_iff, map_mul, map_inv₀, ← div_eq_mul_inv]
    have hv : V.valuation (val zC (s d)) ≠ 0 := by
      simpa using hr
    exact (div_le_one₀ (zero_lt_iff.2 hv)).2 (hd j)

theorem exists_of_goodChart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {C : Type} [Field C] (V : ValuationSubring C)
    (zC : Spec (CommRingCat.of C) ⟶ X) (h : genPt ξ ⤳ centre zC) {c : κ}
    (hg : GoodChart V ξ x zC h c) :
    ∃ (z : Spec (CommRingCat.of V) ⟶ X) (hz : genPt ξ ⤳ centre z),
      Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z = zC ∧ InChart ξ x c ⟨centre z, hz⟩ := by
  obtain ⟨hc, hj⟩ := hg
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have hch : InChart ξ x c ⟨centre zC, h⟩ := ⟨hc, fun j => by
    obtain ⟨s, hs, -⟩ := hj j
    rw [← hs]
    exact mem_regAt_of_gm s⟩
  have hp : centre zC ∈ U := (hmem _).2 ⟨h, hch⟩
  have hadj : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ s : X.presheaf.stalk (centre zC), gm ξ h s = a ∧ val zC s ∈ V := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact hj j
    | algebraMap n =>
      refine ⟨(n : X.presheaf.stalk (centre zC)), by simp, ?_⟩
      rw [map_intCast]
      exact intCast_mem V n
    | add a b _ _ iha ihb =>
      obtain ⟨s, hs, hsV⟩ := iha
      obtain ⟨t, ht, htV⟩ := ihb
      exact ⟨s + t, by rw [map_add, hs, ht], by rw [map_add]; exact add_mem hsV htV⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨s, hs, hsV⟩ := iha
      obtain ⟨t, ht, htV⟩ := ihb
      exact ⟨s * t, by rw [map_mul, hs, ht], by rw [map_mul]; exact mul_mem hsV htV⟩
  let ψ : Γ(X, U) ⟶ CommRingCat.of C := X.presheaf.germ U (centre zC) hp ≫ valC zC
  have hψ : ∀ g, ψ.hom g ∈ V := by
    intro g
    have hreg : gm ξ h ((X.presheaf.germ U (centre zC) hp).hom g) ∈
        Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
      refine (hT.ring c hc _).2 fun p hpc => ?_
      have hpU : p.1 ∈ U := (hmem _).2 ⟨p.2, hpc⟩
      rw [gm_germ ξ h p.2 hp hpU g]
      exact mem_regAt_of_gm _
    obtain ⟨s, hs, hsV⟩ := hadj _ hreg
    have := gm_inj hT.gen h hs
    rw [this] at hsV
    exact hsV
  let ρ : Γ(X, U) ⟶ CommRingCat.of V := CommRingCat.ofHom (ψ.hom.codRestrict V hψ)
  have hρ : ρ ≫ CommRingCat.ofHom (algebraMap V C) = ψ := by
    ext g
    rfl
  have hzU : centre (Spec.map ρ ≫ hU.fromSpec) ∈ U := by
    have h1 : centre (Spec.map ρ ≫ hU.fromSpec) ∈ Set.range hU.fromSpec :=
      ⟨Spec.map ρ (IsLocalRing.closedPoint V), rfl⟩
    rw [hU.range_fromSpec] at h1
    exact h1
  obtain ⟨hz, hzc⟩ := (hmem _).1 hzU
  refine ⟨Spec.map ρ ≫ hU.fromSpec, hz, ?_, hzc⟩
  rw [← Category.assoc, ← Spec.map_comp, hρ]
  exact spec_germ_fromSpec zC hU hp

theorem inChart_of_goodChart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {C : Type} [Field C] (V : ValuationSubring C)
    (z : Spec (CommRingCat.of V) ⟶ X) (hz : genPt ξ ⤳ centre z)
    (h : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z)) {c : κ}
    (hg : GoodChart V ξ x (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) h c) :
    InChart ξ x c ⟨centre z, hz⟩ := by
  have w : centre (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ⤳ centre z :=
    (IsLocalRing.specializes_closedPoint (R := V) _).map z.continuous
  obtain ⟨c', hc', hreg⟩ := hT.cover ⟨centre z, hz⟩
  obtain ⟨hc, hj⟩ := hg
  obtain ⟨t, ht⟩ := exists_gm (hreg c)
  obtain ⟨u, hu, huV⟩ := hj c'
  have ht' := gm_specializes ξ h hz w t
  rw [ht] at ht'
  have hmul : (X.presheaf.stalkSpecializes w).hom t * u = 1 := by
    apply gm_inj hT.gen h
    rw [map_mul, map_one, ht', hu]
    field_simp
  have hv := val_specializes (CommRingCat.ofHom (algebraMap V C)) z w t
  have hvu : val z t * ⟨_, huV⟩ = 1 := by
    apply Subtype.ext
    have := congrArg (val (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z)) hmul
    rw [map_mul, map_one, hv] at this
    exact this
  have hunit : IsUnit t := isUnit_of_map_unit (val z) _ (IsUnit.of_mul_eq_one _ hvu)
  obtain ⟨e, rfl⟩ := hunit
  refine ⟨hc, fun j => ?_⟩
  obtain ⟨b, hb⟩ := exists_gm (hreg j)
  have h1 : gm ξ hz (↑e⁻¹ : X.presheaf.stalk (centre z)) * (x c / x c') = 1 := by
    rw [← ht, ← map_mul, Units.inv_mul, map_one]
  have h2 : gm ξ hz (↑e⁻¹ : X.presheaf.stalk (centre z)) = x c' / x c := by
    field_simp at h1 ⊢
    exact h1
  have h3 : x j / x c = gm ξ hz (b * (↑e⁻¹ : X.presheaf.stalk (centre z))) := by
    rw [map_mul, hb, h2]
    field_simp
  rw [h3]
  exact mem_regAt_of_gm _

theorem eq_of_mem_affine {C : Type} [Field C] (V : ValuationSubring C)
    (z₁ z₂ : Spec (CommRingCat.of V) ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (h₁ : centre z₁ ∈ U) (h₂ : centre z₂ ∈ U)
    (e : Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z₁ =
      Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z₂) : z₁ = z₂ := by
  obtain ⟨φ₁, e₁⟩ : ∃ φ, Spec.map φ ≫ hU.fromSpec = z₁ := ⟨_, spec_germ_fromSpec z₁ hU h₁⟩
  obtain ⟨φ₂, e₂⟩ : ∃ φ, Spec.map φ ≫ hU.fromSpec = z₂ := ⟨_, spec_germ_fromSpec z₂ hU h₂⟩
  subst e₁ e₂
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  have e' := Spec.map_injective e
  have : φ₁ = φ₂ := by
    ext g
    exact congrArg (fun m => m.hom g) e'
  rw [this]

end CoordExtend

open CoordExtend in

theorem coord_point_extends : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (κ : Type) [Finite κ] (x : κ → Ω), CoordTie ℤ ξ x →
    ∀ (C : Type) [Field C] (V : ValuationSubring C) (zC : Spec (CommRingCat.of C) ⟶ X),
    genPt ξ ⤳ centre zC →
    ∃! z : Spec (CommRingCat.of V) ⟶ X, genPt ξ ⤳ centre z ∧
      Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z = zC := by
  intro X Ω _ ξ κ _ x hT C _ V zC h
  obtain ⟨c, hg⟩ := exists_goodChart hT V zC h
  obtain ⟨z, hz, hzC, hch⟩ := exists_of_goodChart hT V zC h hg
  refine ⟨z, ⟨hz, hzC⟩, ?_⟩
  rintro y ⟨hy, hyC⟩
  obtain ⟨U, hU, hmem⟩ := hT.affine c hg.1
  have hych : InChart ξ x c ⟨centre y, hy⟩ := by
    subst hyC
    exact inChart_of_goodChart hT V y hy h hg
  exact eq_of_mem_affine V y z hU ((hmem _).2 ⟨hy, hych⟩) ((hmem _).2 ⟨hz, hch⟩) (hyC.trans hzC.symm)

end GlobalTheory.CompanionTheory.Ar
