import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutAppLEOfIsPullbackOfIsAffine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.NilThicken

theorem ker_inl_le_map_ker_of_isPushout {A B C D : CommRingCat.{0}} {a : A ⟶ B} {c : A ⟶ C}
    {b : B ⟶ D} {d : C ⟶ D} (h : IsPushout a c b d) (hc : Function.Surjective c.hom) :
    RingHom.ker b.hom ≤ Ideal.map a.hom (RingHom.ker c.hom) := by
  set J : Ideal B := Ideal.map a.hom (RingHom.ker c.hom)
  let π : B ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let e := RingHom.quotientKerEquivOfSurjective hc
  let σ : C ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom
    ((Ideal.quotientMap J a.hom (Ideal.le_comap_map)).comp e.symm.toRingHom)
  have w : a ≫ π = c ≫ σ := by
    ext x
    have hx : e.symm (c.hom x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp [π, σ, hx]
  intro x hx
  have h1 : (b ≫ h.desc π σ w).hom x = π.hom x := by rw [h.inl_desc]
  rw [CommRingCat.comp_apply, (RingHom.mem_ker).mp hx, map_zero] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm

theorem isNilpotent_ker_app :
    ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁)
      (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) →
      Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → ∀ U : Y₁.Opens, IsAffineOpen U →
      IsNilpotent (RingHom.ker (i.app U).hom) := by
  intro R₁ R₀ g Y₁ Y₀ p₁ p₀ i hpb hg hnil U hU
  have P := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y₁ Y₀ (Spec R₁) (Spec R₀)
    i p₀ p₁ (Spec.map g) hpb inferInstance inferInstance U hU
  have hnat := Scheme.ΓSpecIso_naturality g
  set c := (Spec.map g).appTop
  have hcker : RingHom.ker c.hom = Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom) := by
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    have := congrArg (fun φ => φ.hom x) hnat
    simp only [CommRingCat.comp_apply] at this
    rw [← this]
    constructor
    · intro h0; rw [h0, map_zero]
    · intro h0
      have hinj := ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom)).1
      exact hinj (by rw [h0, map_zero])
  have hcs : Function.Surjective c.hom := by
    intro y
    obtain ⟨r, hr⟩ := hg ((Scheme.ΓSpecIso R₀).hom y)
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).2 r
    refine ⟨x, ?_⟩
    have := congrArg (fun φ => φ.hom x) hnat
    simp only [CommRingCat.comp_apply] at this
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom).1
    rw [this, hx, hr]
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have hle := ker_inl_le_map_ker_of_isPushout P hcs
  have hJ : (Ideal.map (p₁.appLE ⊤ U (fun _ _ => trivial)).hom (RingHom.ker c.hom)) ^ n = ⊥ := by
    rw [← Ideal.map_pow, hcker]
    have h2 : (Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom)) ^ n = ⊥ := by
      apply le_bot_iff.mp
      refine (Ideal.le_comap_pow _ n).trans ?_
      rw [show RingHom.ker g.hom ^ n = ⊥ from hn]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [Ideal.mem_bot]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).1 (by rw [hx, map_zero])
    rw [h2, Ideal.map_bot]
  exact le_bot_iff.mp ((Ideal.pow_right_mono hle n).trans hJ.le)

end GlobalTheory.NilThicken
