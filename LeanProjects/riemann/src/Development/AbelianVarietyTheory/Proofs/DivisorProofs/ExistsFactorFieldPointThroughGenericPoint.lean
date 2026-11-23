import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.factor_gp (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (L : Type) [Field L] (ρ : R →+* L)
    (y : Sp L ⟶ M.S) (hρ : Function.Injective ρ) (hy : y ≫ M.π = spMap ρ) :
    ∃ ga : FractionRing R →+* L, (∀ r, ga (algebraMap R _ r) = ρ r) ∧ y = spMap ga ≫ M.gp := by
  have hI := M.integral
  have hdom := M.dominant
  have hsub : ∀ (K : Type) [Field K] (a b : Sp K), a = b := fun K _ a b =>
    PrimeSpectrum.ext (by haveI := a.isPrime; haveI := b.isPrime; rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])
  let p : Sp L := IsLocalRing.closedPoint L
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y p) (U := ⊤) trivial
  have hyV : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]; rintro _ ⟨z, rfl⟩; rw [hsub L z p]; exact hxV
  obtain ⟨q, hq⟩ := M.gp.denseRange.exists_mem_open V.isOpen ⟨y p, hxV⟩
  have hgV : Set.range M.gp ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]; rintro _ ⟨z, rfl⟩; rw [hsub (FractionRing R) z q]; exact hq
  haveI : Nonempty V := ⟨⟨y p, hxV⟩⟩
  haveI : IsDomain Γ(M.S, V) := IsIntegral.component_integral V
  set yV := IsOpenImmersion.lift hV.fromSpec y hyV with hyVdef
  set gV := IsOpenImmersion.lift hV.fromSpec M.gp hgV with hgVdef
  have hyf : yV ≫ hV.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
  have hgf : gV ≫ hV.fromSpec = M.gp := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨by', hby⟩ := Spec.map_surjective yV
  obtain ⟨bg, hbg⟩ := Spec.map_surjective gV
  obtain ⟨c, hc⟩ := Spec.map_surjective (hV.fromSpec ≫ M.π)
  have hcy : by'.hom.comp c.hom = ρ := by
    have e : Spec.map (c ≫ by') = Spec.map (CommRingCat.ofHom ρ) := by
      rw [Spec.map_comp, hby, hc, ← Category.assoc, hyf, hy]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hcg : bg.hom.comp c.hom = algebraMap R (FractionRing R) := by
    have e : Spec.map (c ≫ bg) = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
      rw [Spec.map_comp, hbg, hc, ← Category.assoc, hgf, M.gp_π]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hdV : IsDominant gV := by
    haveI : IsDominant (gV ≫ hV.fromSpec) := by rw [hgf]; exact hdom
    exact IsDominant.of_comp_of_isOpenImmersion gV hV.fromSpec
  have hinj : Function.Injective bg.hom := by
    rw [← hbg] at hdV
    have h := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical bg.hom).1 hdV.denseRange
    rw [nilradical_eq_zero] at h
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h)
  let ga : FractionRing R →+* L := IsFractionRing.lift hρ
  have hga : ∀ r, ga (algebraMap R _ r) = ρ r := IsFractionRing.lift_algebraMap hρ
  have key : ∀ b, by'.hom b = ga (bg.hom b) := by
    intro b
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) (bg.hom b)
    have hs0 : ρ s ≠ 0 := (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero s.2)
    have hcs : bg.hom (c.hom s) = algebraMap R (FractionRing R) s := RingHom.congr_fun hcg s
    have hcr : bg.hom (c.hom r) = algebraMap R (FractionRing R) r := RingHom.congr_fun hcg r
    have h1 : c.hom s * b = c.hom r := hinj (by
      rw [map_mul, hcs, hcr, ← hrs]; exact IsLocalization.mk'_spec' (FractionRing R) r s)
    have h2 := congrArg by'.hom h1
    have hys : by'.hom (c.hom s) = ρ s := RingHom.congr_fun hcy s
    have hyr : by'.hom (c.hom r) = ρ r := RingHom.congr_fun hcy r
    rw [map_mul, hys, hyr] at h2
    rw [← hrs, IsFractionRing.lift_mk', eq_div_iff hs0, mul_comm]
    exact h2
  refine ⟨ga, hga, ?_⟩
  have e : by' = bg ≫ CommRingCat.ofHom ga := by ext b; exact key b
  rw [← hyf, ← hby, e, Spec.map_comp, Category.assoc, hbg, hgf]

end GlobalTheory.Mum
