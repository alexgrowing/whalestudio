import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulUnramified

lemma eq_one_of_pow_eq_one_thick_affine (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (G : Over (Sp C)) [GrpObj G] (n : ℕ)
    (hn : IsUnit (n : C)) (R : CommRingCat.{0}) (g : Spec R ⟶ Sp C) (z : Over.mk g ⟶ G)
    (hz : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g), j ≫ z = 1)
    (hzn : z ^ n = 1) : z = 1 := by
  let φ : CommRingCat.of C ⟶ R := Spec.preimage g
  let K : Ideal C := RingHom.ker π
  let J : Ideal R := Ideal.map φ.hom K
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* R ⧸ J :=
    (Ideal.quotientMap J φ.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ∀ c, ψ (π c) = q (φ c) := by
    intro c
    have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk K c := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
    rfl
  have hJ : RingHom.ker q = J := Ideal.mk_ker
  have hJsq : J ^ 2 = ⊥ := by
    simp only [J, ← Ideal.map_pow]
    change Ideal.map φ.hom (RingHom.ker π ^ 2) = ⊥
    rw [hsq, Ideal.zero_eq_bot, Ideal.map_bot]
  let T₀ : Over (Sp C₀) := Over.mk (spMap ψ)
  have hw : Spec.map (CommRingCat.ofHom q) ≫ g = T₀.hom ≫ spMap π := by
    rw [← Spec.map_preimage g]
    simp only [T₀, spMap, Over.mk_hom, ← Spec.map_comp]
    congr 1
    ext c
    exact (hψ c).symm
  let j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g := Over.homMk (Spec.map (CommRingCat.ofHom q)) hw
  have hsurj : Function.Surjective j.left := by
    intro (p : PrimeSpectrum R)
    change p ∈ Set.range (PrimeSpectrum.comap q)
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 ∈ RingHom.ker q ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hJ, hJsq, Ideal.mem_bot] at this
    rw [this]
    exact zero_mem _
  have hker : RingHom.ker (CommRingCat.ofHom q).hom ^ 2 = ⊥ := by
    change RingHom.ker q ^ 2 = ⊥
    rw [hJ, hJsq]
  have hn' : IsUnit (n : Γ(Sp C, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  exact eq_one_of_pow_eq_one G j hsurj (mul_eq_zero_of_ker_sq (CommRingCat.ofHom q) hker) n hn' z
    (hz T₀ j) hzn

end GlobalTheory.MulUnramified

namespace GlobalTheory.MulUnramified

theorem eq_one_of_pow_eq_one_thick : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  intro C C₀ _ _ π hπ hsq G _ n hn T z hz hzn
  apply Over.OverMorphism.ext
  refine T.left.affineOpenCover.openCover.hom_ext _ _ fun i ↦ ?_
  let k : T.left.affineOpenCover.I₀ := i
  let f : Over.mk (T.left.affineOpenCover.f k ≫ T.hom) ⟶ T := Over.homMk (T.left.affineOpenCover.f k) rfl
  have hfz : (f ≫ z) ^ n = 1 := by
    rw [← MonObj.comp_pow, hzn, comp_one]
  have h := eq_one_of_pow_eq_one_thick_affine C C₀ π hπ hsq G n hn _ _ (f ≫ z)
    (fun T₀ j ↦ by rw [← Category.assoc]; exact hz T₀ _) hfz
  have h' := congrArg (·.left) (h.trans (comp_one f).symm)
  simp only [Over.comp_left] at h'
  exact h'

end GlobalTheory.MulUnramified
