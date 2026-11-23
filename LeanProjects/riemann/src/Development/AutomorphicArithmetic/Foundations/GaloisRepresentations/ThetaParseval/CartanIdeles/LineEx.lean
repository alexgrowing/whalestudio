import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf

noncomputable section

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GroundTheory.Global GroundTheory.Global.IdeleGroup

open UpperTheory.Gal.TP.Skew

private theorem ordE_mul {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a b : E}
    (ha : a ≠ 0) (hb : b ≠ 0) : ordE w (a * b) = ordE w a + ordE w b := by
  unfold ordE
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul E w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb)]

theorem UpperTheory.Gal.TP.Skew.lineEx :
    UpperTheory.Gal.TP.Skew.OrdAut → UpperTheory.Gal.TP.Skew.OrdLine → UpperTheory.Gal.TP.Skew.MemOrd → UpperTheory.Gal.TP.Skew.MemDual → UpperTheory.Gal.TP.Skew.LineEx := by
  intro hA hL hM hD F E _ _ _ _ _ σ hc hu
  obtain ⟨s, δ, I, hs, hss, hδ, hsk, hI, hid⟩ := hL F E σ hc hu
  have hD0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  obtain ⟨m1, m2, m3⟩ := hM E I hI
  obtain ⟨d1, -, -⟩ := hM E _ hD0
  have hss' : ∀ w : HeightOneSpectrum (𝓞 E), s • s • w = w := fun w => by
    rw [smul_smul, hss, one_smul]
  have ordS : ∀ (w : HeightOneSpectrum (𝓞 E)) (x : E), ordE w (σ x) = ordE (s • w) x := fun w x => by
    have h := (hA F E s (s • w)).1 x
    rw [hss', hs] at h
    exact h
  have hσ0 : ∀ x : E, x ≠ 0 → σ x ≠ 0 := fun x hx h =>
    hx (by simpa using (map_eq_zero_iff σ σ.toRingHom.injective).mp h)
  have key : ∀ (w : HeightOneSpectrum (𝓞 E)) (y x : E), y ≠ 0 → x ≠ 0 →
      ordE w (y * (δ * σ x)) = ordE w y + ordE w δ + ordE (s • w) x := fun w y x hy hx => by
    rw [ordE_mul w hy (mul_ne_zero hδ (hσ0 x hx)), ordE_mul w hδ (hσ0 x hx), ordS]
    ring
  have hdual : ∀ y : E, (∀ x ∈ I, y * (δ * σ x) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔
      ∀ x ∈ (I : Submodule (𝓞 E) E), ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * (y * (δ * σ x)))) :=
    fun y => forall₂_congr fun x _ => hD E _
  refine ⟨δ, (I : Submodule (𝓞 E) E), hδ, hsk, m3, fun y => ?_⟩
  rw [FractionalIdeal.mem_coe, ← hdual y]
  constructor
  · intro hy x hx
    by_cases hy0 : y = 0
    · simpa [hy0] using FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    by_cases hx0 : x = 0
    · simpa [hx0] using FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    refine (d1 _ (mul_ne_zero hy0 (mul_ne_zero hδ (hσ0 x hx0)))).mpr fun w => ?_
    have h1 := (m1 y hy0).mp hy w
    have h2 := (m1 x hx0).mp hx (s • w)
    have h3 := hid w
    rw [key w y x hy0 hx0]
    omega
  · intro h
    by_cases hy0 : y = 0
    · simpa [hy0] using FractionalIdeal.mem_coe.mp (Submodule.zero_mem _)
    refine (m1 y hy0).mpr fun w => ?_
    obtain ⟨x, hx, hx0, hxo⟩ := m2 (s • w)
    have h1 := (d1 _ (mul_ne_zero hy0 (mul_ne_zero hδ (hσ0 x hx0)))).mp (h x hx) w
    have h3 := hid w
    rw [key w y x hy0 hx0] at h1
    omega

end
