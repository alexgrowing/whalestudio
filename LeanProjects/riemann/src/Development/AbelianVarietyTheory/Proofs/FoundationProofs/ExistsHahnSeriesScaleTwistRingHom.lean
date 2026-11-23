import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNTwist

noncomputable def twistMap {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : HahnSeries ℚ Ω' where
  coeff r := χ r * s (h.coeff r)
  isPWO_support' := h.isPWO_support.mono (by
    intro r hr
    simp only [Function.mem_support, ne_eq] at hr ⊢
    intro h0
    exact hr (by rw [h0, map_zero, mul_zero]))

lemma twistMap_coeff {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) (r : ℚ) : (twistMap s χ h).coeff r = χ r * s (h.coeff r) := rfl

lemma twistMap_support {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h : HahnSeries ℚ Ω) : (twistMap s χ h).support ⊆ h.support := by
  intro r hr
  simp only [HahnSeries.mem_support, twistMap_coeff, ne_eq] at hr ⊢
  intro h0
  exact hr (by rw [h0, map_zero, mul_zero])

noncomputable def twistHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (s : Ω →+* Ω') (χ : ℚ → Ω')
    (h0 : χ 0 = 1) (hadd : ∀ r r', χ (r + r') = χ r * χ r') :
    HahnSeries ℚ Ω →+* HahnSeries ℚ Ω' where
  toFun := twistMap s χ
  map_one' := by
    ext r
    rw [twistMap_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs with hr
    · subst hr; simp [h0]
    · simp
  map_zero' := by
    ext r
    simp [twistMap_coeff]
  map_add' x y := by
    ext r
    simp [twistMap_coeff, mul_add]
  map_mul' x y := by
    ext a
    show (twistMap s χ (x * y)).coeff a = (twistMap s χ x * twistMap s χ y).coeff a
    rw [twistMap_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
    have hsub : Finset.antidiagonal (twistMap s χ x).isPWO_support (twistMap s χ y).isPWO_support a ⊆
        Finset.antidiagonal x.isPWO_support y.isPWO_support a :=
      fun ij hij => (Finset.antidiagonal_mono_right (twistMap_support s χ y))
        ((Finset.antidiagonal_mono_left (twistMap_support s χ x)) hij)
    rw [Finset.sum_subset hsub (fun ij hbig hij => ?_)]
    · refine Finset.sum_congr rfl (fun ij hij => ?_)
      have hsum : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hij).2.2
      rw [twistMap_coeff, twistMap_coeff, map_mul, ← hsum, hadd]
      ring
    · have hs : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hbig).2.2
      by_cases h1 : (twistMap s χ x).coeff ij.1 = 0
      · rw [h1, zero_mul]
      · by_cases h2 : (twistMap s χ y).coeff ij.2 = 0
        · rw [h2, mul_zero]
        · exact absurd (Finset.mem_antidiagonal.mpr ⟨h1, h2, hs⟩) hij

end GlobalTheory.FNTwist

theorem GlobalTheory.FNTwist.exists_scale_twist_ringHom : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (s : Ω →+* Ω') (l : ℚ) (χ : ℚ → Ω'), 0 < l → χ 0 = 1 → (∀ r r', χ (r + r') = χ r * χ r') → ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω', ∀ h r, (Φ h).coeff (r * l) = χ r * s (h.coeff r) := by
  intro Ω Ω' _ _ s l χ hl h0 hadd
  have hinj : Function.Injective (AddMonoidHom.mulRight l) := by
    intro a b hab
    simpa [AddMonoidHom.coe_mulRight, hl.ne'] using hab
  have hmono : ∀ g g' : ℚ, AddMonoidHom.mulRight l g ≤ AddMonoidHom.mulRight l g' ↔ g ≤ g' := by
    intro g g'
    simp only [AddMonoidHom.coe_mulRight]
    exact mul_le_mul_iff_of_pos_right hl
  refine ⟨(HahnSeries.embDomainRingHom (AddMonoidHom.mulRight l) hinj hmono).comp
    (GlobalTheory.FNTwist.twistHom s χ h0 hadd), fun h r => ?_⟩
  rw [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
  have := HahnSeries.embDomain_coeff (f := ⟨⟨AddMonoidHom.mulRight l, hinj⟩, hmono _ _⟩)
    (x := GlobalTheory.FNTwist.twistHom s χ h0 hadd h) (a := r)
  rw [show χ r * s (h.coeff r) = (GlobalTheory.FNTwist.twistHom s χ h0 hadd h).coeff r from rfl]
  simpa using this
