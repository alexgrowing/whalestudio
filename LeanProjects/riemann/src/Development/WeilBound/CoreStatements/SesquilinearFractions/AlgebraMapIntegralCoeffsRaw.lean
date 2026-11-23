import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsCommonDenominatorCoeffs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem algebraMap_bar_eq_conj (a : 𝓞 E) :
    algebraMap (𝓞 E) E (H.bar a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) := H.bar_eq a

def familyCombination (D : Datum H) {p : ℕ} (x' : Fin p → D.La) : (Fin p → 𝓞 E) →ₗ[𝓞 E] D.La where
  toFun c := ∑ a, c a • x' a
  map_add' c c' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_smul]

section Maps

variable (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (m : ℕ)
  (hm : ∀ y a, ∃ g : 𝓞 E, (g : E) = m * projectionCoeffs D x' y a)

def integralCoeffsRaw (y : D.La) (a : Fin p) : 𝓞 E := Classical.choose (hm y a)

theorem algebraMap_integralCoeffsRaw (y : D.La) (a : Fin p) :
    algebraMap (𝓞 E) E (integralCoeffsRaw D x' m hm y a) = m * projectionCoeffs D x' y a := Classical.choose_spec (hm y a)

def integralCoeffs : D.La →ₗ[𝓞 E] (Fin p → 𝓞 E) where
  toFun y a := H.bar (integralCoeffsRaw D x' m hm y a)
  map_add' y y' := by
    funext a
    apply IsFractionRing.injective (𝓞 E) E
    simp only [Pi.add_apply]
    rw [map_add, algebraMap_bar_eq_conj, algebraMap_bar_eq_conj, algebraMap_bar_eq_conj, algebraMap_integralCoeffsRaw, algebraMap_integralCoeffsRaw, algebraMap_integralCoeffsRaw, projectionCoeffs_add,
      Pi.add_apply, mul_add, map_add]
  map_smul' c y := by
    funext a
    apply IsFractionRing.injective (𝓞 E) E
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [map_mul, algebraMap_bar_eq_conj, algebraMap_bar_eq_conj, algebraMap_integralCoeffsRaw, algebraMap_integralCoeffsRaw, projectionCoeffs_smul, Pi.smul_apply, smul_eq_mul,
      map_mul, map_mul, map_mul, IsCMField.complexConj_apply_apply, map_natCast]
    show _ = ((c : 𝓞 E) : E) * _
    ring

theorem conj_integralCoeffs (y : D.La) (a : Fin p) :
    IsCMField.complexConj E (algebraMap (𝓞 E) E (integralCoeffs D x' m hm y a)) = m * projectionCoeffs D x' y a := by
  show IsCMField.complexConj E (algebraMap (𝓞 E) E (H.bar (integralCoeffsRaw D x' m hm y a))) = _
  rw [algebraMap_bar_eq_conj, IsCMField.complexConj_apply_apply, algebraMap_integralCoeffsRaw]

def orthogonalComponent : D.La →ₗ[𝓞 E] D.La := (m : 𝓞 E) • LinearMap.id - familyCombination D x' ∘ₗ integralCoeffs D x' m hm

theorem orthogonalComponent_mem (hdet : (gramE D x').det ≠ 0) (y : D.La) : orthogonalComponent D x' m hm y ∈ orthogonalFamilyAlt D x' := by
  show ∀ a, sesq D (x' a) (orthogonalComponent D x' m hm y) = 0
  intro b
  have hsub : ∀ u v w : D.La, sesq D u (v - w) = sesq D u v - sesq D u w := by
    intro u v w
    simp only [sesq, map_sub, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  have hsm : ∀ u v : D.La, sesq D u ((m : 𝓞 E) • v) = m * sesq D u v := by
    intro u v
    rw [Nat.cast_smul_eq_nsmul]
    simp only [sesq, map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Finset.mul_sum,
      _root_.mul_assoc]
  have hcomb : familyCombination D x' (integralCoeffs D x' m hm y) =
      ∑ a, integralCoeffs D x' m hm y a • x' a := rfl
  have hG := congrFun (gram_mulVec_projection_coeffs D x' hdet y) b
  simp only [Matrix.mulVec, dotProduct, pairingVector] at hG
  have hd : ∀ a, IsCMField.complexConj E ((integralCoeffs D x' m hm y a : 𝓞 E) : E) =
      m * projectionCoeffs D x' y a := fun a => conj_integralCoeffs D x' m hm y a
  simp only [orthogonalComponent, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.comp_apply]
  rw [hsub, hsm, hcomb, sesq_integral_combination]
  simp only [hd]
  rw [← hG, Finset.mul_sum]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro a _
  ring

end Maps

end GlobalTheory.CompanionTheory.Ar.Fl

end
