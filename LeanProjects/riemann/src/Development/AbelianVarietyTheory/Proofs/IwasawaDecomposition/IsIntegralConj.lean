import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral

open NumberField

namespace GlobalTheory.HermDen

open ReciprocityTheory.ChartRestriction.G.FD

theorem isIntegral_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {x : E}
    (hx : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  hx.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom

theorem exists_den (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ Λ, ∀ y ∈ Λ,
      IsIntegral ℤ ((den : E) * ReciprocityTheory.ChartRestriction.G.FD.herm G x y) := by
  classical
  obtain ⟨k, hk, hi⟩ := GlobalTheory.LatFin.exists_common_den Λ hΛ
  obtain ⟨l, hl, hG⟩ := GlobalTheory.LatFin.exists_common_den
    (Submodule.span (𝓞 E) (Set.range fun a : Fin r => (G a : Fin r → E)))
    (Submodule.fg_span (Set.finite_range _))
  have hG' : ∀ a b, IsIntegral ℤ ((l : E) * G a b) := fun a b =>
    hG _ (Submodule.subset_span ⟨a, rfl⟩) b
  refine ⟨((k * k * l : ℤ) : 𝓞 E), Int.cast_ne_zero.2 (mul_ne_zero (mul_ne_zero hk hk) hl),
    fun x hx y hy => ?_⟩
  have e : ((((k * k * l : ℤ) : 𝓞 E)) : E) * herm G x y
      = ∑ a, ∑ b, ((k : E) * x a) * ((l : E) * G a b) * cc ((k : E) * y b) := by
    have h1 : ((((k * k * l : ℤ) : 𝓞 E)) : E) = (k : E) * k * l := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_intCast]
      push_cast
      ring
    rw [h1, herm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h2 : cc ((k : E) * y b) = k * cc (y b) := by simp [cc]
    rw [h2]
    ring
  rw [e]
  exact IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ =>
    ((hi x hx a).mul (hG' a b)).mul (isIntegral_conj (hi y hy b))

end GlobalTheory.HermDen
