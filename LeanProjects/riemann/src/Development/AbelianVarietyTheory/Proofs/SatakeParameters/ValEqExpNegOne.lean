import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLocUnif

theorem val_eq_exp_neg_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (w : Valuation E (WithZero (Multiplicative ℤ)))
    (h1 : ∀ x : 𝓞 E, x ∉ P.asIdeal → w (algebraMap (𝓞 E) E x) = 1)
    (ϖ : 𝓞 E) (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2)
    (hlt : w (algebraMap (𝓞 E) E ϖ) < 1)
    (y : 𝓞 E) (hy : w (algebraMap (𝓞 E) E y) = WithZero.exp (-1 : ℤ)) :
    w (algebraMap (𝓞 E) E ϖ) = WithZero.exp (-1 : ℤ) := by
  have hu : ∀ u : E, P.valuation E u = 1 → w u = 1 := by
    intro u hu
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer u hu.le
    have hd : (d : 𝓞 E) ∉ P.asIdeal := d.2
    have hn : n ∉ P.asIdeal := by
      rw [← P.valuation_eq_one_iff_notMem (K := E), ← hnd, map_mul, hu,
        (P.valuation_eq_one_iff_notMem (K := E)).2 hd, one_mul]
    have := h1 n hn
    rwa [← hnd, map_mul, h1 _ hd, mul_one] at this
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hP2 (zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
    exact WithZero.exp_ne_zero hy.symm
  have hϖE : algebraMap (𝓞 E) E ϖ ≠ 0 := by
    simpa using hϖ0
  have hvϖ : P.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
    have a1 := (P.intValuation_lt_one_iff_mem ϖ).2 hP
    have a2 := (P.intValuation_le_pow_iff_mem ϖ 2).not.2 hP2
    rw [P.intValuation_eq_exp_neg_multiplicity hϖ0] at a1 a2 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at a1
    rw [WithZero.exp_le_exp] at a2
    congr 1
    push_cast at a2
    omega
  set m : ℕ := multiplicity P.asIdeal (Ideal.span {y}) with hm
  have hvy : P.intValuation y = WithZero.exp (-(m : ℤ)) :=
    P.intValuation_eq_exp_neg_multiplicity hy0
  have e1 : P.valuation E (algebraMap (𝓞 E) E y) = WithZero.exp (-(m : ℤ)) :=
    (P.valuation_of_algebraMap (K := E) y).trans hvy
  have e2 : P.valuation E (algebraMap (𝓞 E) E ϖ) = WithZero.exp (-1 : ℤ) :=
    (P.valuation_of_algebraMap (K := E) ϖ).trans hvϖ
  have hq := hu (algebraMap (𝓞 E) E y / algebraMap (𝓞 E) E ϖ ^ m) (by
    rw [map_div₀, map_pow, e1, e2, ← WithZero.exp_nsmul, ← WithZero.exp_sub, ← WithZero.exp_zero]
    congr 1
    simp)
  have hw0 : w (algebraMap (𝓞 E) E ϖ) ≠ 0 := (Valuation.ne_zero_iff w).2 hϖE
  rw [map_div₀, map_pow, hy] at hq
  rw [← WithZero.exp_log hw0] at hq hlt ⊢
  set j := WithZero.log (w (algebraMap (𝓞 E) E ϖ))
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [← WithZero.exp_nsmul, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_inj] at hq
  congr 1
  simp only [nsmul_eq_mul] at hq
  have : (-j) * (m : ℤ) = 1 := by linarith
  have := Int.eq_one_of_mul_eq_one_right (by omega) this
  omega

theorem isUnifV_of_centre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* v.adicCompletion F), (∀ x : F, φ (algebraMap F E x) = algebraMap F (v.adicCompletion F) x) → (∀ x : 𝓞 E, φ (x : E) ∈ Formalism.UG.Ov F v) → (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ φ ((x : E)⁻¹) ∉ Formalism.UG.Ov F v)) → ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → Formalism.UG.IsUnifV F v (φ (ϖ : E)) := by
  intro F E _ _ _ _ _ v P φ hF hO hc ϖ hP hP2
  let w : Valuation E (WithZero (Multiplicative ℤ)) := (Valued.v).comap φ
  have hw : ∀ x : E, w x = Valued.v (φ x) := fun _ => rfl
  have hmem : ∀ x : E, φ x ∈ Formalism.UG.Ov F v ↔ w x ≤ 1 := fun _ => Iff.rfl
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hP2 (zero_mem _)
  obtain ⟨y, hy⟩ := v.intValuation_exists_uniformizer
  refine val_eq_exp_neg_one P w ?_ ϖ hP hP2 ?_ (algebraMap (𝓞 F) (𝓞 E) y) ?_
  · intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (zero_mem _)
    have hxE : algebraMap (𝓞 E) E x ≠ 0 := by simpa using hx0
    have a1 : w (algebraMap (𝓞 E) E x) ≤ 1 := (hmem _).1 (hO x)
    have a2 : w ((algebraMap (𝓞 E) E x)⁻¹) ≤ 1 := (hmem _).1 (not_not.1 ((hc x hx0).not.1 hx))
    rw [map_inv₀] at a2
    have hw0 : w (algebraMap (𝓞 E) E x) ≠ 0 := (Valuation.ne_zero_iff w).2 hxE
    exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 hw0)).1 a2)
  · have hxE : algebraMap (𝓞 E) E ϖ ≠ 0 := by simpa using hϖ0
    have a2 : ¬ w ((algebraMap (𝓞 E) E ϖ)⁻¹) ≤ 1 := (hmem _).not.1 ((hc ϖ hϖ0).1 hP)
    rw [map_inv₀, not_le] at a2
    have hw0 : w (algebraMap (𝓞 E) E ϖ) ≠ 0 := (Valuation.ne_zero_iff w).2 hxE
    exact (one_lt_inv₀ (zero_lt_iff.2 hw0)).1 a2
  · have e : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) y)
        = algebraMap F E (algebraMap (𝓞 F) F y) := by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [e, hw, hF, ← hy, ← v.valuation_of_algebraMap (K := F)]
    exact v.valuedAdicCompletion_eq_valuation' (algebraMap (𝓞 F) F y)

end GlobalTheory.SplitLocUnif
