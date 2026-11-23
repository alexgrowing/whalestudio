import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TensTopRing
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fdFE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

instance imt (v : HeightOneSpectrum (𝓞 F)) : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

theorem t2Space_scalarTensorExt (v : HeightOneSpectrum (𝓞 F)) : T2Space (Fv F v ⊗[F] E) := by
  have := fdFE (F := F) (E := E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  exact T2Space.of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem ratV_zero : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
  funext i; exact map_zero _

theorem ratV_add (x y : Fin n → E) :
    ratV (F := F) (Fv F v) (x + y) = ratV (F := F) (Fv F v) x + ratV (F := F) (Fv F v) y := by
  funext i; exact map_add _ _ _

theorem ratV_zsmul (m : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (m • x) = m • ratV (F := F) (Fv F v) x := by
  funext i; exact map_zsmul _ _ _

def mulE (e : E) : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
  LinearMap.pi fun i => (LinearMap.mulLeft (Fv F v) (inclR (F := F) (Fv F v) e)) ∘ₗ LinearMap.proj i

theorem mulE_apply (e : E) (w : Fin n → Fv F v ⊗[F] E) (i : Fin n) :
    mulE v e w i = inclR (F := F) (Fv F v) e * w i := rfl

theorem spanTop (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span (Fv F v) (ratV (F := F) (Fv F v) '' (L : Set (Fin n → E))) = ⊤ := by
  set W := Submodule.span (Fv F v) (ratV (F := F) (Fv F v) '' (L : Set (Fin n → E))) with hW
  have h1 : ∀ a : 𝓞 E, ∀ w ∈ W, mulE v (algebraMap (𝓞 E) E a) w ∈ W := by
    intro a w hw
    have : W.map (mulE v (algebraMap (𝓞 E) E a)) ≤ W := by
      rw [hW, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨a • x, L.smul_mem a hx, ?_⟩
      funext i
      show inclR (F := F) (Fv F v) ((a • x) i) = inclR (F := F) (Fv F v) (algebraMap (𝓞 E) E a) * inclR _ (x i)
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact this ⟨w, hw, rfl⟩
  have h2 : ∀ e : E, ∀ w ∈ W, mulE v e w ∈ W := by
    intro e w hw
    obtain ⟨y, hy0, hyi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := e) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic e))
    let a : 𝓞 E := IsIntegralClosure.mk' (𝓞 E) (y • e) hyi
    have ha : algebraMap (𝓞 E) E a = y • e := IsIntegralClosure.algebraMap_mk' _ _ _
    have hyF : ((y : Fv F v)) ≠ 0 := by
      rw [← map_intCast (algebraMap F (Fv F v))]
      exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hy0)
    have key : algebraMap (Fv F v) (Fv F v ⊗[F] E) ((y : Fv F v))⁻¹ * (y : Fv F v ⊗[F] E) = 1 := by
      rw [← map_intCast (algebraMap (Fv F v) (Fv F v ⊗[F] E)), ← map_mul, inv_mul_cancel₀ hyF, map_one]
    have : mulE v e w = ((y : Fv F v))⁻¹ • mulE v (algebraMap (𝓞 E) E a) w := by
      funext i
      rw [Pi.smul_apply, mulE_apply, mulE_apply, ha, zsmul_eq_mul, map_mul, map_intCast, Algebra.smul_def,
        ← mul_assoc, ← mul_assoc, key, one_mul]
    rw [this]; exact W.smul_mem _ (h1 a w hw)
  have h3 : ∀ x : Fin n → E, ratV (F := F) (Fv F v) x ∈ W := by
    intro x
    have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [ratV_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [ratV_add]; exact W.add_mem hx hy
    | smul e x _ hx =>
        have : ratV (F := F) (Fv F v) (e • x) = mulE v e (ratV (F := F) (Fv F v) x) := by
          funext i; exact map_mul _ _ _
        rw [this]; exact h2 e _ hx
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine W.sum_mem fun i _ => ?_
  generalize w i = t
  induction t using TensorProduct.induction_on with
  | zero => rw [Pi.single_zero]; exact W.zero_mem
  | tmul r e =>
      have : (Pi.single i (r ⊗ₜ[F] e) : Fin n → Fv F v ⊗[F] E) =
          r • ratV (F := F) (Fv F v) (Pi.single i e) := by
        funext j
        by_cases h : j = i
        · subst h
          simp [ratV, inclR, TensorProduct.smul_tmul']
        · simp [ratV, h]
      rw [this]; exact W.smul_mem r (h3 _)
  | add s t hs ht => rw [Pi.single_add]; exact W.add_mem hs ht

end MassDataIdxK
