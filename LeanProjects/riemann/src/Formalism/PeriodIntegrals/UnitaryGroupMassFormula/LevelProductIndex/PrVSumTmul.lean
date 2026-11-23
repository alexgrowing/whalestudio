import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.Development

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct

noncomputable section

namespace PI.LPI

open Formalism.UG

theorem exists_gen {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Lb) :
    ∃ (k : ℕ) (m : Fin k → Fin n → E), (∀ i, m i ∈ Lb) ∧
      (∀ l ∈ Lb, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) := by
  have : Module.Finite ℤ Lb := Module.Finite.trans (𝓞 E) Lb
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Lb)
  refine ⟨k, fun i => (s i : Fin n → E), fun i => (s i).2, fun l hl => ?_⟩
  have hmem : (⟨l, hl⟩ : Lb) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
  refine ⟨z, ?_⟩
  have h2 := congrArg Subtype.val hz
  simp only [Submodule.coe_sum] at h2
  exact h2.symm

theorem prV_tmul {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (e ⊗ₜ[F] a) = e ⊗ₜ[F] a v := by
  simp [prV, evalV, Algebra.TensorProduct.map_tmul]
  rfl

theorem prV_sum_tmul {F E : Type} [Field F] [NumberField F] [CommRing E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (e : Fin k → E) (a : Fin k → FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (∑ i, e i ⊗ₜ[F] a i) = ∑ i, e i ⊗ₜ[F] a i v := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => prV_tmul v (e i) (a i)

def adOf {F : Type} [Field F] [NumberField F] (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  (⟨a, Filter.Eventually.of_forall ha⟩ :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

theorem adOf_apply {F : Type} [Field F] [NumberField F]
    (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    adOf a ha v = a v := rfl

theorem adOf_mem {F : Type} [Field F] [NumberField F]
    (a : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) : adOf a ha ∈ intAd F := fun v => ha v

theorem plUp_of (hG : PLGen) (hI : PLInj) : PLUp := by
  intro F E _ _ _ _ _ n Lb hfin y hy
  obtain ⟨k, m, hm, hgen⟩ := exists_gen Lb hfin
  have hloc := fun v : HeightOneSpectrum (𝓞 F) =>
    (hG F E (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring n k Lb m hm hgen
      (fun j => prV (E := E) v (y j))).1 (hy v)
  choose a ha hya using hloc
  let A : Fin k → FiniteAdeleRing (𝓞 F) F := fun i => adOf (fun v => a v i) (fun v => ha v i)
  have hyA : (fun j => ∑ i, m i j ⊗ₜ[F] A i) ∈ latA F Lb :=
    (hG F E (FiniteAdeleRing (𝓞 F) F) (intAd F) n k Lb m hm hgen _).2
      ⟨A, fun i => adOf_mem _ _, rfl⟩
  have hyy : y = fun j => ∑ i, m i j ⊗ₜ[F] A i := by
    funext j
    refine sub_eq_zero.1 (hI F E _ fun v => ?_)
    rw [map_sub, sub_eq_zero, prV_sum_tmul]
    exact congrFun (hya v) j
  rw [hyy]
  exact hyA

end PI.LPI
