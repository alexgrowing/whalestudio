import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.AdeleBaseChange

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV Formalism.UG Formalism.UG.P

theorem exists_tensor_finiteAdele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ ι : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E, (∀ x : E, ι (1 ⊗ₜ[F] x) = algebraMap E _ x) ∧ (∀ y, y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v (ι y P) ≤ 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (α : FiniteAdeleRing (𝓞 F) F), α v = 1 → (∀ v', v' ≠ v → α v' = 0) → ∀ P : HeightOneSpectrum (𝓞 E), ι (α ⊗ₜ[F] 1) P = if P.under (𝓞 F) = v then 1 else 0 := by
  intro F E _ _ _ _ _
  obtain ⟨ι, hι⟩ := exists_toAd F E
  let c : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* AfE F E :=
    (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toRingEquiv
  have hc : ∀ a x, c (a ⊗ₜ[F] x) = x ⊗ₜ[F] a := fun a x => rfl
  have hc' : ∀ a x, c.symm (x ⊗ₜ[F] a) = a ⊗ₜ[F] x := fun a x => rfl
  let j := c.trans (RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩)
  have hj : ∀ y, j y = ι (c y) := fun y => rfl
  refine ⟨j, fun x => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, fun v α h1 h0 P => ?_⟩
  · rw [hj, hc, map_tmul_one hι]
  · have : j y ∈ intAd E := by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, x, rfl⟩ := hy
        rw [hj, hc]
        exact map_mem_int hι (levelaf_tmul_mem x ha)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact neg_mem hx
    exact this
  · have h : c y ∈ RInt F E := mem_int_of_map hι hy
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := levelaf_decomp g hg h
    have e' : y = c.symm (c y) := (c.symm_apply_apply y).symm
    rw [e', e, map_sum]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨r i, hr i, g i, ?_⟩
    rw [hc']
  · rw [hj, hc, hι, map_one, one_mul, adMap_apply]
    split_ifs with h
    · subst h
      rw [h1, map_one]
    · rw [h0 _ h, map_zero]

end GlobalTheory.AdeleBaseChange
