import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.IntLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_int_generators (E : Type) [Field E] [NumberField E] :
    ∃ (k : ℕ) (x : Fin k → 𝓞 E), ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  refine ⟨k, s, fun w => ?_⟩
  have : w ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  exact ⟨n, hn.symm⟩

omit [NumberField E] in

theorem mem_addClosure_of_mem_ordAt (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E)
    (hy : y ∈ ordAt E v) :
    y ∈ AddSubgroup.closure
      {y : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  have h := Subring.mem_closure_iff.1 hy
  refine AddSubgroup.closure_mono ?_ h
  intro z hz
  induction hz using Submonoid.closure_induction with
  | mem z hz => exact hz
  | one => exact ⟨1, one_mem _, 1, rfl⟩
  | mul z w _ _ hz hw =>
    obtain ⟨a, ha, x, rfl⟩ := hz
    obtain ⟨b, hb, x', rfl⟩ := hw
    exact ⟨a * b, mul_mem ha hb, x * x', by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl⟩

omit [NumberField E] in

theorem exists_coeff {k : ℕ} (x : Fin k → 𝓞 E)
    (hx : ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j) (v : HeightOneSpectrum (𝓞 F))
    (y : Fv F v ⊗[F] E) (hy : y ∈ ordAt E v) :
    ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧
      y = ∑ j, a j ⊗ₜ[F] (x j : E) := by
  have hy' := mem_addClosure_of_mem_ordAt v y hy
  clear hy
  induction hy' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, w, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hx w
    refine ⟨fun j => n j • a, fun j => zsmul_mem ha _, ?_⟩
    show a ⊗ₜ[F] (algebraMap (𝓞 E) E (∑ j, n j • x j)) =
      ∑ j, (n j • a) ⊗ₜ[F] (algebraMap (𝓞 E) E (x j))
    simp only [map_sum, map_zsmul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul]
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, ea⟩ := hy
    obtain ⟨b, hb, eb⟩ := hz
    exact ⟨a + b, fun j => add_mem (ha j) (hb j), by
      simp only [Pi.add_apply, ea, eb, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  | neg y _ hy =>
    obtain ⟨a, ha, ea⟩ := hy
    exact ⟨-a, fun j => neg_mem (ha j), by
      simp only [Pi.neg_apply, ea, TensorProduct.neg_tmul, Finset.sum_neg_distrib]⟩

theorem mem_intA_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (z : Af F ⊗[F] E),
      z ∈ intA F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), evF E v z ∈ ordAt E v := by
  intro F E _ _ _ _ _ z
  constructor
  · intro hz v
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      exact Subring.subset_closure ⟨_, ha v, x, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  · intro h
    obtain ⟨k, x, hx⟩ := exists_int_generators E
    choose a ha ea using fun v => exists_coeff x hx v _ (h v)
    let A : Fin k → Af F := fun j =>
      ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    have e : z = ∑ j, A j ⊗ₜ[F] (x j : E) := by
      apply evF_ext
      intro v
      rw [ea v, map_sum]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [e]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨A j, fun v => ha v j, x j, rfl⟩

end GlobalTheory.PlaceComp.IntLocal
