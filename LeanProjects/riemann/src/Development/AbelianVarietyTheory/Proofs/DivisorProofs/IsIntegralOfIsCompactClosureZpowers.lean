import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.isIntegral_matrix_of_pow_bounded {O K : Type} [CommRing O] [IsNoetherianRing O]
    [Field K] [Algebra O K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ (k : ℕ) (i j : Fin n), ∃ b : O, algebraMap O K b = a * (g ^ k) i j) :
    IsIntegral O g := by
  classical
  let ψ : (Fin n → Fin n → O) →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun b => Matrix.of fun i j => algebraMap O K (b i j)
      map_add' := fun b c => by ext i j; simp
      map_smul' := fun c b => by ext i j; simp [Algebra.smul_def] }
  let φ : Matrix (Fin n) (Fin n) K →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun A => a • A
      map_add' := fun A B => smul_add a A B
      map_smul' := fun c A => smul_comm a c A }
  have hφ : Function.Injective φ := fun A B hAB => smul_right_injective _ ha hAB
  have hP : (LinearMap.range ψ).FG := by
    rw [LinearMap.range_eq_map]; exact Submodule.FG.map _ Module.Finite.fg_top
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  have hle : Submodule.map φ (Subalgebra.toSubmodule (Algebra.adjoin O {g})) ≤
      LinearMap.range ψ := by
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.map_span_le]
    rintro _ ⟨k, rfl⟩
    choose b hb using h k
    exact ⟨b, by ext i j; simp [ψ, φ, hb]⟩
  exact IsIntegral.of_mem_of_fg _ (Submodule.fg_of_fg_map_injective φ hφ
    (Submodule.FG.of_le_of_isNoetherian hle)) g (Algebra.self_mem_adjoin_singleton O g)

open NumberField IsDedekindDomain in
private theorem exists_smul_pow_entry_mem_adicCompletionIntegers (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E))
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E))))) :
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ (k : ℕ) (i j : Fin n),
      a * ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ^ k) i j ∈
        w.adicCompletionIntegers E := by
  set O := w.adicCompletionIntegers E
  set C := closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E)))
  set S : Set (w.adicCompletion E) :=
    ⋃ i, ⋃ j, (fun h : GL (Fin n) (w.adicCompletion E) => (h : Matrix (Fin n) (Fin n) _) i j) '' C
  have hS : IsCompact S := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    hg.image (Units.continuous_val.matrix_elem i j)
  let U : {a : w.adicCompletion E // a ∈ O ∧ a ≠ 0} → Set (w.adicCompletion E) :=
    fun a => (fun x => a.1 * x) ⁻¹' (O : Set _)
  have hUo : ∀ a, IsOpen (U a) := fun a =>
    (Valued.isOpen_integer _).preimage (continuous_const.mul continuous_id)
  have hcov : S ⊆ ⋃ a, U a := by
    intro x _
    by_cases hx : x ∈ O
    · exact Set.mem_iUnion.2 ⟨⟨1, O.one_mem, one_ne_zero⟩, by simpa [U] using hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx O.zero_mem
      have hxi : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
      exact Set.mem_iUnion.2 ⟨⟨x⁻¹, hxi, inv_ne_zero hx0⟩, by simp [U, hx0, O.one_mem]⟩
  have hdir : Directed (· ⊆ ·) U := by
    rintro ⟨a, ha, ha0⟩ ⟨b, hb, hb0⟩
    refine ⟨⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0⟩, ?_, ?_⟩
    · intro x hx
      have := mul_mem hb (show a * x ∈ O from hx)
      simpa [U, mul_assoc, mul_comm, mul_left_comm] using this
    · intro x hx
      have := mul_mem ha (show b * x ∈ O from hx)
      simpa [U, mul_assoc] using this
  haveI : Nonempty {a : w.adicCompletion E // a ∈ O ∧ a ≠ 0} := ⟨⟨1, O.one_mem, one_ne_zero⟩⟩
  obtain ⟨a, hSa⟩ := hS.elim_directed_cover U hUo hcov hdir
  refine ⟨a.1, a.2.2, fun k i j => hSa ?_⟩
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨g ^ k, subset_closure ?_, by simp⟩⟩⟩
  exact Subgroup.npow_mem_zpowers g k

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.isIntegral_of_isCompact_closure_zpowers (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E))
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E))))) :
    IsIntegral (w.adicCompletionIntegers E)
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  obtain ⟨a, ha0, ha⟩ := exists_smul_pow_entry_mem_adicCompletionIntegers E w n g hg
  exact _root_.GlobalTheory.isIntegral_matrix_of_pow_bounded _ a ha0 fun k i j => ⟨⟨_, ha k i j⟩, rfl⟩

end GlobalTheory
