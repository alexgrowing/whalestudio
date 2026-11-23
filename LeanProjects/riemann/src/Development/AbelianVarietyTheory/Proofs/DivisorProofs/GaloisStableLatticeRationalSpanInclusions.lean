import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealSmulMemSpanRational
open NumberField

namespace GlobalTheory

theorem differentIdeal_int_le_differentIdeal (K K' : Type) [Field K] [NumberField K] [Field K']
    [NumberField K'] [Algebra K K'] :
    differentIdeal ℤ (𝓞 K') ≤ differentIdeal (𝓞 K) (𝓞 K') := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 K')]
  exact Ideal.mul_le_left

theorem span_rational_le_span_and_different_smul_le :
    ∀ (K K' L : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L] [NumberField L] [Algebra K K'] [IsGalois K K'] [Algebra K' L] (n : ℕ) (M : Submodule (𝓞 K') (Fin n → K')), (∀ (s : K' ≃ₐ[K] K'), ∀ x ∈ M, (fun i => s (x i)) ∈ M) → Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) ≤ Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ∧ (differentIdeal ℤ (𝓞 K')).map (algebraMap (𝓞 K') (𝓞 L)) • Submodule.span (𝓞 L) ((fun x i => algebraMap K' L (x i)) '' (M : Set (Fin n → K'))) ≤ Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) := by
  intro K K' L _ _ _ _ _ _ _ _ _ n M hM
  set φ : (Fin n → K') → (Fin n → L) := fun x i => algebraMap K' L (x i) with hφ
  set P := Submodule.span (𝓞 L) ((fun (x : Fin n → K) i => algebraMap K' L (algebraMap K K' (x i))) '' {x | (fun i => algebraMap K K' (x i)) ∈ M}) with hP
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨_, hx, rfl⟩
  ·
    have himg : ∀ y ∈ Submodule.span (𝓞 K') {y : Fin n → K' | y ∈ M ∧ ∃ y0 : Fin n → K, y = fun i => algebraMap K K' (y0 i)}, φ y ∈ P := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨hyM, y0, rfl⟩ := hy
        exact Submodule.subset_span ⟨y0, hyM, rfl⟩
      | zero =>
        have h0 : φ 0 = 0 := by funext i; simp [hφ]
        rw [h0]; exact P.zero_mem
      | add a b _ _ ha hb =>
        have : φ (a + b) = φ a + φ b := by funext i; simp [hφ]
        rw [this]; exact P.add_mem ha hb
      | smul c a _ ha =>
        have : φ (c • a) = algebraMap (𝓞 K') (𝓞 L) c • φ a := by
          funext i
          change algebraMap K' L ((c : K') * a i) = ((algebraMap (𝓞 K') (𝓞 L) c : 𝓞 L) : L) * φ a i
          rw [map_mul]; rfl
        rw [this]; exact P.smul_mem _ ha
    rw [Ideal.map, Submodule.span_smul_span, Submodule.span_le]
    intro z hz
    obtain ⟨_, ⟨d, hd, rfl⟩, _, ⟨x, hx, rfl⟩, rfl⟩ := Set.mem_smul.mp hz
    have hdK : d ∈ differentIdeal (𝓞 K) (𝓞 K') := differentIdeal_int_le_differentIdeal K K' hd
    have hmem := differentIdeal_smul_mem_span_rational K K' n M hM d hdK x hx
    have h := himg _ hmem
    have : φ (d • x) = algebraMap (𝓞 K') (𝓞 L) d • φ x := by
      funext i
      change algebraMap K' L ((d : K') * x i) = ((algebraMap (𝓞 K') (𝓞 L) d : 𝓞 L) : L) * φ x i
      rw [map_mul]; rfl
    rw [this] at h
    exact h

end GlobalTheory
