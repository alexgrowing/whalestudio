import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

private noncomputable def UpperTheory.canonicalEmbeddingVector (E : Type) [Field E] [NumberField E] (d : ℕ) :
    (Fin d → 𝓞 E) →ₗ[ℤ] (Fin d → ((E →+* ℂ) → ℂ)) where
  toFun v := fun i => canonicalEmbedding E (v i : E)
  map_add' v w := by ext i φ; simp
  map_smul' n v := by ext i φ; simp

private theorem UpperTheory.canonicalEmbeddingVector_injective (E : Type) [Field E] [NumberField E] (d : ℕ) :
    Function.Injective (UpperTheory.canonicalEmbeddingVector E d) := by
  intro v w h
  ext i
  exact canonicalEmbedding_injective E (congrFun h i)

theorem UpperTheory.integral_vectors_height_summable :
    ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (s : ℝ), ((d * Module.finrank ℚ E : ℕ) : ℝ) < s →
        Summable fun v : {v : Fin d → E // ∀ i, IsIntegral ℤ (v i)} => (∑ i, ∑ φ : E →+* ℂ, ‖φ (v.1 i)‖) ^ (-s) := by
  intro E _ _ d s hs
  classical
  have hs0 : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg _) hs
  let L : Submodule ℤ (Fin d → ((E →+* ℂ) → ℂ)) := LinearMap.range (UpperTheory.canonicalEmbeddingVector E d)
  have hdisc : DiscreteTopology L := by
    refine DiscreteTopology.of_forall_le_norm (r := 1) one_pos ?_
    rintro ⟨_, v, rfl⟩ hx
    have hv : v ≠ 0 := by
      rintro rfl
      exact hx (Subtype.ext (map_zero _))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have h1 : 1 ≤ house (v i : E) :=
      one_le_house_of_isIntegral (v i).isIntegral_coe (by simpa using hi)
    exact h1.trans (norm_le_pi_norm (UpperTheory.canonicalEmbeddingVector E d v) i)
  have hrank : Module.finrank ℤ L = d * Module.finrank ℚ E := by
    rw [LinearMap.finrank_range_of_inj (UpperTheory.canonicalEmbeddingVector_injective E d), Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  have hsum := ZLattice.summable_norm_rpow L (-s) (by rw [hrank]; linarith)
  let g : {v : Fin d → E // ∀ i, IsIntegral ℤ (v i)} → L := fun v =>
    ⟨UpperTheory.canonicalEmbeddingVector E d (fun i => ⟨v.1 i, v.2 i⟩), LinearMap.mem_range_self _ _⟩
  have hg : Function.Injective g := by
    intro v w h
    have h2 := UpperTheory.canonicalEmbeddingVector_injective E d (congrArg Subtype.val h)
    ext i
    exact congrArg Subtype.val (congrFun h2 i)
  refine Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_) (hsum.comp_injective hg)
  have hle : ‖g v‖ ≤ ∑ i, ∑ φ : E →+* ℂ, ‖φ (v.1 i)‖ := by
    show ‖UpperTheory.canonicalEmbeddingVector E d (fun i => ⟨v.1 i, v.2 i⟩)‖ ≤ _
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun φ => ?_
    show ‖φ (v.1 i)‖ ≤ _
    calc ‖φ (v.1 i)‖ ≤ ∑ φ : E →+* ℂ, ‖φ (v.1 i)‖ :=
          Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ (v.1 i)‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ φ)
      _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ φ : E →+* ℂ, ‖φ (v.1 i)‖)
            (fun _ _ => by positivity) (Finset.mem_univ i)
  by_cases h0 : ‖g v‖ = 0
  · have hz : g v = g ⟨0, fun _ => isIntegral_zero⟩ := by
      rw [norm_eq_zero.mp h0]
      apply Subtype.ext
      ext i φ
      show (0 : ℂ) = φ 0
      simp
    have hv := hg hz
    subst hv
    simp only [Pi.zero_apply, map_zero, norm_zero, Finset.sum_const_zero,
      Real.zero_rpow (neg_ne_zero.mpr hs0.ne')]
    exact Real.rpow_nonneg (norm_nonneg _) _
  · exact Real.rpow_le_rpow_of_nonpos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) hle (by linarith)
