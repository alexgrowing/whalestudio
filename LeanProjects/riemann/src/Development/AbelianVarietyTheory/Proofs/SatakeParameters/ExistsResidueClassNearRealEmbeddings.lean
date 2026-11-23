import Mathlib

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace GlobalTheory

theorem exists_realPlace_embedding {F : Type} [Field F] [NumberField F] (τ : F →+* ℝ) :
    ∃ (P : InfinitePlace F) (hP : P.IsReal), embedding_of_isReal hP = τ := by
  have hreal : ComplexEmbedding.IsReal (Complex.ofRealHom.comp τ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hP : (InfinitePlace.mk (Complex.ofRealHom.comp τ)).IsReal := isReal_mk_iff.2 hreal
  refine ⟨_, hP, ?_⟩
  ext x
  apply Complex.ofReal_injective
  rw [embedding_of_isReal_apply, embedding_mk_eq_of_isReal hreal]
  simp

theorem exists_integer_near (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ, ∀ w : (F →+* ℝ) → ℝ, ∃ z : 𝓞 F, ∀ τ : F →+* ℝ, |τ (z : F) - w τ| ≤ C := by
  classical
  have hfin : Finite (F →+* ℝ) := by
    refine Finite.of_injective (fun τ => (Complex.ofRealHom.comp τ : F →+* ℂ)) ?_
    intro a b h
    ext x
    have := congrArg (fun f : F →+* ℂ => f x) h
    simpa using this
  have := Fintype.ofFinite (F →+* ℝ)
  let b := RingOfIntegers.basis F
  refine ⟨∑ τ : F →+* ℝ, ∑ i, |τ ((b i : 𝓞 F) : F)|, fun w => ?_⟩
  let v : mixedSpace F := (fun w' => w (embedding_of_isReal w'.2), 0)
  let c := (latticeBasis F).repr v
  refine ⟨∑ i, round (c i) • b i, fun τ => ?_⟩
  obtain ⟨P, hP, hτ⟩ := exists_realPlace_embedding τ
  have hv : v = ∑ i, c i • latticeBasis F i := ((latticeBasis F).sum_repr v).symm
  have hw : w τ = ∑ i, c i * τ ((b i : 𝓞 F) : F) := by
    have h1 := congrArg (fun u : mixedSpace F => u.1 ⟨P, hP⟩) hv
    simp only [v, hτ] at h1
    rw [h1]
    simp [Prod.fst_sum, Finset.sum_apply, latticeBasis_apply, integralBasis_apply,
      mixedEmbedding_apply_isReal, hτ, b, c, v]
  have hz : τ (((∑ i, round (c i) • b i : 𝓞 F)) : F)
      = ∑ i, (round (c i) : ℝ) * τ ((b i : 𝓞 F) : F) := by
    simp [map_sum]
  rw [hz, hw, ← Finset.sum_sub_distrib]
  calc |∑ i, ((round (c i) : ℝ) * τ ((b i : 𝓞 F) : F) - c i * τ ((b i : 𝓞 F) : F))|
      ≤ ∑ i, |(round (c i) : ℝ) * τ ((b i : 𝓞 F) : F) - c i * τ ((b i : 𝓞 F) : F)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |τ ((b i : 𝓞 F) : F)| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sub_mul, abs_mul]
        have h2 : |(round (c i) : ℝ) - c i| ≤ 1 := by
          have := abs_sub_round (c i)
          rw [abs_sub_comm]
          linarith
        exact mul_le_of_le_one_left (abs_nonneg _) h2
    _ ≤ ∑ τ' : F →+* ℝ, ∑ i, |τ' ((b i : 𝓞 F) : F)| :=
        Finset.single_le_sum (f := fun τ' : F →+* ℝ => ∑ i, |τ' ((b i : 𝓞 F) : F)|)
          (fun τ' _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ τ)

theorem residueClass_relativelyDense : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (m : Ideal (𝓞 F)) (a₀ : 𝓞 F), m ≠ ⊥ →
    ∃ C : ℝ, ∀ y : (F →+* ℝ) → ℝ, ∃ a : 𝓞 F, a - a₀ ∈ m ∧
      ∀ τ : F →+* ℝ, |τ (a : F) - y τ| ≤ C := by
  intro F _ _ _ m a₀ hm
  obtain ⟨C, hC⟩ := exists_integer_near F
  have hMpos : 0 < Ideal.absNorm m := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.1 h))
  set M : ℕ := Ideal.absNorm m with hMdef
  have hMmem : ((M : ℕ) : 𝓞 F) ∈ m := Ideal.absNorm_mem m
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hMpos
  refine ⟨M * C, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hC (fun τ => (y τ - τ (a₀ : F)) / M)
  refine ⟨a₀ + (M : 𝓞 F) * z, ?_, fun τ => ?_⟩
  · simpa using m.mul_mem_right z hMmem
  · have h := hz τ
    have h3 : τ (((a₀ + (M : 𝓞 F) * z : 𝓞 F)) : F) - y τ
        = M * (τ (z : F) - (y τ - τ (a₀ : F)) / M) := by
      have : τ (((a₀ + (M : 𝓞 F) * z : 𝓞 F)) : F) = τ (a₀ : F) + M * τ (z : F) := by
        simp
      rw [this]
      field_simp
      ring
    rw [h3, abs_mul, abs_of_pos hM0]
    exact mul_le_mul_of_nonneg_left h hM0.le

end GlobalTheory
