import Mathlib
import Formalism.PeriodIntegrals.FinOrdAd

noncomputable section

namespace PI

open NumberField IsDedekindDomain TensorProduct Matrix

theorem charpoly_int_of_powers_in_compact (hT : TensCpctDen) (hP : PowBddInt)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ)
    (γ : Matrix (Fin k) (Fin k) E) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ C : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F), IsCompact C →
    (∀ (n : ℕ) (i j : Fin k), inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) ((γ ^ n) i j) ∈ C) →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i) := by
  let _ := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro C hC hmem
  obtain ⟨N, hN, hNC⟩ := hT F E C hC
  exact hP E k γ N hN (fun n i j => hNC _ (hmem n i j))

theorem continuous_conj_entry (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (k : ℕ)
    (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (i j : Fin k) :
    letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      ((y * u * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) := by
  let _ := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  let : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  have : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have : ContinuousAdd (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) _
  have hmul : ∀ c d : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Continuous (fun z => c * z * d) := by
    intro c d
    have := IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F)
      ((LinearMap.mulRight (FiniteAdeleRing (𝓞 F) F) d).comp
        (LinearMap.mulLeft (FiniteAdeleRing (𝓞 F) F) c))
    exact this
  have he : ∀ a b : Fin k, Continuous (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      (u : Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) :=
    fun a b => Units.continuous_val.matrix_elem a b
  have hfun : (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      ((y * u * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) =
      fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => ∑ b, ∑ a, (y : Matrix (Fin k) (Fin k) _) i a *
        (u : Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b *
        ((y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin k) (Fin k) _) b j := by
    funext u
    simp only [Units.val_mul, Matrix.mul_apply, Finset.sum_mul]
  rw [hfun]
  exact continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun a _ => (hmul _ _).comp (he a b)

theorem finOrdAd_of (hU : UnitKron) (hP : PowBddInt) (hT : TensCpctDen) (hD : DefPosDef) : FinOrdAd := by
  intro F E _ _ _ _ _ hreal σ k J hH hDef U _hUle hUc y _hy γ hγ hbc
  let _ := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, Units.ext (Matrix.ext fun i _ => Fin.elim0 i)⟩
  · obtain ⟨hc, hdef⟩ := hD F E hreal σ k J hk hH hDef
    obtain ⟨u, hu, hyu⟩ := Subgroup.mem_map.mp hbc
    have hint := charpoly_int_of_powers_in_compact hT hP F E k (γ : Matrix (Fin k) (Fin k) E)
      (⋃ (i : Fin k) (j : Fin k), (fun u : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
        ((y * u * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) '' (U : Set _))
      (isCompact_iUnion fun i => isCompact_iUnion fun j => hUc.image (continuous_conj_entry F E k y i j))
      (by
        intro n i j
        have h1 : bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) (γ ^ n) = y * u ^ n * y⁻¹ := by
          rw [map_pow, ← hyu, ← map_pow]
          rfl
        refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, u ^ n, U.pow_mem hu n, ?_⟩⟩
        show ((y * u ^ n * y⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin k) (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j = _
        rw [← h1, ← Units.val_pow_eq_pow_val]
        rfl)
    have hγ' : ((γ : Matrix (Fin k) (Fin k) E).map (σ : E →+* E))ᵀ * J * (γ : Matrix (Fin k) (Fin k) E) = J := hγ
    obtain ⟨n, hn, hpow⟩ := hU E (σ : E →+* E) hc k J γ hdef hγ' hint
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Units.ext (by rw [Units.val_pow_eq_pow_val, hpow]; simp)⟩

end PI
