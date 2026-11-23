import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.embCyc :
    ∀ (N m M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K] (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {m} K K'] (L : Type) [Field L] [NumberField L] [Algebra K' L] [IsCyclotomicExtension {M} K' L], N ∣ M → m ∣ M → Nonempty (K →ₐ[ℚ] CyclotomicField N ℚ) → IsCyclotomicExtension {M} ℚ L := by
  intro N m M _ K _ _ _ K' _ _ _ _ L _ _ _ _ hNM hmM hφ
  obtain ⟨φ⟩ := hφ
  have hM0 : M ≠ 0 := NeZero.ne M
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hM0 (zero_dvd_iff.mp hNM)
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K' L (Set.mem_singleton M) hM0
  let F : Subalgebra ℚ L := Algebra.adjoin ℚ {ζ}
  have hroot : ∀ x : L, ∀ k : ℕ, k ∣ M → x ^ k = 1 → x ∈ F := by
    intro x k hk hx
    have hxM : x ^ M = 1 := by
      obtain ⟨j, hj⟩ := hk
      rw [hj, pow_mul, hx, one_pow]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hxM
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _
  have hpN : IsPrimitiveRoot (ζ ^ (M / N)) N := by
    have := hζ.pow_of_dvd (p := M / N) ?_ (Nat.div_dvd_of_dvd hNM)
    · rwa [Nat.div_div_self hNM hM0] at this
    · exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hNM) (Nat.pos_of_ne_zero hN0)).ne'
  have hsp : Polynomial.Splits ((Polynomial.X ^ N - 1 : Polynomial ℚ).map (algebraMap ℚ L)) := by
    simpa using Polynomial.X_pow_sub_one_splits hpN
  haveI hC : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := by
    convert CyclotomicField.isCyclotomicExtension N ℚ
    · rfl
    · exact Subsingleton.elim _ _
  haveI := IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ (CyclotomicField N ℚ)
  let ψ : CyclotomicField N ℚ →ₐ[ℚ] L :=
    Polynomial.IsSplittingField.lift (CyclotomicField N ℚ) (Polynomial.X ^ N - 1) hsp
  have h1 : ∀ y, ψ y ∈ F := by
    intro y
    have hy := IsCyclotomicExtension.adjoin_roots (S := {N}) (A := ℚ) y
    have hle : Algebra.adjoin ℚ {b : CyclotomicField N ℚ | ∃ n : ℕ, n ∈ ({N} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1}
        ≤ F.comap ψ := by
      rw [Algebra.adjoin_le_iff]
      rintro b ⟨n, hn, -, hb⟩
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hb
      exact hroot (ψ b) N hNM (by rw [← map_pow, hb, map_one])
    exact hle hy
  have h2 : ∀ k : K, algebraMap K' L (algebraMap K K' k) ∈ F := by
    intro k
    let e1 : K →ₐ[ℚ] L := ((algebraMap K' L).comp (algebraMap K K')).toRatAlgHom
    let e2 : K →ₐ[ℚ] L := ψ.comp φ
    let g := e2.equivFieldRange
    haveI := Normal.of_algEquiv g
    have hr := AlgHom.fieldRange_of_normal (e1.comp g.symm.toAlgHom)
    have hk : e1 k ∈ e2.fieldRange := by
      rw [← hr]
      exact AlgHom.mem_fieldRange.mpr ⟨g k, by simp⟩
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hk
    show e1 k ∈ F
    rw [← hy]
    exact h1 (φ y)
  have h3 : ∀ x : K', algebraMap K' L x ∈ F := by
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {m}) (A := K) x
    induction hx using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨n, hn, -, hbn⟩ := hb
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      exact hroot _ m hmM (by rw [← map_pow, hbn, map_one])
    | algebraMap k => exact h2 k
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  have h4 : ∀ x : L, x ∈ F := by
    intro x
    have hx := IsCyclotomicExtension.adjoin_roots (S := {M}) (A := K') x
    induction hx using Algebra.adjoin_induction with
    | mem b hb =>
      obtain ⟨n, hn, -, hbn⟩ := hb
      rw [Set.mem_singleton_iff] at hn
      rw [hn] at hbn
      exact hroot _ M dvd_rfl hbn
    | algebraMap k => exact h3 k
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨ζ, hζ⟩, fun x => Algebra.adjoin_mono ?_ (h4 x)⟩
  rintro _ rfl
  exact hζ.pow_eq_one
