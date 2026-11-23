import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
open scoped TensorProduct

namespace GlobalTheory.LocalLatticeIntegral

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ r : 𝓞 E, (r : E) = (M : E) * e := by
  have h : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨M, hM, hi⟩ := h.exists_integral_multiple
  exact ⟨M, hM, ⟨M • e, hi⟩, by simp [zsmul_eq_mul]⟩

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    [hL : Submodule.IsLattice E L] (x : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, h1⟩ := hx
    obtain ⟨M, hM, h2⟩ := hy
    refine ⟨N * M, mul_ne_zero hN hM, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.toAddSubgroup.zsmul_mem h1 M
    · rw [mul_smul]; exact L.toAddSubgroup.zsmul_mem h2 N
  | smul e x _ hx =>
    obtain ⟨N, hN, h1⟩ := hx
    obtain ⟨M, hM, r, hr⟩ := exists_int_mul_integral e
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h2 := L.smul_mem r h1
    convert h2 using 1
    funext j
    have : (r • N • x) j = (r : E) * ((N : E) * x j) := by
      simp [Algebra.smul_def, zsmul_eq_mul]
    rw [this, hr]
    simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_mul]
    ring

theorem exists_single_mem_latLoc : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) [Submodule.IsLattice E L] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∃ (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), c ≠ (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧ ∀ (i : Fin n), Pi.single i (c ⊗ₜ[F] (1 : E)) ∈ GlobalTheory.AdelicU.latLoc F L v := by
  intro F E _ _ _ _ _ n L _ v
  choose N hN hmem using fun i : Fin n => exists_int_smul_mem L (Pi.single i (1 : E))
  have hP : (∏ i, N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hN i
  haveI : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :=
    charZero_of_injective_algebraMap (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).injective
  refine ⟨((∏ i, N i : ℤ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), Int.cast_ne_zero.2 hP, fun i => ?_⟩
  obtain ⟨k, hk⟩ : N i ∣ ∏ j, N j := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  have h1 : (∏ j, N j) • (Pi.single i (1 : E) : Fin n → E) ∈ L := by
    rw [hk, mul_comm, mul_smul]; exact L.toAddSubgroup.zsmul_mem (hmem i) k
  generalize (∏ j, N j) = P at h1
  refine AddSubgroup.subset_closure ⟨1, one_mem _, _, h1, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_same, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      zsmul_eq_mul, mul_one]
  · rw [Pi.single_eq_of_ne hj, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, TensorProduct.tmul_zero]

end GlobalTheory.LocalLatticeIntegral
