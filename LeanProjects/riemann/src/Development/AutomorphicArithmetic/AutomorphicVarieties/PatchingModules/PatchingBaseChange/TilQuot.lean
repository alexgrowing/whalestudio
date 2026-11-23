import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.KerMapPowerSeriesQuotient

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem mem_map_C_of_forall_coeff_mem_of_fg {A : Type} [CommRing A] (J : Ideal A) (hJ : J.FG) (f : PowerSeries A)
    (h : ∀ n, PowerSeries.coeff n f ∈ J) : f ∈ J.map PowerSeries.C := by
  obtain ⟨s, rfl⟩ := hJ
  have hc : ∀ n, ∃ c : A → A, Function.support c ⊆ ↑s ∧ ∑ a ∈ s, c a • a = PowerSeries.coeff n f :=
    fun n => Submodule.mem_span_finset.mp (h n)
  choose c _ hc using hc
  have hf : f = ∑ a ∈ s, PowerSeries.C a * PowerSeries.mk (fun n => c n a) := by
    ext n
    rw [map_sum]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    rw [← hc n]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hf]
  refine Ideal.sum_mem _ fun a ha => Ideal.mul_mem_right _ _ ?_
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ha)

theorem UpperTheory.V.Pa.BC.til_quot :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (R : Type) [CommRing R] [Algebra O R] (I : Ideal R), I.FG → Function.Surjective (Til.map O' (Ideal.Quotient.mkₐ O I)) ∧ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I)) = I.map (Til.ι O O' R) := by
  intro O O' _ _ _ R _ _ I hI
  set φ := Algebra.TensorProduct.map (AlgHom.id O' O') (Ideal.Quotient.mkₐ O I) with hφ
  have hsurj : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩) (Ideal.Quotient.mkₐ_surjective O I)
  have hker : RingHom.ker φ = I.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) := by
    have e := Algebra.TensorProduct.lTensor_ker (A := O') (Ideal.Quotient.mkₐ O I)
      (Ideal.Quotient.mkₐ_surjective O I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ O I) = I := by
      ext x
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hk] at e
    rw [← e]
    rfl
  have hcoeff : ∀ (f : Til O O' R) (n : ℕ),
      PowerSeries.coeff n (Til.map O' (Ideal.Quotient.mkₐ O I) f : PowerSeries (O' ⊗[O] (R ⧸ I)))
        = φ (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R))) :=
    fun f n => PowerSeries.coeff_map _ _ _
  refine ⟨?_, ?_⟩
  · intro f
    refine ⟨(PowerSeries.mk fun n =>
      (hsurj (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] (R ⧸ I))))).choose : PowerSeries (O' ⊗[O] R)), ?_⟩
    apply PowerSeries.ext
    intro n
    refine (hcoeff _ n).trans ?_
    erw [PowerSeries.coeff_mk]
    exact (hsurj _).choose_spec
  · have hι : I.map (Til.ι O O' R) = (RingHom.ker φ).map (Til.C O O' R) := by
      rw [hker]
      exact (Ideal.map_map _ _).symm
    rw [hι]
    ext f
    rw [RingHom.mem_ker]
    constructor
    · intro hf
      have h : ∀ n, PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R)) ∈ RingHom.ker φ := by
        intro n
        rw [RingHom.mem_ker, ← hcoeff, hf]
        exact map_zero _
      have hJ : (RingHom.ker φ).FG := by
        rw [hker]
        exact hI.map _
      exact mem_map_C_of_forall_coeff_mem_of_fg _ hJ f h
    · intro hf
      refine (Ideal.map_le_iff_le_comap.mpr ?_ : (RingHom.ker φ).map (Til.C O O' R)
        ≤ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I))) hf
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      apply PowerSeries.ext
      intro n
      rw [hcoeff]
      change φ (PowerSeries.coeff n (PowerSeries.C x : PowerSeries (O' ⊗[O] R)))
        = PowerSeries.coeff n (0 : PowerSeries (O' ⊗[O] (R ⧸ I)))
      rw [PowerSeries.coeff_C, map_zero]
      split_ifs
      · exact RingHom.mem_ker.mp hx
      · exact map_zero _
