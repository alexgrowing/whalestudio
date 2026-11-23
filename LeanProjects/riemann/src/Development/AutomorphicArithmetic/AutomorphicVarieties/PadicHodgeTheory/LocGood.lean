import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RtChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

section Series

variable {E σ : Type} [Field E]

private theorem mem_max_iff (f : MvPowerSeries σ E) :
    f ∈ maximalIdeal (MvPowerSeries σ E) ↔ MvPowerSeries.constantCoeff f = 0 := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    not_not]

private theorem sum_X_mul (s : Finset σ) :
    ∀ f : MvPowerSeries σ E, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0) →
      ∃ g : σ → MvPowerSeries σ E, f = ∑ i ∈ s, MvPowerSeries.X i * g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f h
    refine ⟨fun _ => 0, ?_⟩
    ext n
    simpa using h n (by simp)
  | insert a s ha ih =>
    intro f h
    let q : MvPowerSeries σ E := fun n => MvPowerSeries.coeff (Finsupp.single a 1 + n) f
    have hqc : ∀ n, MvPowerSeries.coeff n q = MvPowerSeries.coeff (Finsupp.single a 1 + n) f := fun _ => rfl
    obtain ⟨g, e⟩ := ih (f - MvPowerSeries.X a * q) (by
      intro n hn
      rw [map_sub, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
      split_ifs with hle
      · rw [hqc, add_tsub_cancel_of_le hle, one_mul, sub_self]
      · rw [sub_zero]
        refine h n fun i hi => ?_
        rcases Finset.mem_insert.1 hi with rfl | hi
        · rw [Finsupp.single_le_iff] at hle
          omega
        · exact hn i hi)
    refine ⟨Function.update g a q, ?_⟩
    rw [Finset.sum_insert ha, Function.update_self,
      Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi ha)], ← e]
    ring

private theorem coeff_lin_mul (i : σ) (a b : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (a * b) =
      MvPowerSeries.constantCoeff a * MvPowerSeries.coeff (Finsupp.single i 1) b +
        MvPowerSeries.coeff (Finsupp.single i 1) a * MvPowerSeries.constantCoeff b := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map, Finset.Nat.antidiagonal_succ]
  simp

private theorem coeff_lin_X [DecidableEq σ] (i j : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.X j : MvPowerSeries σ E) = if i = j then 1 else 0 := by
  rw [MvPowerSeries.coeff_X]
  simp only [Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]

private theorem coeff_lin_of_mem_sq {f : MvPowerSeries σ E} (hf : f ∈ maximalIdeal (MvPowerSeries σ E) ^ 2)
    (i : σ) : MvPowerSeries.coeff (Finsupp.single i 1) f = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) fun a b ha hb => ?_
  · rw [coeff_lin_mul, (mem_max_iff a).1 ha, (mem_max_iff b).1 hb, zero_mul, mul_zero, add_zero]
  · rw [map_add, ha, hb, add_zero]

private theorem mem_sq_of_coeff [Fintype σ] {f : MvPowerSeries σ E} (h0 : MvPowerSeries.constantCoeff f = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) f = 0) : f ∈ maximalIdeal (MvPowerSeries σ E) ^ 2 := by
  classical
  obtain ⟨g, e⟩ := sum_X_mul Finset.univ f fun n hn => by
    have : n = 0 := Finsupp.ext fun j => hn j (Finset.mem_univ j)
    subst this
    simpa using h0
  have hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0 := fun i => by
    have := h1 i
    rw [e, map_sum] at this
    simpa [coeff_lin_mul, coeff_lin_X] using this
  rw [e, pow_two]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_mul ((mem_max_iff _).2 (MvPowerSeries.constantCoeff_X i)) ((mem_max_iff _).2 (hg i))

end Series

private theorem zl_inj (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra h
  have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
  have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ hm
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm

theorem UpperTheory.V.Loc.locGood :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), LocGood U (D.It U) := by
  intro hP l _ O _ _ _ _ _ _ _ D U
  refine ⟨?_, ?_⟩
  · rintro R _ _ _ r r' h hh e ⟨f, hf, hI⟩
    obtain ⟨f', hf', hI'⟩ := rtConj hP D U R r.hom h hh ⟨f, congrArg GLift.hom hf, hI⟩
    exact ⟨f', GLift.ext (hf'.trans e.symm), hI'⟩
  · have hi := zl_inj l O
    haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
    have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
      exact (IsFractionRing.injective O _).comp hi
    letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
    haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
      IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
    haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance
    haveI : Module.Finite ℚ_[l] (FractionRing O) :=
      Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])
    obtain ⟨x, hx, -⟩ := univEx D U
    obtain ⟨w, φ, hc, hd, hg⟩ := rtChart hP D U (FractionRing O) x hx
    refine ⟨x, Fin 12, inferInstance, w, φ, hx, ⟨hc.ker, hg, hc.const, fun i => ?_, fun f hf h1 => ?_⟩, hd⟩
    · obtain ⟨a, c, hc0, ha⟩ := hc.dense 2 (MvPowerSeries.X i)
      have key : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) (φ a) =
          if j = i then algebraMap O (FractionRing O) c else 0 := fun j => by
        have := coeff_lin_of_mem_sq ha j
        rw [map_sub, sub_eq_zero, ← algebraMap_smul (FractionRing O) c, map_smul, coeff_lin_X] at this
        rw [← this]
        split_ifs <;> simp
      refine ⟨a, ?_, fun j hj => by rw [key, if_neg hj]⟩
      rw [key, if_pos rfl]
      exact (map_ne_zero_iff _ (IsFractionRing.injective O _)).2 hc0
    · exact hc.inj 2 f (mem_sq_of_coeff (by rw [hc.const, hf, map_zero]) h1)
