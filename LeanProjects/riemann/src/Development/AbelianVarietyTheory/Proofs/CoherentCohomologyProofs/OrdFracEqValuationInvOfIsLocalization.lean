import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsDiscreteValuationRingLocalizationOfIsDedekindD

open Module IsDiscreteValuationRing IsDedekindDomain TensorProduct Pointwise

universe u v

namespace GlobalTheory

namespace ExtField

section Local

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type*} [Field L] [Algebra A L] [IsFractionRing A L]
  [Algebra R A] [IsLocalHom (algebraMap R A)] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R A L]
  {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain A] [IsDiscreteValuationRing A]
  [IsFractionRing A L] [IsLocalHom (algebraMap R A)] in
variable (R K L) in
include K L in

theorem faithfulSMul_of_tower : FaithfulSMul R A := by
  rw [faithfulSMul_iff_algebraMap_injective]
  have h : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  rw [IsScalarTower.algebraMap_eq R A L] at h
  exact Function.Injective.of_comp h

end Local

section Kernel

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {V : Type*} [AddCommGroup V] [Module K V]
  {ι : Type*}

theorem ker_liftBaseChange_eq_of_finrank_le [Fintype ι] [DecidableEq ι] (c : V →ₗ[K] (ι → L))
    {W₀ : Submodule K V} (hW : W₀ ≤ LinearMap.ker c) [FiniteDimensional K (V ⧸ W₀)]
    (hr : finrank K (V ⧸ W₀) ≤ Fintype.card ι) {θ : ι → V}
    (hdet : (Matrix.of fun i j => c (θ j) i).det ≠ 0) :
    LinearMap.ker (c.liftBaseChange L) = W₀.baseChange L := by
  let g : L ⊗[K] (V ⧸ W₀) →ₗ[L] (ι → L) := (W₀.liftQ c hW).liftBaseChange L
  have hg : c.liftBaseChange L = g ∘ₗ W₀.mkQ.baseChange L := by
    ext v i
    simp [g]
  have hs : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet)) y
    refine ⟨∑ j, a j ⊗ₜ Submodule.Quotient.mk (θ j), ?_⟩
    funext i
    simp [g, Matrix.mulVec, dotProduct, mul_comm]
  have hi : LinearMap.ker g = ⊥ := by
    have h₁ := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_baseChange,
      Module.finrank_fintype_fun_eq_card] at h₁
    rw [← Submodule.finrank_eq_zero]
    omega
  rw [hg, LinearMap.ker_comp, hi, Submodule.comap_bot, ker_baseChange_mkQ]

end Kernel

section Scale

variable {R K V ι : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

end Scale

section Free

variable (R S : Type*) [CommRing R] [Nontrivial R] [AddCommGroup S] [Module R S]
  [Module.Free R S] [Module.Finite R S] (Q : Type*) [AddCommGroup Q] [Module R Q]

end Free

section Valuation

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] (P : HeightOneSpectrum S)
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra S A]
  [IsLocalization.AtPrime A P.asIdeal] [Algebra A L] [IsScalarTower S A L] [IsFractionRing A L]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
private theorem valuation_algebraMap_le_one (a : A) : P.valuation L (algebraMap A L a) ≤ 1 := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj P.asIdeal.primeCompl a
  have h₁ := congrArg (fun y => P.valuation L (algebraMap A L y)) h
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at h₁
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem P).mpr s.2, mul_one] at h₁
  rw [h₁]
  exact P.valuation_le_one r

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
private theorem valuation_algebraMap_unit (u : Aˣ) : P.valuation L (algebraMap A L u) = 1 := by
  refine eq_one_of_one_le_mul_left (valuation_algebraMap_le_one (L := L) P A (u : A))
    (valuation_algebraMap_le_one (L := L) P A (u⁻¹ : Aˣ)) ?_
  rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]

omit [IsFractionRing A L] in
private theorem valuation_algebraMap_irreducible {ϖ : A} (hϖ : Irreducible ϖ) :
    P.valuation L (algebraMap A L ϖ) = WithZero.exp (-1) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer' L
  have hπ' : P.valuation L (algebraMap A L (algebraMap S A π)) = WithZero.exp (-1) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact hπ
  have h₀ : algebraMap S A π ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  obtain ⟨k, u, hu⟩ := eq_unit_mul_pow_irreducible h₀ hϖ
  rw [hu, map_mul, map_mul, valuation_algebraMap_unit, one_mul, map_pow, map_pow] at hπ'
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, ← WithZero.exp_zero, WithZero.exp_inj] at hπ'
    omega
  have h₁ : P.valuation L (algebraMap A L ϖ) ≠ 0 := by
    intro h
    rw [h, zero_pow hk] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  rw [← WithZero.exp_log h₁, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at hπ'
  rw [← WithZero.exp_log h₁, WithZero.exp_inj]
  rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' hπ' with h | h
  · exact h.2
  · omega

theorem ordFrac_eq_valuation_inv_of_isLocalization (x : L) :
    Ring.ordFrac A x = (P.valuation L x)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, rfl⟩ := exists_units_eq_smul_zpow_of_irreducible hϖ hx
  rw [Units.smul_def, Algebra.smul_def, ordFrac_unit_mul_zpow hϖ, map_mul, map_zpow₀,
    valuation_algebraMap_unit, valuation_algebraMap_irreducible P A hϖ, one_mul,
    ← WithZero.exp_zsmul, ← WithZero.exp_neg]
  simp

theorem log_ordFrac_eq_neg_log_valuation (x : L) :
    WithZero.log (Ring.ordFrac A x) = -WithZero.log (P.valuation L x) := by
  rw [ordFrac_eq_valuation_inv_of_isLocalization P A, WithZero.log_inv]

end Valuation

section Semilocal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]

omit [Module.Finite R S] in
variable {S} in
private theorem exists_algebra_localization (P : HeightOneSpectrum S) :
    ∃ _ : Algebra (Localization.AtPrime P.asIdeal) L,
      IsScalarTower S (Localization.AtPrime P.asIdeal) L ∧
      IsScalarTower R (Localization.AtPrime P.asIdeal) L ∧
      IsFractionRing (Localization.AtPrime P.asIdeal) L := by
  have hu : ∀ y : P.asIdeal.primeCompl, IsUnit (algebraMap S L y) := fun y =>
    IsLocalization.map_units L ⟨y.1, P.asIdeal.primeCompl_le_nonZeroDivisors y.2⟩
  letI : Algebra (Localization.AtPrime P.asIdeal) L := (IsLocalization.lift hu).toAlgebra
  have h₁ : IsScalarTower S (Localization.AtPrime P.asIdeal) L :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp hu).symm
  refine ⟨inferInstance, h₁, IsScalarTower.of_algebraMap_eq fun r => ?_,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl _ L⟩
  rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime P.asIdeal),
    ← IsScalarTower.algebraMap_apply S, ← IsScalarTower.algebraMap_apply]

variable {S} in
private theorem dvr_localization (P : HeightOneSpectrum S) :
    IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S P.ne_bot _

include R K L in

theorem not_isField_of_finite : ¬ IsField S := by
  have := faithfulSMul_of_tower R K S L
  rw [← Algebra.IsIntegral.isField_iff_isField (FaithfulSMul.algebraMap_injective R S)]
  exact not_isField R

include R in

theorem finite_heightOneSpectrum : Finite (HeightOneSpectrum S) := by
  have := finite_maximalSpectrum_of_finite R S
  exact Finite.of_injective (fun P : HeightOneSpectrum S => (⟨P.asIdeal, P.isMaximal⟩ :
    MaximalSpectrum S)) fun P Q h => HeightOneSpectrum.ext (congrArg MaximalSpectrum.asIdeal h)

include R S in

theorem finrank_field_pos : 0 < finrank K L := by
  have := faithfulSMul_of_tower R K S L
  rw [IsFractionRing.finrank_eq R K S L]
  exact Module.finrank_pos

variable [Fintype (HeightOneSpectrum S)]

private theorem log_ordFrac_norm_algebraMap {x : S} (hx : x ≠ 0) :
    WithZero.log (Ring.ordFrac R (Algebra.norm K (algebraMap S L x))) =
      ∑ P : HeightOneSpectrum S,
        (P.asIdeal.inertiaDeg R : ℤ) * -WithZero.log (P.valuation L (algebraMap S L x)) := by
  have := faithfulSMul_of_tower R K S L
  let e := HeightOneSpectrum.equivMaximalSpectrum (not_isField_of_finite R K S L)
  letI : Fintype (MaximalSpectrum S) := Fintype.ofEquiv _ e
  have := isDiscreteValuationRing_localization_of_isDedekindDomain R (S := S)
  have h := addVal_norm_eq_sum R (fun n : MaximalSpectrum S => Localization.AtPrime n.asIdeal) x
  rw [← e.sum_comp] at h
  have key : ∀ P : HeightOneSpectrum S, ∃ m : ℕ,
      addVal (Localization.AtPrime (e P).asIdeal) (algebraMap S _ x) = m ∧
        -WithZero.log (P.valuation L (algebraMap S L x)) = m := by
    intro P
    obtain ⟨_, _, _, _⟩ := exists_algebra_localization R L P
    have := dvr_localization P
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (addVal_localization_ne_top R
      (fun n : MaximalSpectrum S => Localization.AtPrime n.asIdeal)
      (mem_nonZeroDivisors_of_ne_zero hx) (e P))
    refine ⟨m, hm.symm, ?_⟩
    have hm₁ : addVal (Localization.AtPrime P.asIdeal) (algebraMap S _ x) = m := hm.symm
    rw [← log_ordFrac_eq_neg_log_valuation P (Localization.AtPrime P.asIdeal),
      IsScalarTower.algebraMap_apply S (Localization.AtPrime P.asIdeal) L,
      ordFrac_algebraMap_eq_exp hm₁, WithZero.log_exp]
  choose m hm hm' using key
  simp only [hm] at h
  norm_cast at h
  rw [Algebra.norm_localization R (nonZeroDivisors R), ordFrac_algebraMap_eq_exp h,
    WithZero.log_exp]
  push_cast
  exact Finset.sum_congr rfl fun P _ => by rw [hm', mul_comm]; rfl

variable {L} in

theorem log_ordFrac_norm_eq_sum {x : L} (hx : x ≠ 0) :
    WithZero.log (Ring.ordFrac R (Algebra.norm K x)) =
      ∑ P : HeightOneSpectrum S,
        (P.asIdeal.inertiaDeg R : ℤ) * -WithZero.log (P.valuation L x) := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (finrank_field_pos R K S L)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hb₀ : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha₀ : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hb₁ : algebraMap S L b ≠ 0 := by simpa using hb₀
  have ha₁ : algebraMap S L a ≠ 0 := by simpa using ha₀
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, map_mul, map_inv₀,
    WithZero.log_mul (by simpa using ha₀) (by simpa using hb₀), WithZero.log_inv,
    log_ordFrac_norm_algebraMap R K S L ha₀, log_ordFrac_norm_algebraMap R K S L hb₀,
    ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [map_mul, map_inv₀, WithZero.log_mul (by simpa using ha₀) (by simpa using hb₀),
    WithZero.log_inv]
  ring

variable {R K S L}
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [FloorRing F]

end Semilocal

end ExtField

example {K L : Type*} [Field K] [Field L] [Algebra K L] {a : L} (ha : a ≠ 0) :
    ∃ W₀ : Submodule K (K × K), W₀ ≠ ⊥ ∧ W₀ ≠ ⊤ ∧ LinearMap.ker ((LinearMap.pi fun _ : Fin 1 =>
      (LinearMap.fst K K K).smulRight a).liftBaseChange L) = W₀.baseChange L := by
  refine ⟨LinearMap.ker (LinearMap.fst K K K), ?_, ?_, ?_⟩
  · rw [Submodule.ne_bot_iff]
    exact ⟨(0, 1), rfl, by simp⟩
  · intro h
    simpa using (h ▸ Submodule.mem_top : (1, 0) ∈ LinearMap.ker (LinearMap.fst K K K))
  · refine ExtField.ker_liftBaseChange_eq_of_finrank_le _ (fun x hx => ?_) ?_
      (θ := fun _ => (1, 0)) (by simpa using ha)
    · funext i
      simpa [ha] using hx
    · rw [((LinearMap.fst K K K).quotKerEquivOfSurjective LinearMap.fst_surjective).finrank_eq]
      simp

end GlobalTheory
