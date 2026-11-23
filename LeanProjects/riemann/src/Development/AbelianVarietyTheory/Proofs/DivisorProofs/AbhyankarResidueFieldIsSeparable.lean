import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralClStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrExistsUnitPowEqMulUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAevalValuationDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerResidueMemAdjoinUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationNormalizationRootAdjoinIsDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureTensorLocalizationInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationMulEqAevalRootStatement
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

theorem residueField_isSeparable_of_kummer_root (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)]
    (hinj : Function.Injective (algebraMap T V))
    (α : V) (ϖ u : T) (m k : ℕ) (hϖ : Irreducible ϖ) (hu : IsUnit u) (hk : IsUnit (k : T)) (hk0 : 0 < k) (hm0 : 0 < m)
    (hα : α ^ (m * k) = algebraMap T V (u * ϖ ^ k))
    (hgen : ∀ v : V, ∃ f g : Polynomial T, Polynomial.aeval α g ≠ 0 ∧ Polynomial.aeval α g * v = Polynomial.aeval α f) :
    Algebra.IsSeparable (IsLocalRing.ResidueField T) (IsLocalRing.ResidueField V) := by
  obtain ⟨γ, hγu, hαγ, hγk⟩ := GlobalTheory.T.dvr_exists_unit_pow_eq_mul_uniformizer T V hinj α ϖ u m k hϖ hu hk0 hα
  have hK := GlobalTheory.T.kummer_aeval_valuation_dvr T V hinj γ ϖ u k hϖ hu hk hk0 hγk
  have hres := GlobalTheory.T.kummer_residue_mem_adjoin_unit T V hinj α γ ϖ m hϖ hm0 hγu hαγ hK hgen
  set g := IsLocalRing.residue V γ
  have hsepg : IsSeparable (IsLocalRing.ResidueField T) g := by
    have hroot : Polynomial.aeval g (Polynomial.X ^ k - Polynomial.C (IsLocalRing.residue T u)) = 0 := by
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, g]
      rw [← map_pow, hγk]
      rw [sub_eq_zero]
      rfl
    have hsep : (Polynomial.X ^ k - Polynomial.C (IsLocalRing.residue T u)).Separable := by
      apply Polynomial.separable_X_pow_sub_C
      · have := hk.map (IsLocalRing.residue T)
        simpa using this.ne_zero
      · exact (hu.map (IsLocalRing.residue T)).ne_zero
    exact hsep.of_dvd (minpoly.dvd _ _ hroot)
  have htop : IntermediateField.adjoin (IsLocalRing.ResidueField T) {g} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective x
    exact hres v
  have hS := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsepg
  refine ⟨fun x => ?_⟩
  have hx : x ∈ IntermediateField.adjoin (IsLocalRing.ResidueField T) {g} := by rw [htop]; trivial
  have h := Algebra.IsSeparable.isSeparable (IsLocalRing.ResidueField T)
    (⟨x, hx⟩ : IntermediateField.adjoin (IsLocalRing.ResidueField T) {g})
  unfold IsSeparable at h ⊢
  rwa [IntermediateField.minpoly_eq] at h
end GlobalTheory

namespace GlobalTheory

theorem abhyankar_residueField_isSeparable : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    ∀ [Q.LiesOver (maximalIdeal D)],
    Algebra.IsSeparable (D ⧸ maximalIdeal D) (integralClosure D (TensorProduct S D L) ⧸ Q) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hD hπ he hram hsep _ _ Q _ _
  obtain ⟨φ⟩ := hD
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at he
    · exact h
  haveI : Module.Finite S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) :=
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne')).finite
  haveI : Module.Finite S D := Module.Finite.equiv φ.symm.toLinearEquiv
  haveI : Algebra.IsIntegral S D := inferInstance
  haveI : Algebra.IsIntegral D (integralClosure D (TensorProduct S D L)) := inferInstance
  haveI : Algebra.IsIntegral S (integralClosure D (TensorProduct S D L)) := Algebra.IsIntegral.trans D
  haveI : Algebra.IsIntegral (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
    Algebra.IsIntegral.tower_top S
  set P : Ideal (integralClosure S L) := Q.under (integralClosure S L) with hPdef
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  haveI : P.LiesOver (maximalIdeal S) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  obtain ⟨hVd, hVdvr⟩ := GlobalTheory.T.localization_normalization_rootAdjoin_isDVR S K L π e D ⟨φ⟩ hπ he Q
  have hinj := GlobalTheory.T.integralClosure_tensor_localization_injective' S K L π e D ⟨φ⟩ hπ he Q
  have hπP : algebraMap S (integralClosure S L) π ∈ P :=
    (Ideal.mem_of_liesOver P (maximalIdeal S) π).mp ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)
  obtain ⟨ϖ, hϖ, u', hπu'⟩ := GlobalTheory.T.uniformizer_eq_pow_ramificationIdx_mul_unit_integralClosure S K L π e D P hπ hπP
  set u : Localization.AtPrime P := (u' : Localization.AtPrime P) with hu_def
  have hu : IsUnit u := u'.isUnit
  have hπu : algebraMap S (Localization.AtPrime P) π = u * ϖ ^ P.ramificationIdx S := by
    rw [hπu', mul_comm]
  have hk0 : 0 < P.ramificationIdx S := by
    rcases Nat.eq_zero_or_pos (P.ramificationIdx S) with h | h
    · exfalso
      have hmem : algebraMap S (Localization.AtPrime P) π ∈ maximalIdeal (Localization.AtPrime P) := by
        rw [IsScalarTower.algebraMap_apply S (integralClosure S L) (Localization.AtPrime P)]
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hπP
      rw [hπu, h, pow_zero, mul_one] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).1 hmem hu
    · exact h
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) := by
    show IsLocalHom (Localization.localRingHom _ _ _ _)
    infer_instance
  have hdvd : P.ramificationIdx S ∣ e := hram P hPmax
  have hmk : e / P.ramificationIdx S * P.ramificationIdx S = e := Nat.div_mul_cancel hdvd
  have hm0 : 0 < e / P.ramificationIdx S := Nat.div_pos (Nat.le_of_dvd he0 hdvd) hk0
  have hk : IsUnit ((P.ramificationIdx S : ℕ) : Localization.AtPrime P) := by
    have h1 : IsUnit ((e : ℕ) : Localization.AtPrime P) := by
      simpa using he.map (algebraMap S (Localization.AtPrime P))
    rw [← hmk, Nat.cast_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  set t : D := φ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)) with ht_def
  have ht : t ^ e = algebraMap S D π := by
    have h0 : (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)) ^ e =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) π := by
      have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π)
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
      rw [sub_eq_zero] at h
      rw [h, AdjoinRoot.algebraMap_eq]
    rw [ht_def, ← map_pow, h0, AlgEquiv.commutes]
  have hα : (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
      (algebraMap D _ t)) ^ (e / P.ramificationIdx S * P.ramificationIdx S) =
      algebraMap (Localization.AtPrime P) (Localization.AtPrime Q) (u * ϖ ^ P.ramificationIdx S) := by
    rw [hmk, ← hπu, ← map_pow, ← map_pow, ht]
    rw [← IsScalarTower.algebraMap_apply S (Localization.AtPrime P) (Localization.AtPrime Q)]
    rw [← IsScalarTower.algebraMap_apply S D (integralClosure D (TensorProduct S D L))]
    rw [← IsScalarTower.algebraMap_apply S (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)]
  have hST : ∀ s : S, s ≠ 0 → algebraMap S (Localization.AtPrime P) s ≠ 0 := by
    intro s hs h
    have hSL : Function.Injective (algebraMap S L) := by
      rw [IsScalarTower.algebraMap_eq S K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
    have hSO : Function.Injective (algebraMap S (integralClosure S L)) := by
      intro a b hab
      apply hSL
      have := congrArg (fun x : integralClosure S L => (x : L)) hab
      simpa using this
    have hOT : Function.Injective (algebraMap (integralClosure S L) (Localization.AtPrime P)) :=
      IsLocalization.injective _ (P.primeCompl_le_nonZeroDivisors)
    rw [IsScalarTower.algebraMap_apply S (integralClosure S L) (Localization.AtPrime P)] at h
    exact hs (hSO (hOT (h.trans (map_zero _).symm) |>.trans (map_zero _).symm))
  have hpoly : ∀ f : Polynomial (integralClosure S L),
      Polynomial.aeval (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap D _ t)) (f.map (algebraMap (integralClosure S L) (Localization.AtPrime P))) =
      algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (Polynomial.aeval (algebraMap D _ t) f) := by
    intro f
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply]
  have hgen : ∀ v : Localization.AtPrime Q, ∃ f g : Polynomial (Localization.AtPrime P),
      Polynomial.aeval (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap D _ t)) g ≠ 0 ∧
      Polynomial.aeval (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap D _ t)) g * v =
      Polynomial.aeval (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap D _ t)) f := by
    intro v
    obtain ⟨⟨b, c⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl v
    obtain ⟨fb, sb, hsb, hb⟩ := GlobalTheory.T.exists_mul_eq_aeval_root_normalisation S K L π e D φ b
    obtain ⟨fc, sc, hsc, hc⟩ := GlobalTheory.T.exists_mul_eq_aeval_root_normalisation S K L π e D φ c.1
    refine ⟨Polynomial.C (algebraMap S _ sc) * fb.map (algebraMap (integralClosure S L) (Localization.AtPrime P)),
      Polynomial.C (algebraMap S _ sb) * fc.map (algebraMap (integralClosure S L) (Localization.AtPrime P)), ?_, ?_⟩
    · rw [map_mul, Polynomial.aeval_C, hpoly, ← hc]
      refine mul_ne_zero ?_ ?_
      · rw [← IsScalarTower.algebraMap_apply]
        rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime P) (Localization.AtPrime Q)]
        exact fun h => hST sb hsb (hinj (h.trans (map_zero _).symm))
      · rw [map_mul]
        refine mul_ne_zero ?_ (IsLocalization.map_units (Localization.AtPrime Q) c).ne_zero
        rw [← IsScalarTower.algebraMap_apply]
        rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime P) (Localization.AtPrime Q)]
        exact fun h => hST sc hsc (hinj (h.trans (map_zero _).symm))
    · dsimp only
      rw [map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, hpoly, hpoly, ← hb, ← hc, map_mul, map_mul]
      simp only [← IsScalarTower.algebraMap_apply S (Localization.AtPrime P) (Localization.AtPrime Q)]
      simp only [IsScalarTower.algebraMap_apply S (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)]
      have hm := IsLocalization.mk'_spec (Localization.AtPrime Q) b c
      linear_combination (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap S _ sb) * algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap S _ sc)) * hm
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  haveI : FaithfulSMul S (integralClosure S L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have hSL : Function.Injective (algebraMap S L) := by
      rw [IsScalarTower.algebraMap_eq S K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
    intro a b hab
    apply hSL
    have := congrArg (fun x : integralClosure S L => (x : L)) hab
    simpa using this
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field S) P
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hP0 _
  have hsepV := residueField_isSeparable_of_kummer_root (Localization.AtPrime P) (Localization.AtPrime Q) hinj
    (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q) (algebraMap D _ t))
    ϖ u (e / P.ramificationIdx S) (P.ramificationIdx S) hϖ hu hk hk0 hm0 hα hgen
  have h1 : Algebra.IsSeparable P.ResidueField Q.ResidueField := hsepV
  have h2 : Algebra.IsSeparable (integralClosure S L ⧸ P) (integralClosure D (TensorProduct S D L) ⧸ Q) :=
    Algebra.isSeparable_residueField_iff.mp h1
  have h3 : Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P) := hsep P hPmax
  letI := Ideal.Quotient.field (maximalIdeal S)
  letI := Ideal.Quotient.field (maximalIdeal D)
  letI := Ideal.Quotient.field P
  letI := Ideal.Quotient.field Q
  haveI : Q.LiesOver (maximalIdeal S) := Ideal.LiesOver.trans Q P (maximalIdeal S)
  haveI : IsScalarTower (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)
      (integralClosure D (TensorProduct S D L) ⧸ Q) := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [← IsScalarTower.algebraMap_apply]
  haveI h4 : Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure D (TensorProduct S D L) ⧸ Q) :=
    Algebra.IsSeparable.trans (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P) _
  haveI : (maximalIdeal D).LiesOver (maximalIdeal S) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal D))).symm⟩
  haveI : IsScalarTower (S ⧸ maximalIdeal S) (D ⧸ maximalIdeal D)
      (integralClosure D (TensorProduct S D L) ⧸ Q) := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [← IsScalarTower.algebraMap_apply]
  exact Algebra.isSeparable_tower_top_of_isSeparable (S ⧸ maximalIdeal S) (D ⧸ maximalIdeal D) _
end GlobalTheory
