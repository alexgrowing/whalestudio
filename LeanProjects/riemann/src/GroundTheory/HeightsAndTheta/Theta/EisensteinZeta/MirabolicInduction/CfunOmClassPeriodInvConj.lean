import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmEtaLogPeriodNegConjPf
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open UpperHalfPlane ModularGroup ModularForm Complex NumberField Module
open scoped Real Modular MatrixGroups nonZeroDivisors

namespace ClassPeriodInv

variable {K : Type*} [Field K] [NumberField K]

theorem exists_conj_aut (hK : finrank ℚ K = 2) (σ : K →+* ℂ) :
    ∃ g : K ≃ₐ[ℚ] K, ∀ x, σ (g x) = starRingEnd ℂ (σ x) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) σ
    ((starRingEnd ℂ).comp σ) (Subsingleton.elim _ _)
  exact ⟨g.symm, fun x => RingHom.congr_fun hg x⟩

open Classical in

theorem norm_eq_mul_conj (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (g : K ≃ₐ[ℚ] K) (hg : ∀ x, σ (g x) = starRingEnd ℂ (σ x)) (x : K) :
    algebraMap ℚ K (Algebra.norm ℚ x) = x * g x := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hg1 : g ≠ 1 := by
    rintro rfl
    obtain ⟨y, hy⟩ := hσ
    have := hg y
    simp only [AlgEquiv.one_apply] at this
    exact hy (Complex.conj_eq_iff_im.mp this.symm)
  have hcard : Fintype.card Gal(K/ℚ) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hK]
  have huniv : (Finset.univ : Finset Gal(K/ℚ)) = {1, g} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair (Ne.symm hg1)]
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair (Ne.symm hg1)]
  rfl

abbrev intAut (g : K ≃ₐ[ℚ] K) : 𝓞 K ≃ₐ[ℤ] 𝓞 K :=
  (RingOfIntegers.mapRingEquiv g.toRingEquiv).toIntAlgEquiv

theorem intNorm_eq_mul_conj (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (g : K ≃ₐ[ℚ] K) (hg : ∀ x, σ (g x) = starRingEnd ℂ (σ x)) (x : 𝓞 K) :
    algebraMap ℤ (𝓞 K) (Algebra.intNorm ℤ (𝓞 K) x) = x * intAut g x := by
  apply RingOfIntegers.coe_injective
  have h1 := Algebra.algebraMap_intNorm (A := ℤ) (K := ℚ) (B := 𝓞 K) (L := K) x
  have h2 := norm_eq_mul_conj hK σ hσ g hg (x : K)
  rw [← h1] at h2
  simpa using h2

theorem eq_of_le_of_absNorm_eq {J J' : Ideal (𝓞 K)} (h : J' ≤ J) (hn : Ideal.absNorm J' = Ideal.absNorm J)
    (h0 : Ideal.absNorm J ≠ 0) : J' = J := by
  obtain ⟨M, rfl⟩ := Ideal.dvd_iff_le.mpr h
  rw [map_mul] at hn
  have hM : Ideal.absNorm M = 1 := by
    have : Ideal.absNorm J * Ideal.absNorm M = Ideal.absNorm J * 1 := by rw [hn, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) this
  rw [Ideal.absNorm_eq_one_iff.mp hM, Ideal.mul_top]

theorem mul_map_eq_span_absNorm (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (g : K ≃ₐ[ℚ] K) (hg : ∀ x, σ (g x) = starRingEnd ℂ (σ x)) (I : Ideal (𝓞 K)) :
    I * I.map (intAut g) = Ideal.span {((Ideal.absNorm I : ℤ) : 𝓞 K)} := by
  have hspan : (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((Ideal.absNorm I : ℤ) : 𝓞 K)} := by
    rw [Ideal.relNorm_int, Ideal.map_span, Set.image_singleton]
    simp
  have hle : (Ideal.relNorm ℤ I).map (algebraMap ℤ (𝓞 K)) ≤ I * I.map (intAut g) := by
    have hdef : Ideal.relNorm ℤ I = Ideal.span (Algebra.intNorm ℤ (𝓞 K) '' I) := rfl
    rw [hdef, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, intNorm_eq_mul_conj hK σ hσ g hg y]
    exact Ideal.mul_mem_mul hy (Ideal.mem_map_of_mem _ hy)
  rw [hspan] at hle
  by_cases hI : I = ⊥
  · subst hI
    simp
  have h0 : Ideal.absNorm I ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  refine (eq_of_le_of_absNorm_eq hle ?_ ?_).symm
  · rw [← hspan, Ideal.absNorm_algebraMap, Ideal.absNorm_relNorm, map_mul,
      ← Ideal.absNorm_relNorm (R := ℤ) (I := I.map (intAut g)), Ideal.relNorm_map_algEquiv,
      Ideal.absNorm_relNorm, RingOfIntegers.rank, hK, sq]
  · rw [map_mul, ← Ideal.absNorm_relNorm (R := ℤ) (I := I.map (intAut g)), Ideal.relNorm_map_algEquiv,
      Ideal.absNorm_relNorm]
    exact mul_ne_zero h0 h0

theorem coe_spanSingleton_mul_coeIdeal (c : K) (M : Ideal (𝓞 K)) :
    ((FractionalIdeal.spanSingleton (𝓞 K)⁰ c * (M : FractionalIdeal (𝓞 K)⁰ K) :
      FractionalIdeal (𝓞 K)⁰ K) : Set K) = (fun y : 𝓞 K => c * (y : K)) '' (M : Set (𝓞 K)) := by
  ext x
  simp only [SetLike.mem_coe, FractionalIdeal.mem_singleton_mul, FractionalIdeal.mem_coeIdeal,
    Set.mem_image]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩

theorem exists_inv_eq_conj (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ w : ℂ, w ≠ 0 ∧ σ '' (((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Set K) = (fun z => w * z) '' (starRingEnd ℂ '' (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) :
        Set K))) := by
  obtain ⟨g, hg⟩ := exists_conj_aut hK σ
  obtain ⟨a, I₀, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (I : FractionalIdeal (𝓞 K)⁰ K)
  have hI₀ : I₀ ≠ ⊥ := by
    rintro rfl
    apply I.ne_zero
    rw [hI]
    simp
  set n : 𝓞 K := ((Ideal.absNorm I₀ : ℤ) : 𝓞 K) with hn
  have hn0 : algebraMap (𝓞 K) K n ≠ 0 := by
    have : (Ideal.absNorm I₀ : ℤ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hI₀)
    simpa [hn] using this
  have ha0 : algebraMap (𝓞 K) K a ≠ 0 := by
    simpa using ha
  set A : K := algebraMap (𝓞 K) K a with hA
  set N : K := algebraMap (𝓞 K) K n with hN
  set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ (A / N) *
    ((I₀.map (intAut g) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) with hJdef
  have hIJ : (I : FractionalIdeal (𝓞 K)⁰ K) * J = 1 := by
    rw [hI, hJdef]
    calc _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ (A⁻¹ * (A / N)) *
          ((I₀ * I₀.map (intAut g) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
          rw [FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
          ring
      _ = 1 := by
          rw [mul_map_eq_span_absNorm hK σ hσ g hg, FractionalIdeal.coeIdeal_span_singleton,
            ← hn, FractionalIdeal.spanSingleton_mul_spanSingleton, ← hN,
            show A⁻¹ * (A / N) * N = 1 by field_simp]
          exact FractionalIdeal.spanSingleton_one
  have hJ : ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = J :=
    Units.inv_eq_of_mul_eq_one_right hIJ
  refine ⟨σ (A / N) * starRingEnd ℂ (σ A), ?_, ?_⟩
  · refine mul_ne_zero ?_ ?_
    · exact (map_ne_zero σ).mpr (div_ne_zero ha0 hn0)
    · exact (map_ne_zero _).mpr ((map_ne_zero σ).mpr ha0)
  rw [hJ, hJdef, coe_spanSingleton_mul_coeIdeal, hI, coe_spanSingleton_mul_coeIdeal]
  have hmap : ((I₀.map (intAut g) : Ideal (𝓞 K)) : Set (𝓞 K)) = intAut g '' (I₀ : Set (𝓞 K)) := by
    ext y
    rw [SetLike.mem_coe, Ideal.mem_map_of_equiv]
    rfl
  rw [hmap]
  simp only [Set.image_image]
  refine Set.image_congr fun y _ => ?_
  have hy : ((intAut g y : 𝓞 K) : K) = g (y : K) := rfl
  rw [hy, map_mul, hg]
  simp only [map_mul, map_inv₀]
  have hσA : starRingEnd ℂ (σ A) ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero σ).mpr ha0)
  field_simp

theorem conj_latticeOf (z : ℂ) :
    starRingEnd ℂ '' latticeOf z = latticeOf (-(starRingEnd ℂ z)) := by
  unfold latticeOf
  have h : (starRingEnd ℂ '' ((Submodule.span ℤ ({1, z} : Set ℂ)) : Set ℂ)) =
      ((Submodule.span ℤ ({1, z} : Set ℂ)).map
        ((starRingEnd ℂ).toAddMonoidHom.toIntLinearMap) : Set ℂ) := by
    rw [Submodule.map_coe]
    rfl
  rw [h, Submodule.map_span, Set.image_pair]
  congr 1
  simp only [AddMonoidHom.coe_toIntLinearMap, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    map_one]
  rw [Submodule.span_insert, Submodule.span_insert, ← Submodule.span_neg ({starRingEnd ℂ z} : Set ℂ),
    Set.neg_singleton]

theorem isLatticeParam_conj {Λ : Set ℂ} {τ : ℍ} (h : IsLatticeParam Λ τ) {w : ℂ} (hw : w ≠ 0) :
    IsLatticeParam ((fun z => w * z) '' (starRingEnd ℂ '' Λ)) (negConj τ) := by
  obtain ⟨c, hc, hΛ⟩ := h
  refine ⟨starRingEnd ℂ c / w, div_ne_zero ((map_ne_zero _).mpr hc) hw, ?_⟩
  have hneg : ((negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ (τ : ℂ)) := rfl
  rw [hneg, ← conj_latticeOf, ← hΛ]
  simp only [Set.image_image]
  refine Set.image_congr fun x _ => ?_
  rw [map_mul]
  field_simp

theorem negConj_mem_fd {τ : ℍ} (h : τ ∈ 𝒟) : negConj τ ∈ 𝒟 := by
  have hneg : ((negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ (τ : ℂ)) := rfl
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hneg, Complex.normSq_neg, Complex.normSq_conj]
    exact h1
  · change |((negConj τ : ℍ) : ℂ).re| ≤ 1 / 2
    rw [hneg, Complex.neg_re, Complex.conj_re, abs_neg]
    exact h2

theorem negConj_mem_classReducedParams (hK : finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (A : ClassGroup (𝓞 K)) {τ : ℍ}
    (hτ : τ ∈ classReducedParams σ A) : negConj τ ∈ classReducedParams σ A⁻¹ := by
  obtain ⟨I, hIA, hfd, hpar⟩ := hτ
  obtain ⟨w, hw, hset⟩ := exists_inv_eq_conj hK σ hσ I
  refine ⟨I⁻¹, by rw [map_inv, hIA], negConj_mem_fd hfd, ?_⟩
  rw [hset]
  exact isLatticeParam_conj hpar hw

theorem exists_eq_mul_of_mk_eq {J J' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K J' = ClassGroup.mk K J) :
    ∃ x : K, x ≠ 0 ∧ ((J' : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (fun y => x * y) '' ((J : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
  have h1 : ClassGroup.mk K (J' * J⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.mp h1
  have hP : ((J' * J⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    dsimp only
    rw [FractionalIdeal.coe_spanSingleton]
    exact hx
  have hJ' : (J' : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hP, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply J'.ne_zero
    rw [hJ', FractionalIdeal.spanSingleton_zero, zero_mul]
  refine ⟨x, hx0, ?_⟩
  ext y
  rw [hJ', SetLike.mem_coe, FractionalIdeal.mem_singleton_mul, Set.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem isLatticeParam_mul {Λ : Set ℂ} {τ : ℍ} (h : IsLatticeParam Λ τ) {w : ℂ} (hw : w ≠ 0) :
    IsLatticeParam ((fun z => w * z) '' Λ) τ := by
  obtain ⟨c, hc, hΛ⟩ := h
  refine ⟨c / w, div_ne_zero hc hw, ?_⟩
  rw [← hΛ, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  field_simp

theorem isLatticeParam_of_mem_classReducedParams (σ : K →+* ℂ) {A : ClassGroup (𝓞 K)} {τ : ℍ}
    (hτ : τ ∈ classReducedParams σ A) {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hJ : ClassGroup.mk K J = A) :
    IsLatticeParam (σ '' ((J : FractionalIdeal (𝓞 K)⁰ K) : Set K)) τ := by
  obtain ⟨J', hJ'A, -, hpar⟩ := hτ
  obtain ⟨x, hx, hset⟩ := exists_eq_mul_of_mk_eq (hJ'A.trans hJ.symm)
  have hx' : σ x⁻¹ ≠ 0 := (map_ne_zero σ).mpr (inv_ne_zero hx)
  have hJset : σ '' ((J : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (fun z => σ x⁻¹ * z) '' (σ '' ((J' : FractionalIdeal (𝓞 K)⁰ K) : Set K)) := by
    rw [hset]
    simp only [Set.image_image]
    refine Set.image_congr fun y _ => ?_
    rw [← map_mul, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  rw [hJset]
  exact isLatticeParam_mul hpar hx'

theorem etaPeriod_negConj (τ : ℍ) : etaPeriod (negConj τ) = etaPeriod τ :=
  Real.log_injOn_pos (etaPeriod_pos _) (etaPeriod_pos _) (EtaLogPeriodNegConj.proof τ)

theorem of_classReducedParamsNonempty_classFunctionsWellDefined
    (hne : ClassReducedParamsNonempty.Statement) (hwd : ClassFunctionsWellDefined.Statement) :
    ClassPeriodInv.Statement := by
  intro K _ _ hK σ hσ A
  have hA : classTau σ A ∈ classReducedParams σ A := Classical.epsilon_spec (hne K hK σ hσ A)
  have hB : classTau σ A⁻¹ ∈ classReducedParams σ A⁻¹ :=
    Classical.epsilon_spec (hne K hK σ hσ A⁻¹)
  have h := (hwd K hK σ hσ A⁻¹ _ _ hB (negConj_mem_classReducedParams hK σ hσ A hA)).2
  unfold classPeriod
  rw [h, etaPeriod_negConj]

theorem of_classReducedParamsNonempty_etaPeriodLatticeClass
    (hne : ClassReducedParamsNonempty.Statement) (hlc : EtaPeriodLatticeClass.Statement) :
    ClassPeriodInv.Statement := by
  intro K _ _ hK σ hσ A
  have hA : classTau σ A ∈ classReducedParams σ A := Classical.epsilon_spec (hne K hK σ hσ A)
  have hB : classTau σ A⁻¹ ∈ classReducedParams σ A⁻¹ :=
    Classical.epsilon_spec (hne K hK σ hσ A⁻¹)
  obtain ⟨I, hIA, -⟩ := hA
  have hI' : ClassGroup.mk K I⁻¹ = A⁻¹ := by rw [map_inv, hIA]
  have h1 := isLatticeParam_of_mem_classReducedParams σ hB hI'
  have h2 := isLatticeParam_of_mem_classReducedParams σ
    (negConj_mem_classReducedParams hK σ hσ A (Classical.epsilon_spec (hne K hK σ hσ A))) hI'
  unfold classPeriod
  rw [hlc _ _ _ h1 h2, etaPeriod_negConj]
  rfl

end ClassPeriodInv

end GroundTheory.Heights₂.Theta
