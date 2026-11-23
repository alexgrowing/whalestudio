import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.RingAFacts

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

namespace KF

section Norms

variable (l : ℕ) [hl : Fact l.Prime]

lemma norm_l_eq : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h1 : (((l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [← h1, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  first
    | exact Padic.norm_p
    | simp [Padic.norm_p]

lemma l_pos_real : (0 : ℝ) < (l : ℝ) := by
  exact_mod_cast hl.out.pos

lemma l_inv_lt_one : (l : ℝ)⁻¹ < 1 := by
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)

variable {l}

lemma norm_pow_add_eq_one {a b : ℂ_[l]} (ha : ‖a‖ = 1) (hb : ‖b‖ ≤ 1) :
    ‖a ^ l + (l : ℂ_[l]) * b‖ = 1 := by
  have h1 : ‖a ^ l‖ = 1 := by rw [norm_pow, ha, one_pow]
  have h2 : ‖(l : ℂ_[l]) * b‖ < 1 := by
    rw [norm_mul, norm_l_eq]
    calc (l : ℝ)⁻¹ * ‖b‖ ≤ (l : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (l_pos_real l).le)
      _ < 1 := by rw [mul_one]; exact l_inv_lt_one l
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2.ne'), h1]
  exact max_eq_left h2.le

lemma norm_pow_add_lt_one {a b : ℂ_[l]} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    ‖a ^ l + (l : ℂ_[l]) * b‖ < 1 := by
  have h1 : ‖a ^ l‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg a) ha hl.out.ne_zero
  have h2 : ‖(l : ℂ_[l]) * b‖ < 1 := by
    rw [norm_mul, norm_l_eq]
    calc (l : ℝ)⁻¹ * ‖b‖ ≤ (l : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (l_pos_real l).le)
      _ < 1 := by rw [mul_one]; exact l_inv_lt_one l
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

lemma norm_eq_of_pow_sub {a b : ℂ_[l]} {N : ℕ} (hN : N ≠ 0) (ha : ‖a‖ < 1)
    (h : a ^ (N + 1) - a = (l : ℂ_[l]) * b) : ‖a‖ = (l : ℝ)⁻¹ * ‖b‖ := by
  have hN1 : ‖a ^ N‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg a) ha hN
  have h1 : ‖a ^ N - 1‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hN1.ne), norm_neg, norm_one]
    exact max_eq_right hN1.le
  have h2 : a ^ (N + 1) - a = a * (a ^ N - 1) := by ring
  have h3 := congrArg norm h
  rw [h2, norm_mul, h1, mul_one, norm_mul, norm_l_eq] at h3
  exact h3

end Norms

end KF

open KF

theorem FrobAIsom_of : RingAFacts → FrobAIsom := by
  intro hA l hl σ0 hσ
  obtain ⟨hle, hpow⟩ := hA l
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hlpos : (0 : ℝ) < l := by linarith
  have hl0 : (l : ℝ) ≠ 0 := hlpos.ne'

  have hform : ∀ x : ringA l, ∃ y : ringA l,
      ((σ0 x : ringA l) : ℂ_[l]) = (x : ℂ_[l]) ^ l + (l : ℂ_[l]) * (y : ℂ_[l]) := by
    intro x
    obtain ⟨y, hy⟩ := hσ x
    refine ⟨y, ?_⟩
    have h := congrArg Subtype.val hy
    push_cast at h
    linear_combination h
  have hsm : ∀ x : ringA l, ‖(x : ℂ_[l])‖ < 1 → ‖((σ0 x : ringA l) : ℂ_[l])‖ < 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hform x
    rw [hy]
    exact norm_pow_add_lt_one hx (hle _ y.2)
  have hun : ∀ x : ringA l, ‖(x : ℂ_[l])‖ = 1 → ‖((σ0 x : ringA l) : ℂ_[l])‖ = 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hform x
    rw [hy]
    exact norm_pow_add_eq_one hx (hle _ y.2)

  have hrel : ∀ x : ringA l, ‖(x : ℂ_[l])‖ < 1 → ∃ y : ringA l,
      ‖(x : ℂ_[l])‖ = (l : ℝ)⁻¹ * ‖(y : ℂ_[l])‖ ∧
      ‖((σ0 x : ringA l) : ℂ_[l])‖ = (l : ℝ)⁻¹ * ‖((σ0 y : ringA l) : ℂ_[l])‖ := by
    intro x hx
    obtain ⟨f, hf, y, hy, hxy⟩ := hpow (x : ℂ_[l]) x.2
    have hN : l ^ f - 1 ≠ 0 := by
      have : 2 ≤ l ^ f := le_trans hl.out.two_le (Nat.le_self_pow hf.ne' l)
      omega
    have hN1 : l ^ f - 1 + 1 = l ^ f := Nat.sub_add_cancel (Nat.one_le_pow _ _ hl.out.pos)
    have e : x ^ (l ^ f) - x = (l : ringA l) * ⟨y, hy⟩ := Subtype.ext (by push_cast; exact hxy)
    have e2 := congrArg (fun z => ((σ0 z : ringA l) : ℂ_[l])) e
    simp only [map_sub, map_pow, map_mul, map_natCast] at e2
    push_cast at e2
    refine ⟨⟨y, hy⟩, ?_, ?_⟩
    · apply norm_eq_of_pow_sub hN hx
      rw [hN1]
      exact hxy
    · apply norm_eq_of_pow_sub hN (hsm x hx)
      rw [hN1]
      exact e2

  have key : ∀ k : ℕ, ∀ x : ringA l, ((l : ℝ)⁻¹) ^ k < l * ‖(x : ℂ_[l])‖ →
      ‖((σ0 x : ringA l) : ℂ_[l])‖ = ‖(x : ℂ_[l])‖ := by
    intro k
    induction k with
    | zero =>
      intro x hx
      rcases (hle _ x.2).lt_or_eq with h | h
      · exfalso
        obtain ⟨y, hy1, -⟩ := hrel x h
        have hy := hle _ y.2
        rw [pow_zero] at hx
        have hxy : (l : ℝ) * ‖(x : ℂ_[l])‖ = ‖(y : ℂ_[l])‖ := by
          rw [hy1]
          field_simp
        linarith
      · rw [h]
        exact hun x h
    | succ k ih =>
      intro x hx
      rcases (hle _ x.2).lt_or_eq with h | h
      · obtain ⟨y, hy1, hy2⟩ := hrel x h
        have hyx : ‖(y : ℂ_[l])‖ = l * ‖(x : ℂ_[l])‖ := by
          rw [hy1]
          field_simp
        have hk : ((l : ℝ)⁻¹) ^ k < l * ‖(y : ℂ_[l])‖ := by
          rw [hyx]
          rw [pow_succ] at hx
          have h2 := mul_lt_mul_of_pos_left hx hlpos
          calc ((l : ℝ)⁻¹) ^ k = l * (((l : ℝ)⁻¹) ^ k * (l : ℝ)⁻¹) := by field_simp
            _ < l * (l * ‖(x : ℂ_[l])‖) := h2
        rw [hy2, ih y hk, hy1]
      · rw [h]
        exact hun x h
  intro x
  by_cases hx0 : ‖(x : ℂ_[l])‖ = 0
  · have hx : x = 0 := Subtype.ext (by simpa using hx0)
    subst hx
    simp
  · have hpos : 0 < (l : ℝ) * ‖(x : ℂ_[l])‖ :=
      mul_pos hlpos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0))
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
    exact key k x hk

namespace KF

section Extend

variable (l : ℕ) [hl : Fact l.Prime]

lemma ringA_le_ringB : ringA l ≤ ringB l := Subring.le_topologicalClosure _

def incAB : ringA l →+* ringB l := Subring.inclusion (ringA_le_ringB l)

lemma incAB_coe (x : ringA l) : ((incAB l x : ringB l) : ℂ_[l]) = x := rfl

lemma incAB_unif : IsUniformInducing (incAB l) := by
  have h1 : IsUniformInducing ((↑) : ringB l → ℂ_[l]) := isUniformEmbedding_subtype_val.isUniformInducing
  rw [← h1.of_comp_iff]
  exact isUniformEmbedding_subtype_val.isUniformInducing

lemma incAB_dense : DenseRange (incAB l) := by
  unfold DenseRange
  rw [Subtype.dense_iff]
  intro x hx
  have hsub : (ringA l : Set ℂ_[l]) ⊆ Subtype.val '' Set.range (incAB l) :=
    fun y hy => ⟨incAB l ⟨y, hy⟩, ⟨_, rfl⟩, rfl⟩
  exact closure_mono hsub hx

variable {l}
variable (σ0 : ringA l →+* ringA l) (hiso : ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖)

def sigF : ringA l →+* ℂ_[l] := (ringA l).subtype.comp σ0

include hiso in
lemma sigF_unif : UniformContinuous (sigF σ0) := by
  apply Isometry.uniformContinuous
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  exact hiso x

def sig1 : ringB l →+* ℂ_[l] :=
  IsDenseInducing.extendRingHom (incAB_unif l) (incAB_dense l) (sigF_unif σ0 hiso)

lemma frobenius_extension_continuous : Continuous (sig1 σ0 hiso) :=
  (uniformContinuous_uniformly_extend (incAB_unif l) (incAB_dense l) (sigF_unif σ0 hiso)).continuous

lemma frobenius_extension_on_inclusion (a : ringA l) : sig1 σ0 hiso (incAB l a) = (σ0 a : ℂ_[l]) :=
  uniformly_extend_of_ind (incAB_unif l) (incAB_dense l) (sigF_unif σ0 hiso) a

lemma frobenius_extension_mem (x : ringB l) : sig1 σ0 hiso x ∈ ringB l := by
  refine (incAB_dense l).induction_on x ?_ ?_
  · exact IsClosed.preimage (frobenius_extension_continuous σ0 hiso) (Subring.isClosed_topologicalClosure (ringA l))
  · intro a
    rw [frobenius_extension_on_inclusion]
    exact ringA_le_ringB l (σ0 a).2

lemma frobenius_extension_congruence (hA : ∀ x ∈ ringA l, ‖x‖ ≤ 1)
    (hσ : ∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y) (x : ringB l) :
    ‖sig1 σ0 hiso x - (x : ℂ_[l]) ^ l‖ ≤ (l : ℝ)⁻¹ := by
  refine (incAB_dense l).induction_on x ?_ ?_
  · exact isClosed_le
      (continuous_norm.comp ((frobenius_extension_continuous σ0 hiso).sub (continuous_subtype_val.pow l))) continuous_const
  · intro a
    rw [frobenius_extension_on_inclusion, incAB_coe]
    obtain ⟨y, hy⟩ := hσ a
    have h := congrArg Subtype.val hy
    push_cast at h
    rw [h, norm_mul, norm_l_eq l]
    calc (l : ℝ)⁻¹ * ‖(y : ℂ_[l])‖ ≤ (l : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hA _ y.2) (inv_nonneg.mpr (l_pos_real l).le)
      _ = (l : ℝ)⁻¹ := mul_one _

def jBK (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) : ringB l →+* MaximalUnramifiedExtension l :=
  (ringB l).subtype.codRestrict (MaximalUnramifiedExtension l) (fun x => by
    rw [Subring.subtype_apply]
    exact ((hB x).1 x.2).1)

set_option maxHeartbeats 800000 in

lemma jBK_coe (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) (x : ringB l) :
    ((jBK hB x : MaximalUnramifiedExtension l) : ℂ_[l]) = x := by
  exact RingHom.codRestrict_apply _ _ _ x

lemma jBK_inj (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) :
    Function.Injective (jBK hB) := by
  intro x y h
  apply Subtype.ext
  rw [← jBK_coe hB x, ← jBK_coe hB y, h]

lemma l_ne_zero_Kur : (l : MaximalUnramifiedExtension l) ≠ 0 := by
  intro h
  have h2 := congrArg (fun z : MaximalUnramifiedExtension l => (z : ℂ_[l])) h
  push_cast at h2
  have h3 := norm_l_eq l
  rw [h2, norm_zero] at h3
  exact (inv_pos.mpr (l_pos_real l)).ne h3

lemma jBK_surj (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) (z : MaximalUnramifiedExtension l) :
    ∃ (k : ℕ) (b : ringB l), z * (l : MaximalUnramifiedExtension l) ^ k = jBK hB b := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖(z : ℂ_[l])‖ (by exact_mod_cast hl.out.one_lt : (1 : ℝ) < l)
  have hmem : ((z * (l : MaximalUnramifiedExtension l) ^ k : MaximalUnramifiedExtension l) : ℂ_[l]) ∈ ringB l := by
    rw [hB]
    refine ⟨(z * (l : MaximalUnramifiedExtension l) ^ k).2, ?_⟩
    push_cast
    rw [norm_mul, norm_pow, norm_l_eq l, inv_pow, ← div_eq_mul_inv]
    exact (div_le_one (pow_pos (l_pos_real l) k)).mpr hk.le
  exact ⟨k, ⟨_, hmem⟩, Subtype.ext (jBK_coe hB ⟨_, hmem⟩).symm⟩

lemma jBK_away (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1) :
    @IsLocalization.Away (ringB l) _ (l : ringB l) (MaximalUnramifiedExtension l) _ (jBK hB).toAlgebra := by
  letI := (jBK hB).toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    show IsUnit (jBK hB ((l : ringB l) ^ n))
    rw [map_pow, map_natCast]
    exact (IsUnit.mk0 _ l_ne_zero_Kur).pow n
  · intro z
    obtain ⟨k, b, hb⟩ := jBK_surj hB z
    refine ⟨⟨b, ⟨(l : ringB l) ^ k, k, rfl⟩⟩, ?_⟩
    show z * jBK hB ((l : ringB l) ^ k) = jBK hB b
    rw [map_pow, map_natCast]
    exact hb
  · intro x y h
    exact ⟨1, by rw [jBK_inj hB h]⟩

lemma exists_ext (hB : ∀ x : ℂ_[l], x ∈ ringB l ↔ x ∈ MaximalUnramifiedExtension l ∧ ‖x‖ ≤ 1)
    (g : ringB l →+* ℂ_[l]) (hg : ∀ x, g x ∈ ringB l) :
    ∃ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, ∀ (x : MaximalUnramifiedExtension l) (hx : (x : ℂ_[l]) ∈ ringB l),
      (σ x : ℂ_[l]) = g ⟨x, hx⟩ := by
  letI := (jBK hB).toAlgebra
  haveI := jBK_away hB
  let ψ : ringB l →+* MaximalUnramifiedExtension l := (jBK hB).comp (g.codRestrict (ringB l) hg)
  have hu : IsUnit (ψ (l : ringB l)) := by
    rw [map_natCast]
    exact IsUnit.mk0 _ l_ne_zero_Kur
  refine ⟨IsLocalization.Away.lift (l : ringB l) hu, fun x hx => ?_⟩
  have key : IsLocalization.Away.lift (l : ringB l) hu (algebraMap (ringB l) (MaximalUnramifiedExtension l) ⟨x, hx⟩) =
      ψ ⟨x, hx⟩ := by
    first
      | exact IsLocalization.Away.lift_eq (S := MaximalUnramifiedExtension l) (l : ringB l) hu ⟨x, hx⟩
      | exact IsLocalization.lift_eq _ _
      | simp
  have hx' : algebraMap (ringB l) (MaximalUnramifiedExtension l) ⟨x, hx⟩ = x := Subtype.ext (jBK_coe hB _)
  rw [hx'] at key
  rw [key]
  rfl

end Extend

end KF

theorem KurFrob_of : FrobA → FrobAIsom → KurIntegers → KurUnram → KurFrob := by
  intro hF hI hK hU l hl hl2
  obtain ⟨σ0, hmu, hσ⟩ := hF l
  have hiso := hI l σ0 hσ
  obtain ⟨hB, -, -⟩ := hK l
  have hA : ∀ x ∈ ringA l, ‖x‖ ≤ 1 := fun x hx => ((hB x).1 (ringA_le_ringB l hx)).2
  obtain ⟨σ, hσe⟩ := exists_ext hB (sig1 σ0 hiso) (frobenius_extension_mem σ0 hiso)
  refine ⟨σ, ⟨hl.out, hl2, ?_, ?_, ?_⟩, ?_⟩
  · show ‖((l : MaximalUnramifiedExtension l) : ℂ_[l])‖ = _
    push_cast
    exact norm_l_eq l
  · intro a ha
    obtain ⟨k, hk⟩ := hU l (a : ℂ_[l]) a.2 (fun h => ha (Subtype.ext h))
    refine ⟨-k, ?_⟩
    show ‖(a : ℂ_[l])‖ = _
    rw [hk, norm_l_eq l, inv_zpow']
  · intro a ha
    have ha' : (a : ℂ_[l]) ∈ ringB l := (hB a).2 ⟨a.2, ha⟩
    have h1 := hσe a ha'
    show ‖((σ a - a ^ l : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ _
    push_cast
    rw [h1]
    exact frobenius_extension_congruence σ0 hiso hA hσ ⟨a, ha'⟩
  · intro ζ hζ
    have hζA : (ζ : ℂ_[l]) ∈ ringA l := Subring.subset_closure hζ
    have hζB := ringA_le_ringB l hζA
    apply Subtype.ext
    rw [hσe ζ hζB]
    have he : (⟨(ζ : ℂ_[l]), hζB⟩ : ringB l) = incAB l ⟨ζ, hζA⟩ := rfl
    rw [he, frobenius_extension_on_inclusion, hmu ⟨ζ, hζA⟩ hζ]
    simp

end Formalism.L2.Th1.D
