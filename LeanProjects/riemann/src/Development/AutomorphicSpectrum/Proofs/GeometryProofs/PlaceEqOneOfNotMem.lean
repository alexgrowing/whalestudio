import Mathlib
import Formalism.HermitianLattices.StatementLat
import Development.AutomorphicSpectrum.Definitions.SemilocalProjection.HidaSetting
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

open NumberField Matrix IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

noncomputable def gIdx {W : Type} [AddCommGroup W] (A B : AddSubgroup W) : ℝ :=
  Real.log ((B.relIndex A : ℕ) : ℝ) - Real.log ((A.relIndex B : ℕ) : ℝ)

section Index

variable {W : Type} [AddCommGroup W]

theorem gIdx_self (A : AddSubgroup W) : gIdx A A = 0 := by
  simp [gIdx]

theorem gIdx_of_le {A B : AddSubgroup W} (h : B ≤ A) : gIdx A B = Real.log ((B.relIndex A : ℕ) : ℝ) := by
  simp [gIdx, AddSubgroup.relIndex_eq_one.2 h]

theorem gIdx_swap (A B : AddSubgroup W) : gIdx A B = - gIdx B A := by
  simp [gIdx]

private theorem gIdx_eq_lemma {X Y D : AddSubgroup W} (hD : D ≤ X ⊓ Y) (hX : D.relIndex X ≠ 0)
    (hY : D.relIndex Y ≠ 0) :
    gIdx X Y = Real.log (D.relIndex X : ℝ) - Real.log (D.relIndex Y : ℝ) := by
  have e1 : D.relIndex X = D.relIndex (X ⊓ Y) * Y.relIndex X := by
    rw [← AddSubgroup.inf_relIndex_left X Y, AddSubgroup.relIndex_mul_relIndex _ _ _ hD inf_le_left]
  have e2 : D.relIndex Y = D.relIndex (X ⊓ Y) * X.relIndex Y := by
    rw [← AddSubgroup.inf_relIndex_right X Y, AddSubgroup.relIndex_mul_relIndex _ _ _ hD inf_le_right]
  have hd : D.relIndex (X ⊓ Y) ≠ 0 := by
    intro h
    rw [e1, h, zero_mul] at hX
    exact hX rfl
  have h1 : Y.relIndex X ≠ 0 := by
    intro h
    rw [e1, h, mul_zero] at hX
    exact hX rfl
  have h2 : X.relIndex Y ≠ 0 := by
    intro h
    rw [e2, h, mul_zero] at hY
    exact hY rfl
  rw [gIdx, e1, e2]
  push_cast
  rw [Real.log_mul (by exact_mod_cast hd) (by exact_mod_cast h1),
    Real.log_mul (by exact_mod_cast hd) (by exact_mod_cast h2)]
  ring

theorem gIdx_add {A B C : AddSubgroup W} (hAB : A.relIndex B ≠ 0) (hBA : B.relIndex A ≠ 0)
    (hBC : B.relIndex C ≠ 0) (hCB : C.relIndex B ≠ 0) : gIdx A C = gIdx A B + gIdx B C := by
  have hCA : C.relIndex A ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hCB hBA
  have hAC : A.relIndex C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hAB hBC
  have hA : (A ⊓ B ⊓ C).relIndex A ≠ 0 :=
    AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero (by simp) hBA) hCA
  have hB : (A ⊓ B ⊓ C).relIndex B ≠ 0 :=
    AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero hAB (by simp)) hCB
  have hC : (A ⊓ B ⊓ C).relIndex C ≠ 0 :=
    AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero hAC hBC) (by simp)
  rw [gIdx_eq_lemma (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hA hC,
    gIdx_eq_lemma (inf_le_left : A ⊓ B ⊓ C ≤ A ⊓ B) hA hB,
    gIdx_eq_lemma (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hB hC]
  ring

theorem gIdx_map {W' : Type} [AddCommGroup W'] (f : W →+ W') (hf : Function.Injective f)
    (A B : AddSubgroup W) : gIdx (A.map f) (B.map f) = gIdx A B := by
  simp only [gIdx, AddSubgroup.relIndex_map_map_of_injective _ _ hf]

theorem gIdx_frac (Λ : AddSubgroup W) (M a : W →+ W) (hM : Function.Injective M)
    (hc : ∀ x, a (M x) = M (a x)) (h2 : Λ.map a ≤ Λ) (i2 : (Λ.map a).relIndex Λ ≠ 0)
    (h3 : Λ.map (a.comp M) ≤ Λ) (i3 : (Λ.map (a.comp M)).relIndex Λ ≠ 0) :
    gIdx (Λ.map M) Λ =
      Real.log (((Λ.map a).relIndex Λ : ℕ) : ℝ) - Real.log (((Λ.map (a.comp M)).relIndex Λ : ℕ) : ℝ) := by
  have hcomm : Λ.map (a.comp M) = (Λ.map a).map M := by
    rw [AddSubgroup.map_map]
    congr 1
    ext x
    simp [hc]
  have hsub : Λ.map (a.comp M) ≤ Λ.map M := by
    rw [hcomm]
    exact AddSubgroup.map_mono h2
  have iB : (Λ.map (a.comp M)).relIndex (Λ.map M) = (Λ.map a).relIndex Λ := by
    rw [hcomm]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hM
  have h3' : (Λ.map a).map M ≤ Λ := by
    rw [← hcomm]
    exact h3
  rw [gIdx_add (B := Λ.map (a.comp M))
    (by rw [AddSubgroup.relIndex_eq_one.mpr hsub]; exact one_ne_zero) (by rw [iB]; exact i2) i3
    (by rw [AddSubgroup.relIndex_eq_one.mpr h3]; exact one_ne_zero)]
  rw [hcomm, gIdx_map M hM, gIdx_of_le h2, gIdx_swap, gIdx_of_le h3']
  ring

end Index

variable {L : Type} [Field L] [NumberField L]

noncomputable def locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A : Submodule (𝓞 L) W) :
    Submodule (𝓞 L) W :=
  haveI := v.maximalIdeal.isPrime
  Formalism.HermitianLatticesTheory.localization₂ v.maximalIdeal.asIdeal A

theorem mem_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] {v : FinitePlace L} {A : Submodule (𝓞 L) W}
    {x : W} : x ∈ locAt v A ↔ ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ A := (Iff.rfl)

theorem le_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A : Submodule (𝓞 L) W) :
    A ≤ locAt v A := by
  intro x hx
  rw [mem_locAt]
  exact ⟨1, (Ideal.ne_top_iff_one _).mp v.maximalIdeal.isPrime.ne_top, by simpa using hx⟩

theorem locAt_inf {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W) :
    locAt v (A ⊓ B) = locAt v A ⊓ locAt v B := by
  ext x
  simp only [Submodule.mem_inf, mem_locAt]
  constructor
  · rintro ⟨t, ht, hA, hB⟩
    exact ⟨⟨t, ht, hA⟩, ⟨t, ht, hB⟩⟩
  · rintro ⟨⟨s, hs, hA⟩, ⟨t, ht, hB⟩⟩
    refine ⟨s * t, fun h => ?_, ?_, ?_⟩
    · rcases v.maximalIdeal.isPrime.mem_or_mem h with h | h
      · exact hs h
      · exact ht h
    · rw [mul_comm, mul_smul]
      exact A.smul_mem t hA
    · rw [mul_smul]
      exact B.smul_mem s hB

noncomputable def frame {n : ℕ} (T : Matrix (Fin n) (Fin n) L) : Submodule (𝓞 L) (Fin n → L) :=
  Submodule.span (𝓞 L) (Set.range fun k j => T j k)

noncomputable def glued {n : ℕ} (T : FinitePlace L → Matrix (Fin n) (Fin n) L) : Submodule (𝓞 L) (Fin n → L) :=
  ⨅ v, locAt v (frame (T v))

def UnitAt {n : ℕ} (v : FinitePlace L) (T : Matrix (Fin n) (Fin n) L) : Prop :=
  (∀ i j, v (T i j) ≤ 1) ∧ v T.det = 1

theorem place_le_one_iff (v : FinitePlace L) (x : L) : v x ≤ 1 ↔ v.maximalIdeal.valuation L x ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def,
    NNReal.coe_le_one, WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal _)]

theorem exists_denom (v : FinitePlace L) {x : L} (hx : v x ≤ 1) :
    ∃ (s r : 𝓞 L), s ∉ v.maximalIdeal.asIdeal ∧ (s : L) * x = r := by
  rw [place_le_one_iff] at hx
  obtain ⟨n, d, h | h⟩ := v.maximalIdeal.exists_primeCompl_mul_eq_or_mul_eq (K := L) x
  · exact ⟨d, n, d.2, by rw [mul_comm]; exact h⟩
  · refine ⟨n, d, fun hn => ?_, by rw [mul_comm]; exact h⟩
    have h1 := congrArg (v.maximalIdeal.valuation L) h
    rw [map_mul] at h1
    have hd : v.maximalIdeal.valuation L (algebraMap (𝓞 L) L d) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      exact d.2
    have hn' : v.maximalIdeal.valuation L (algebraMap (𝓞 L) L n) < 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hn
    have key : v.maximalIdeal.valuation L x * v.maximalIdeal.valuation L (algebraMap (𝓞 L) L n) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hx) hn'
    rw [h1, hd] at key
    exact lt_irrefl _ key

theorem place_int_le_one (v : FinitePlace L) (r : 𝓞 L) : v (r : L) ≤ 1 := by
  rw [place_le_one_iff]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ r

theorem place_eq_one_of_notMem (v : FinitePlace L) {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) :
    v.maximalIdeal.valuation L (t : L) = 1 :=
  (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 ht

theorem place_sum_le_one (v : FinitePlace L) {ι : Type} (s : Finset ι) (f : ι → L)
    (h : ∀ i ∈ s, v (f i) ≤ 1) : v (∑ i ∈ s, f i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (FinitePlace.add_le v _ _).trans (max_le ?_ ?_)
    · exact h a (Finset.mem_insert_self a s)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem place_mul_le_one (v : FinitePlace L) {a b : L} (ha : v a ≤ 1) (hb : v b ≤ 1) : v (a * b) ≤ 1 := by
  rw [FinitePlace.coe_apply, map_mul]
  rw [FinitePlace.coe_apply] at ha hb
  exact mul_le_one₀ ha (AbsoluteValue.nonneg _ _) hb

variable {n : ℕ}

theorem mem_frame {T : Matrix (Fin n) (Fin n) L} {x : Fin n → L} :
    x ∈ frame T ↔ ∃ z : Fin n → 𝓞 L, x = T *ᵥ fun i => (z i : L) := by
  rw [frame, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    ext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]

theorem exists_common_denom (v : FinitePlace L) {y : Fin n → L} (hy : ∀ i, v (y i) ≤ 1) :
    ∃ (t : 𝓞 L) (z : Fin n → 𝓞 L), t ∉ v.maximalIdeal.asIdeal ∧ ∀ i, (t : L) * y i = z i := by
  choose s r hs hr using fun i => exists_denom v (hy i)
  classical
  haveI := v.maximalIdeal.isPrime
  refine ⟨∏ j, s j, fun i => (∏ j ∈ Finset.univ.erase i, s j) * r i, ?_, fun i => ?_⟩
  · intro hmem
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hs j hj
  · push_cast
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_assoc, hr i]

theorem mem_locAt_frame {v : FinitePlace L} {T : Matrix (Fin n) (Fin n) L} {x : Fin n → L} :
    x ∈ locAt v (frame T) ↔ ∃ y : Fin n → L, (∀ i, v (y i) ≤ 1) ∧ x = T *ᵥ y := by
  constructor
  · intro hx
    rw [mem_locAt] at hx
    obtain ⟨t, ht, htx⟩ := hx
    rw [mem_frame] at htx
    obtain ⟨z, hz⟩ := htx
    have ht0 : (t : L) ≠ 0 := by
      intro h0
      apply ht
      have : t = 0 := by exact_mod_cast h0
      rw [this]
      exact Ideal.zero_mem _
    refine ⟨fun i => (t : L)⁻¹ * z i, fun i => ?_, ?_⟩
    · rw [place_le_one_iff, map_mul, map_inv₀, place_eq_one_of_notMem v ht, inv_one, one_mul]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
    · have e : (fun i => (t : L)⁻¹ * (z i : L)) = (t : L)⁻¹ • (fun i => (z i : L)) := by
        ext i
        simp
      rw [e, Matrix.mulVec_smul, ← hz]
      ext j
      simp [Algebra.smul_def, ht0]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, z, ht, hz⟩ := exists_common_denom v hy
    rw [mem_locAt]
    refine ⟨t, ht, ?_⟩
    rw [mem_frame]
    refine ⟨z, ?_⟩
    rw [← Matrix.mulVec_smul]
    congr 1
    ext i
    rw [Pi.smul_apply, Algebra.smul_def]
    exact hz i

theorem mem_locAt_frame_one {v : FinitePlace L} {x : Fin n → L} :
    x ∈ locAt v (frame (1 : Matrix (Fin n) (Fin n) L)) ↔ ∀ i, v (x i) ≤ 1 := by
  rw [mem_locAt_frame]
  simp

theorem mem_frame_one {x : Fin n → L} :
    x ∈ frame (1 : Matrix (Fin n) (Fin n) L) ↔ ∀ i, ∃ r : 𝓞 L, x i = r := by
  rw [mem_frame]
  simp only [Matrix.one_mulVec]
  constructor
  · rintro ⟨z, rfl⟩ i
    exact ⟨z i, rfl⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext hz⟩

theorem iInf_locAt_frame_one : ⨅ v : FinitePlace L, locAt v (frame (1 : Matrix (Fin n) (Fin n) L)) = frame 1 := by
  ext x
  rw [Submodule.mem_iInf, mem_frame_one]
  simp only [mem_locAt_frame_one]
  constructor
  · intro h i
    obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) (K := L)
      (x := x i) (h := fun w => by
        have := (place_le_one_iff (FinitePlace.mk w) (x i)).mp (h (FinitePlace.mk w) i)
        rwa [FinitePlace.maximalIdeal_mk] at this)
    exact ⟨r, hr.symm⟩
  · intro h w i
    obtain ⟨r, hr⟩ := h i
    rw [hr]
    exact place_int_le_one w r

theorem unitAt_one (v : FinitePlace L) : UnitAt v (1 : Matrix (Fin n) (Fin n) L) := by
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.one_apply]
    split_ifs
    · rw [FinitePlace.coe_apply, map_one]
    · rw [FinitePlace.coe_apply, map_zero]
      exact zero_le_one
  · rw [Matrix.det_one, FinitePlace.coe_apply, map_one]

private theorem adj_le_lemma (v : FinitePlace L) {T : Matrix (Fin n) (Fin n) L} (h : ∀ i j, v (T i j) ≤ 1)
    (i j : Fin n) : v (T.adjugate i j) ≤ 1 := by
  let S := (v.maximalIdeal.valuation L).valuationSubring
  let T' : Matrix (Fin n) (Fin n) S := fun a b =>
    ⟨T a b, by rw [Valuation.mem_valuationSubring_iff, ← place_le_one_iff]; exact h a b⟩
  have key : T.adjugate i j = S.subtype (T'.adjugate i j) :=
    (congrFun (congrFun (RingHom.map_adjugate S.subtype T') i) j).symm
  rw [key, place_le_one_iff]
  exact (T'.adjugate i j).2

theorem UnitAt.inv_le_one {v : FinitePlace L} {T : Matrix (Fin n) (Fin n) L} (h : UnitAt v T) (i j : Fin n) :
    v (T⁻¹ i j) ≤ 1 := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  apply place_mul_le_one v _ (adj_le_lemma v h.1 i j)
  rw [FinitePlace.coe_apply, map_inv₀, ← FinitePlace.coe_apply, h.2, inv_one]

theorem UnitAt.locAt_frame {v : FinitePlace L} {T : Matrix (Fin n) (Fin n) L} (h : UnitAt v T) :
    locAt v (frame T) = locAt v (frame 1) := by
  have hdet : IsUnit T.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h2 := h.2
    rw [h0, FinitePlace.coe_apply, map_zero] at h2
    exact zero_ne_one h2
  have hrow : ∀ (M : Matrix (Fin n) (Fin n) L) (y : Fin n → L), (∀ i j, v (M i j) ≤ 1) →
      (∀ i, v (y i) ≤ 1) → ∀ i, v ((M *ᵥ y) i) ≤ 1 := by
    intro M y hM hy i
    simp only [Matrix.mulVec, dotProduct]
    exact place_sum_le_one v _ _ (fun k _ => place_mul_le_one v (hM i k) (hy k))
  ext x
  rw [mem_locAt_frame, mem_locAt_frame_one]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hrow T y h.1 hy
  · intro hx
    refine ⟨T⁻¹ *ᵥ x, hrow _ x h.inv_le_one hx, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
