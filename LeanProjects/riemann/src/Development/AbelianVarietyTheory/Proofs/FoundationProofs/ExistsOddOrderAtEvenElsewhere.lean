import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemGlobalNormOfMemLocalNorms
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissibleSupersetFinitePlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModLocalSquares
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdmissibleLocalNormMemSUnitsSupGlobalNorm

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma mem_locSq_iff' (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) :
    x ∈ _root_.GlobalTheory.QNorm.locSq F S ↔
      (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) (x : F))) ∧
        ∀ σ : F →+* ℝ, IsSquare (σ (x : F)) := by
  unfold _root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq
  simp [_root_.GlobalTheory.QNorm.mem_sqSub]

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma pos_of_isSquare_real_embedding_unit {F : Type} [Field F] (σ : F →+* ℝ) (x : Fˣ)
    (h : IsSquare (σ (x : F))) : 0 < σ (x : F) := by
  obtain ⟨r, hr⟩ := h
  have hne : σ (x : F) ≠ 0 := (map_ne_zero σ).mpr x.ne_zero
  exact lt_of_le_of_ne (by rw [hr]; exact mul_self_nonneg r) (Ne.symm hne)

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exists_valuation_eq_exp_two_mul_of_isSquare_completion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : F) (hx : x ≠ 0)
    (h : IsSquare (algebraMap F (v.adicCompletion F) x)) :
    ∃ n : ℤ, v.valuation F x = WithZero.exp (2 * n) := by
  obtain ⟨y, hy⟩ := h
  have hv : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hy0 : Valued.v y ≠ 0 := by
    intro h0
    rw [hy, map_mul, h0, zero_mul] at hv
    exact ((Valuation.ne_zero_iff _).mpr hx) hv.symm
  refine ⟨WithZero.log (Valued.v y), ?_⟩
  rw [← hv, hy, map_mul, two_mul, WithZero.exp_add, WithZero.exp_log hy0]

open NumberField IsDedekindDomain in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.exists_odd_order_at_even_elsewhere : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ)
    (σ₀ : F →+* ℝ), ¬ IsSquare (δ : F) →
    (∀ t : F, t ≠ 0 → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨
        ∃ n : ℤ, v.valuation F t = WithZero.exp (2 * n)) →
      (∀ σ : F →+* ℝ, σ ≠ σ₀ → 0 < σ t) → 0 < σ₀ t) →
    ∀ v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ t : F, t ≠ 0 ∧
      (∃ n : ℤ, v₀.valuation F t = WithZero.exp (2 * n + 1)) ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨
          ∃ n : ℤ, v.valuation F t = WithZero.exp (2 * n) := by
  intro F _ _ δ σ₀ hδ H v₀
  classical
  obtain ⟨S₀, hS₀, hδS₀, -⟩ := _root_.GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub F δ hδ
  set S := insert v₀ S₀ with hSdef
  have hv₀S : v₀ ∈ S := Finset.mem_insert_self _ _
  have hS : _root_.GlobalTheory.QNorm.admitted F S :=
    hS₀.mono (Finset.subset_insert _ _)
  have hδS : δ ∈ _root_.GlobalTheory.QNorm.sUnits F S := by
    rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hδS₀ ⊢
    intro v hv
    exact hδS₀ v fun h => hv (Finset.mem_insert_of_mem h)
  obtain ⟨T, hST, hcard, hTsq, hpat⟩ :=
    _root_.GlobalTheory.QNorm.exists_auxiliary_places F δ S hS hδS hδ
  have htop := _root_.GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top F S T hS hST hpat
  set U := _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) with hU
  set M := _root_.GlobalTheory.QNorm.locSq F S with hM
  have hgoodU : ∀ u ∈ U, ∀ v, v ∉ S → IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨
      ∃ n : ℤ, v.valuation F (u : F) = WithZero.exp (2 * n) := by
    intro u hu v hv
    by_cases hvT : v ∈ T
    · exact Or.inl (hTsq v hvT)
    · right
      refine ⟨0, ?_⟩
      rw [hU, _root_.GlobalTheory.QNorm.mem_sUnits] at hu
      rw [hu v (by simp [hv, hvT])]
      simp
  have hinf : M ⊓ U = _root_.GlobalTheory.QNorm.sqs U ⊓ U := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hyM, hyU⟩
      exact ⟨_root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare F (S ∪ T) y hyU
        (_root_.GlobalTheory.QNorm.isSquare_of_mem_locSq F S T hS htop y hyU hyM), hyU⟩
    · rintro ⟨hysq, hyU⟩
      exact ⟨_root_.GlobalTheory.QNorm.sqs_le_locSq F U S hysq, hyU⟩
  have hrel : M.relIndex U = 2 ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right,
      _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits]
  obtain ⟨hM0, hMle⟩ := _root_.GlobalTheory.QNorm.index_locSq_le F S
  have hidx := _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup U M
  have hunion : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hST
  rw [hrel, hunion] at hidx
  have hsup0 : (U ⊔ M).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hidx
    exact hM0 hidx
  have hle2 : (U ⊔ M).index ≤ 2 := by
    have h4 : (4 : ℕ) ^ (S.card + Fintype.card (InfinitePlace F)) =
        2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ]
      congr 1
      omega
    have h : 2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * (U ⊔ M).index ≤
        2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [← hidx, ← h4]
      exact hMle
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  obtain ⟨xs, hxs0, hxsS, hxsσ⟩ := _root_.GlobalTheory.QNorm.exists_approx_mod_squares F S (fun _ => 1)
    (fun σ => if σ = σ₀ then -1 else 1) (fun _ => one_ne_zero)
    (fun σ => by split_ifs <;> norm_num)
  simp only [mul_one] at hxsS
  have hxsσ₀ : σ₀ xs < 0 := by
    have h := hxsσ σ₀
    rw [if_pos rfl] at h
    linarith
  have hxsσ' : ∀ σ, σ ≠ σ₀ → 0 < σ xs := fun σ hσ => by
    have h := hxsσ σ
    rwa [if_neg hσ, mul_one] at h
  set X : Fˣ := Units.mk0 xs hxs0 with hX
  have hXnot : X ∉ U ⊔ M := by
    intro hXmem
    obtain ⟨y, hyU, z, hzM, hyz⟩ := Subgroup.mem_sup.mp hXmem
    rw [hM, mem_locSq_iff'] at hzM
    have hy : (y : F) = xs / z := by
      rw [eq_div_iff z.ne_zero, ← Units.val_mul, hyz, hX, Units.val_mk0]
    have hzpos : ∀ σ : F →+* ℝ, 0 < σ (z : F) := fun σ => pos_of_isSquare_real_embedding_unit σ z (hzM.2 σ)
    have hpos := H y y.ne_zero (fun v => by
      by_cases hv : v ∈ S
      · right
        apply exists_valuation_eq_exp_two_mul_of_isSquare_completion F v _ y.ne_zero
        rw [hy, map_div₀]
        exact (hxsS v hv).div (hzM.1 v hv)
      · exact hgoodU y hyU v hv) (fun σ hσ => by
        rw [hy, map_div₀]
        exact div_pos (hxsσ' σ hσ) (hzpos σ))
    rw [hy, map_div₀] at hpos
    have := (div_pos_iff_of_pos_right (hzpos σ₀)).mp hpos
    linarith
  have hidx2 : (U ⊔ M).index = 2 := by
    have hne1 : (U ⊔ M).index ≠ 1 := by
      intro h1
      exact hXnot (Subgroup.index_eq_one.mp h1 ▸ Subgroup.mem_top X)
    omega
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v₀
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  obtain ⟨xa, hxa0, hxaS, -⟩ := _root_.GlobalTheory.QNorm.exists_approx_mod_squares F S
    (fun v => if v = v₀ then algebraMap F (v.adicCompletion F) ϖ else 1) (fun _ => 1)
    (fun v => by
      split_ifs
      · exact (map_ne_zero _).mpr hϖ0
      · exact one_ne_zero)
    (fun _ => one_ne_zero)
  have hav₀ : ∃ n : ℤ, v₀.valuation F xa = WithZero.exp (2 * n + 1) := by
    have h := hxaS v₀ hv₀S
    rw [if_pos rfl, ← map_mul] at h
    obtain ⟨n, hn⟩ :=
      exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ (xa * ϖ) (mul_ne_zero hxa0 hϖ0) h
    have hva : v₀.valuation F xa ≠ 0 := (Valuation.ne_zero_iff _).mpr hxa0
    rw [map_mul, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_add] at hn
    have h' := WithZero.exp_injective hn
    refine ⟨n, ?_⟩
    rw [← WithZero.exp_log hva]
    congr 1
    omega
  have haS : ∀ v ∈ S, v ≠ v₀ → IsSquare (algebraMap F (v.adicCompletion F) xa) := fun v hv hne => by
    have h := hxaS v hv
    rwa [if_neg hne, mul_one] at h
  set A : Fˣ := Units.mk0 xa hxa0 with hA
  obtain ⟨B, hBmem, hBv₀, hBS⟩ : ∃ B : Fˣ, B ∈ U ⊔ M ∧
      (∃ n : ℤ, v₀.valuation F (B : F) = WithZero.exp (2 * n + 1)) ∧
      ∀ v ∈ S, v ≠ v₀ → IsSquare (algebraMap F (v.adicCompletion F) (B : F)) := by
    by_cases hAmem : A ∈ U ⊔ M
    · exact ⟨A, hAmem, hav₀, haS⟩
    · refine ⟨A * X, (Subgroup.mul_mem_iff_of_index_two hidx2).mpr (iff_of_false hAmem hXnot),
        ?_, ?_⟩
      · obtain ⟨m, hm⟩ := exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ xs hxs0 (hxsS v₀ hv₀S)
        obtain ⟨n, hn⟩ := hav₀
        refine ⟨n + m, ?_⟩
        rw [Units.val_mul, hA, hX, Units.val_mk0, Units.val_mk0, map_mul, hn, hm,
          ← WithZero.exp_add]
        congr 1
        ring
      · intro v hv hne
        rw [Units.val_mul, hA, hX, Units.val_mk0, Units.val_mk0, map_mul]
        exact (haS v hv hne).mul (hxsS v hv)
  obtain ⟨u, huU, m, hmM, hum⟩ := Subgroup.mem_sup.mp hBmem
  rw [hM, mem_locSq_iff'] at hmM
  have hum' : (u : F) * m = B := by rw [← Units.val_mul, hum]
  have hu : (u : F) = B / m := by rw [eq_div_iff m.ne_zero, hum']
  refine ⟨u, u.ne_zero, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hBv₀
    obtain ⟨k, hk⟩ := exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ m m.ne_zero (hmM.1 v₀ hv₀S)
    have hvu : v₀.valuation F (u : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
    have h := congrArg (v₀.valuation F) hum'
    rw [map_mul, hn, hk, ← WithZero.exp_log hvu, ← WithZero.exp_add] at h
    have h' := WithZero.exp_injective h
    refine ⟨n - k, ?_⟩
    rw [← WithZero.exp_log hvu]
    congr 1
    omega
  · intro v hne
    by_cases hv : v ∈ S
    · right
      apply exists_valuation_eq_exp_two_mul_of_isSquare_completion F v _ u.ne_zero
      rw [hu, map_div₀]
      exact (hBS v hv hne).div (hmM.1 v hv)
    · exact hgoodU u huU v hv

end GlobalTheory.QNorm
