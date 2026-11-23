import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FGTorsionFreeGen

namespace SupLatW

open Formalism.MainNotions.Ext.CutC

theorem mem_stdLat_iff {R K : Type} [CommRing R] [Field K] [Algebra R K] {r : ℕ}
    (v : Fin r → K) : v ∈ stdLat R K r ↔ ∃ x : Fin r → R, v = vecK R K x := by
  constructor
  · intro hv
    unfold stdLat at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      refine ⟨Pi.single i 1, ?_⟩
      funext j
      by_cases h : j = i
      · subst h; simp [vecK]
      · simp [vecK, h]
    | zero => exact ⟨0, by funext j; simp [vecK]⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x + y, by funext j; simp [vecK]⟩
    | smul a b _ hb =>
      obtain ⟨y, rfl⟩ := hb
      exact ⟨a • y, by funext j; simp [vecK, Algebra.smul_def]⟩
  · rintro ⟨x, rfl⟩
    have hx : vecK R K x = ∑ i, x i • (Pi.single i (1 : K) : Fin r → K) := by
      funext j
      simp [vecK, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [hx]
    unfold stdLat
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem alg_ne_zero {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) : algebraMap R K ϖ ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hϖ.ne_zero

theorem inv_smul_mem_iff {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ} (x : Fin r → R) :
    (algebraMap R K ϖ)⁻¹ • vecK R K x ∈ stdLat R K r ↔ ∀ i, ϖ ∣ x i := by
  have h0 := alg_ne_zero (K := K) hϖ
  have hinj := IsFractionRing.injective R K
  rw [mem_stdLat_iff]
  constructor
  · rintro ⟨z, hz⟩ i
    refine ⟨z i, hinj ?_⟩
    have e := congrFun hz i
    simp only [vecK, Pi.smul_apply, smul_eq_mul] at e
    rw [map_mul, ← e, mul_inv_cancel_left₀ h0]
  · intro h
    choose z hz using h
    refine ⟨z, funext fun i => ?_⟩
    simp only [vecK, Pi.smul_apply, smul_eq_mul]
    rw [hz i, map_mul, inv_mul_cancel_left₀ h0]

theorem dvd_of_not_isUnit {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) {s : R} (hs : ¬ IsUnit s) : ϖ ∣ s := by
  have hm : s ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal s).mpr (mem_nonunits_iff.mpr hs)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton] at hm
  exact hm

theorem supLat_le_of_dvd {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ} (x y : Fin r → R) (c : R)
    (h : ∀ i, ϖ ∣ x i - c * y i) : supLat R K ϖ x ≤ supLat R K ϖ y := by
  unfold supLat
  refine sup_le le_sup_left ?_
  rw [Submodule.span_singleton_le_iff_mem]
  have h1 : (algebraMap R K ϖ)⁻¹ • vecK R K (fun i => x i - c * y i) ∈ stdLat R K r :=
    (inv_smul_mem_iff hϖ _).mpr h
  have h2 : (algebraMap R K ϖ)⁻¹ • vecK R K x =
      (algebraMap R K ϖ)⁻¹ • vecK R K (fun i => x i - c * y i) +
        c • ((algebraMap R K ϖ)⁻¹ • vecK R K y) := by
    funext i
    simp only [vecK, Pi.add_apply, Pi.smul_apply]
    simp only [smul_eq_mul]
    simp only [Algebra.smul_def, map_sub, map_mul]
    ring
  rw [h2]
  exact Submodule.add_mem _ (Submodule.mem_sup_left h1)
    (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))

theorem supLat_eq_iff {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ}
    (x y : Fin r → R) (hx : ∃ i, ¬ ϖ ∣ x i) :
    supLat R K ϖ x = supLat R K ϖ y ↔ ∃ c : R, IsUnit c ∧ ∀ i, ϖ ∣ x i - c * y i := by
  constructor
  · intro hxy
    have hm : (algebraMap R K ϖ)⁻¹ • vecK R K x ∈
        stdLat R K r ⊔ Submodule.span R {(algebraMap R K ϖ)⁻¹ • vecK R K y} := by
      have : (algebraMap R K ϖ)⁻¹ • vecK R K x ∈ supLat R K ϖ x :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      rw [hxy] at this
      exact this
    obtain ⟨l, hl, t, ht, hsum⟩ := Submodule.mem_sup.mp hm
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp ht
    obtain ⟨z, rfl⟩ := (mem_stdLat_iff (R := R) l).mp hl
    have hw : algebraMap R K ϖ * (algebraMap R K ϖ)⁻¹ = 1 := mul_inv_cancel₀ (alg_ne_zero hϖ)
    have hxi : ∀ i, x i = ϖ * z i + s * y i := by
      intro i
      apply IsFractionRing.injective R K
      have e := congrFun hsum i
      simp only [vecK, Pi.add_apply, Pi.smul_apply] at e
      simp only [smul_eq_mul] at e
      simp only [Algebra.smul_def] at e
      rw [map_add, map_mul, map_mul]
      linear_combination (-(algebraMap R K ϖ)) * e +
        (algebraMap R K s * algebraMap R K (y i) - algebraMap R K (x i)) * hw
    refine ⟨s, ?_, fun i => ⟨z i, by rw [hxi i]; ring⟩⟩
    by_contra hs
    obtain ⟨i, hi⟩ := hx
    exact hi (by
      rw [hxi i]
      exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (dvd_of_not_isUnit hϖ hs) _))
  · rintro ⟨c, hc, h⟩
    refine le_antisymm (supLat_le_of_dvd hϖ x y c h)
      (supLat_le_of_dvd hϖ y x (↑hc.unit⁻¹) fun i => ?_)
    obtain ⟨d, hd⟩ := h i
    refine ⟨-(↑hc.unit⁻¹ : R) * d, ?_⟩
    have hcc : (↑hc.unit⁻¹ : R) * c = 1 := hc.val_inv_mul
    linear_combination (-(↑hc.unit⁻¹ : R)) * hd + (-(y i)) * hcc

theorem covBy_supLat {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ}
    (x : Fin r → R) (hx : ∃ i, ¬ ϖ ∣ x i) : stdLat R K r ⋖ supLat R K ϖ x := by
  have hv : (algebraMap R K ϖ)⁻¹ • vecK R K x ∉ stdLat R K r := by
    rw [inv_smul_mem_iff hϖ]
    push Not
    exact hx
  have hw : algebraMap R K ϖ * (algebraMap R K ϖ)⁻¹ = 1 := mul_inv_cancel₀ (alg_ne_zero hϖ)
  unfold supLat
  rw [covBy_iff_lt_and_eq_or_eq]
  refine ⟨SetLike.lt_iff_le_and_exists.mpr ⟨le_sup_left, _,
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), hv⟩, ?_⟩
  intro C h1 h2
  by_cases hC : C ≤ stdLat R K r
  · exact Or.inl (le_antisymm hC h1)
  · right
    refine le_antisymm h2 (sup_le h1 ?_)
    rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨c, hcC, hcL⟩ := SetLike.not_le_iff_exists.mp hC
    obtain ⟨l, hl, q, hq, hsum⟩ := Submodule.mem_sup.mp (h2 hcC)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hq
    have hs : IsUnit s := by
      by_contra hs
      obtain ⟨t, rfl⟩ := dvd_of_not_isUnit hϖ hs
      apply hcL
      rw [← hsum]
      refine Submodule.add_mem _ hl ?_
      have e : (ϖ * t) • ((algebraMap R K ϖ)⁻¹ • vecK R K x) = vecK R K (t • x) := by
        funext i
        simp only [vecK, Pi.smul_apply]
        simp only [smul_eq_mul]
        simp only [Algebra.smul_def, map_mul]
        linear_combination (algebraMap R K t * algebraMap R K (x i)) * hw
      rw [e, mem_stdLat_iff]
      exact ⟨_, rfl⟩
    have e : (algebraMap R K ϖ)⁻¹ • vecK R K x = (↑hs.unit⁻¹ : R) • (c - l) := by
      rw [← hsum, add_sub_cancel_left, smul_smul, hs.val_inv_mul, one_smul]
    rw [e]
    exact C.smul_mem _ (C.sub_mem hcC (h1 hl))

theorem eq_supLat_of_covBy {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {r : ℕ}
    (M : Submodule R (Fin r → K)) (hM : stdLat R K r ⋖ M) :
    ∃ x : Fin r → R, (∃ i, ¬ ϖ ∣ x i) ∧ M = supLat R K ϖ x := by
  have h0 := alg_ne_zero (K := K) hϖ
  obtain ⟨m, hmM, hmL⟩ := SetLike.exists_of_lt hM.lt
  have hpm : ϖ • m ∈ stdLat R K r := by
    rcases (covBy_iff_lt_and_eq_or_eq.mp hM).2 (stdLat R K r ⊔ Submodule.span R {ϖ • m})
        le_sup_left
        (sup_le hM.le ((Submodule.span_singleton_le_iff_mem _ _).mpr (M.smul_mem _ hmM)))
      with h | h
    · rw [← h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · exfalso
      have hm' : m ∈ stdLat R K r ⊔ Submodule.span R {ϖ • m} := by rw [h]; exact hmM
      obtain ⟨l, hl, q, hq, hsum⟩ := Submodule.mem_sup.mp hm'
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hq
      have hu : IsUnit (1 - t * ϖ) := by
        rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (t * ϖ) with h' | h'
        · exact absurd (isUnit_of_mul_isUnit_right h') hϖ.not_isUnit
        · exact h'
      apply hmL
      have e : (1 - t * ϖ) • m = l := by
        rw [sub_smul, one_smul, mul_smul]
        exact (eq_sub_of_add_eq hsum).symm
      have e2 : m = (↑hu.unit⁻¹ : R) • l := by
        rw [← e, smul_smul, hu.val_inv_mul, one_smul]
      rw [e2]
      exact Submodule.smul_mem _ _ hl
  obtain ⟨z, hz⟩ := (mem_stdLat_iff _).mp hpm
  have hm : m = (algebraMap R K ϖ)⁻¹ • vecK R K z := by
    rw [← hz]
    funext i
    simp only [Pi.smul_apply]
    simp only [smul_eq_mul]
    simp only [Algebra.smul_def]
    rw [inv_mul_cancel_left₀ h0]
  have hz' : ∃ i, ¬ ϖ ∣ z i := by
    by_contra hn
    push Not at hn
    apply hmL
    rw [hm]
    exact (inv_smul_mem_iff hϖ z).mpr hn
  refine ⟨z, hz', ?_⟩
  have hle : supLat R K ϖ z ≤ M := by
    unfold supLat
    exact sup_le hM.le ((Submodule.span_singleton_le_iff_mem _ _).mpr (hm ▸ hmM))
  rcases (covBy_iff_lt_and_eq_or_eq.mp hM).2 (supLat R K ϖ z) le_sup_left hle with h | h
  · exfalso
    apply hmL
    rw [← h, hm]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · exact h.symm

theorem main : SupLatLine := by
  intro R K _ _ _ _ _ _ ϖ hϖ r
  refine ⟨fun x hx => ?_, fun x y hx _ => supLat_eq_iff hϖ x y hx,
    fun M hle hM => eq_supLat_of_covBy hϖ M ((covBy_iff_quot_is_simple hle).mpr hM)⟩
  exact (covBy_iff_quot_is_simple le_sup_left).mp (covBy_supLat hϖ x hx)

end SupLatW
