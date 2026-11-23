import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.TotRam

open IsLocalRing

variable {R O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R O]

theorem isUnit_of_not_dvd_uniformiser {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {ϖ c : S} (hϖ : Irreducible ϖ) (h : ¬ ϖ ∣ c) : IsUnit c := by
  by_contra hc
  have hm : c ∈ maximalIdeal S := (mem_maximalIdeal c).2 (mem_nonunits_iff.2 hc)
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact h hm

theorem not_isUnit_algebraMap [Module.Finite R O] {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ IsUnit (algebraMap R O ϖ) := by
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hmem : ϖ ∈ maximalIdeal R := by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
  have hle : (⊤ : Submodule R O) ≤ maximalIdeal R • ⊤ := by
    intro x _
    have hx : x = ϖ • (v * x) := by rw [Algebra.smul_def, ← mul_assoc, hv, one_mul]
    rw [hx]
    exact Submodule.smul_mem_smul hmem trivial
  exact top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
    (Module.finite_def.mp ‹_›) hle (maximalIdeal_le_jacobson _))

theorem dvd_coeff_of_dvd_sum {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (he : π ^ e ∣ algebraMap R O ϖ) (c : ℕ → R) {m j : ℕ} (hj : j < e) (hjm : j < m)
    (hlow : ∀ i < j, ϖ ∣ c i) (hs : π ^ (j + 1) ∣ ∑ i ∈ Finset.range m, c i • π ^ i) : ϖ ∣ c j := by
  by_contra hc
  have hu : IsUnit (algebraMap R O (c j)) := (isUnit_of_not_dvd_uniformiser hϖ hc).map _
  have hrest : π ^ (j + 1) ∣ ∑ i ∈ (Finset.range m).erase j, c i • π ^ i := by
    refine Finset.dvd_sum fun i hi => ?_
    rw [Algebra.smul_def]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · obtain ⟨d, hd⟩ := hlow i h
      refine Dvd.dvd.mul_right ((pow_dvd_pow π (by omega : j + 1 ≤ e)).trans (he.trans ?_)) _
      rw [hd, map_mul]; exact dvd_mul_right _ _
    · exact Dvd.dvd.mul_left (pow_dvd_pow π (by omega : j + 1 ≤ i)) _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hjm)] at hs
  have h1 : π ^ j * π ∣ π ^ j * algebraMap R O (c j) := by
    rw [← pow_succ, mul_comm, ← Algebra.smul_def]; exact (dvd_add_left hrest).1 hs
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero j hπ.ne_zero)).1 h1
  exact hπ.not_isUnit (isUnit_of_dvd_unit h2 hu)

theorem dvd_coeff_all {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (he : π ^ e ∣ algebraMap R O ϖ) (c : ℕ → R) {m : ℕ}
    (hs : π ^ e ∣ ∑ i ∈ Finset.range m, c i • π ^ i) : ∀ j < e, j < m → ϖ ∣ c j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hjm
    exact dvd_coeff_of_dvd_sum hπ hϖ he c hj hjm (fun i hi => ih i hi (by omega) (by omega))
      ((pow_dvd_pow π (by omega)).trans hs)

theorem coeff_eq_zero_of_sum {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (hinj : Function.Injective (algebraMap R O)) {e : ℕ} (he : π ^ e ∣ algebraMap R O ϖ) :
    ∀ c : ℕ → R, ∑ i ∈ Finset.range e, c i • π ^ i = 0 → ∀ i < e, c i = 0 := by
  have hϖ0 : algebraMap R O ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have key : ∀ n : ℕ, ∀ c : ℕ → R, ∑ i ∈ Finset.range e, c i • π ^ i = 0 → ∀ i < e, ϖ ^ n ∣ c i := by
    intro n
    induction n with
    | zero => intro c _ i _; simp
    | succ n ih =>
      intro c hc i hi
      have hd := dvd_coeff_all hπ hϖ he c (m := e) (by rw [hc]; exact dvd_zero _)
      choose! d hd' using fun k (h : k < e) => hd k h h
      have h0 : algebraMap R O ϖ * ∑ k ∈ Finset.range e, d k • π ^ k = 0 := by
        rw [Finset.mul_sum, ← hc]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hd' k (Finset.mem_range.1 hk), Algebra.smul_def, Algebra.smul_def, map_mul]; ring
      have h1 := (mul_eq_zero.1 h0).resolve_left hϖ0
      rw [hd' i hi, pow_succ']
      exact mul_dvd_mul_left ϖ (ih d h1 i hi)
  intro c hc i hi
  by_contra h0
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ
  have h1 : ϖ ^ n * ϖ ∣ ϖ ^ n * 1 := by
    rw [← pow_succ, mul_one, ← hu]; exact (key (n + 1) c hc i hi).mul_right _
  exact hϖ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n hϖ.ne_zero)).1 h1))

theorem exists_degreeLT [Module.Finite R O] {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (he : Associated (algebraMap R O ϖ) (π ^ e))
    (hres : ∀ x : O, ∃ c : R, ¬ IsUnit (x - algebraMap R O c)) :
    ∀ x : O, ∃ f ∈ Polynomial.degreeLT R e, Polynomial.aeval π f = x := by
  have step : ∀ k (x : O), ∃ f ∈ Polynomial.degreeLT R k, π ^ k ∣ x - Polynomial.aeval π f := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, Submodule.zero_mem _, by rw [pow_zero]; exact one_dvd _⟩
    | succ k ih =>
      intro x
      obtain ⟨f, hf, z, hz⟩ := ih x
      obtain ⟨c, hc⟩ := hres z
      have hm : z - algebraMap R O c ∈ maximalIdeal O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hc)
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨t, ht⟩ := hm
      refine ⟨f + Polynomial.C c * Polynomial.X ^ k, ?_, t, ?_⟩
      · rw [Polynomial.mem_degreeLT] at hf ⊢
        have hk : ((k : ℕ) : WithBot ℕ) < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast k.lt_succ_self
        exact (Polynomial.degree_add_le _ _).trans_lt
          (max_lt (hf.trans hk) ((Polynomial.degree_C_mul_X_pow_le _ _).trans_lt hk))
      · simp only [map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
        rw [pow_succ, mul_assoc, ← ht]
        linear_combination hz
  have hmem : ϖ ∈ maximalIdeal R := by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
  obtain ⟨v, hv⟩ := he.dvd
  let N : Submodule R O := (Polynomial.degreeLT R e).map (Polynomial.aeval π).toLinearMap
  have hle : (⊤ : Submodule R O) ≤ N ⊔ maximalIdeal R • ⊤ := by
    intro x _
    obtain ⟨f, hf, y, hy⟩ := step e x
    refine Submodule.mem_sup.2 ⟨Polynomial.aeval π f, Submodule.mem_map.2 ⟨f, hf, rfl⟩, ϖ • (v * y),
      Submodule.smul_mem_smul hmem trivial, ?_⟩
    rw [Algebra.smul_def]
    linear_combination -hy - y * hv
  have hN := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›)
    (maximalIdeal_le_jacobson _) hle
  intro x
  obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.1 (hN (Submodule.mem_top : x ∈ ⊤))
  exact ⟨f, hf, hfx⟩

theorem eisenstein_of_totallyRamified {ϖ : R} (hϖ : Irreducible ϖ) [Module.Finite R O]
    (hinj : Function.Injective (algebraMap R O))
    (hres : ∀ x : O, ∃ c : R, ¬ IsUnit (x - algebraMap R O c)) {π : O} (hπ : Irreducible π) :
    ∃ Ep : Polynomial R, Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, ϖ ∣ Ep.coeff i) ∧
      (∃ w : Rˣ, Ep.coeff 0 = ϖ * w) ∧ Polynomial.aeval π Ep = 0 ∧
      (∀ x : O, ∃ f : Polynomial R, Polynomial.aeval π f = x) ∧
      ∀ f : Polynomial R, Polynomial.aeval π f = 0 → Ep ∣ f := by
  have hϖ0 : algebraMap R O ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hϖ0 hπ
  have he0 : e ≠ 0 := by
    rintro rfl
    exact not_isUnit_algebraMap hϖ (he.isUnit_iff.2 (by simp))
  have hed : π ^ e ∣ algebraMap R O ϖ := he.symm.dvd
  have hspan := exists_degreeLT hπ hϖ he hres
  obtain ⟨g, hg, hgπ⟩ := hspan (π ^ e)
  have hgdeg : g.degree < e := Polynomial.mem_degreeLT.1 hg
  have hdeg : (Polynomial.X ^ e - g).degree = (e : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]; exact hgdeg
  have hmon : (Polynomial.X ^ e - g).Monic := Polynomial.monic_X_pow_sub hgdeg
  have hnat : (Polynomial.X ^ e - g).natDegree = e := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hroot : Polynomial.aeval π (Polynomial.X ^ e - g) = 0 := by simp [hgπ]
  have hsum : ∑ i ∈ Finset.range (e + 1), (Polynomial.X ^ e - g).coeff i • π ^ i = 0 := by
    have h := Polynomial.aeval_eq_sum_range (p := Polynomial.X ^ e - g) π
    rw [hnat] at h; rw [← h]; exact hroot
  have hdvd : ∀ i < e, ϖ ∣ (Polynomial.X ^ e - g).coeff i := fun i hi =>
    dvd_coeff_all hπ hϖ hed _ (by rw [hsum]; exact dvd_zero _) i hi (by omega)
  have hcoeffe : (Polynomial.X ^ e - g).coeff e = 1 := by
    have := hmon.coeff_natDegree; rwa [hnat] at this
  have hc0 : ∃ w : Rˣ, (Polynomial.X ^ e - g).coeff 0 = ϖ * w := by
    obtain ⟨w, hw⟩ := hdvd 0 (Nat.pos_of_ne_zero he0)
    by_cases hwu : ϖ ∣ w
    · exfalso
      obtain ⟨t, ht⟩ := hwu
      have hrest : π ^ (e + 1) ∣
          ∑ i ∈ (Finset.range (e + 1)).erase e, (Polynomial.X ^ e - g).coeff i • π ^ i := by
        refine Finset.dvd_sum fun i hi => ?_
        have hie : i < e := by
          have := Finset.mem_range.1 (Finset.mem_of_mem_erase hi); have := Finset.ne_of_mem_erase hi; omega
        rw [Algebra.smul_def]
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [pow_zero, mul_one, hw, ht, map_mul, map_mul]
          refine (pow_dvd_pow π (by omega : e + 1 ≤ e + e)).trans ?_
          rw [pow_add]; exact mul_dvd_mul hed (hed.mul_right _)
        · obtain ⟨d, hd⟩ := hdvd i hie
          rw [hd, map_mul, pow_succ]
          exact mul_dvd_mul (hed.mul_right _) (dvd_pow_self π hi0.ne')
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (Nat.lt_succ_self e)), hcoeffe, one_smul] at hsum
      have h1 : π ^ e * π ∣ π ^ e * 1 := by
        rw [← pow_succ, mul_one]; exact (dvd_add_left hrest).1 (by rw [hsum]; exact dvd_zero _)
      exact hπ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero e hπ.ne_zero)).1 h1))
    · exact ⟨(isUnit_of_not_dvd_uniformiser hϖ hwu).unit, hw⟩
  have hmod : ∀ f : Polynomial R, Polynomial.aeval π f = 0 → (Polynomial.X ^ e - g) ∣ f := by
    intro f hf
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hmon]
    have hr : Polynomial.aeval π (f %ₘ (Polynomial.X ^ e - g)) = 0 := by
      have h := congrArg (Polynomial.aeval π) (Polynomial.modByMonic_add_div f (Polynomial.X ^ e - g))
      rwa [map_add, map_mul, hroot, zero_mul, add_zero, hf] at h
    have hrdeg : (f %ₘ (Polynomial.X ^ e - g)).natDegree < e := by
      by_cases h0 : f %ₘ (Polynomial.X ^ e - g) = 0
      · rw [h0, Polynomial.natDegree_zero]; omega
      · rw [Polynomial.natDegree_lt_iff_degree_lt h0, ← hdeg]
        exact Polynomial.degree_modByMonic_lt f hmon
    have hs := Polynomial.aeval_eq_sum_range' hrdeg π
    rw [hr] at hs
    have hc := coeff_eq_zero_of_sum hπ hϖ hinj hed _ hs.symm
    ext i
    rw [Polynomial.coeff_zero]
    by_cases hi : i < e
    · exact hc i hi
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  exact ⟨Polynomial.X ^ e - g, hmon, by rw [hnat]; omega, fun i hi => hdvd i (by rw [hnat] at hi; exact hi), hc0,
    hroot, fun x => (hspan x).imp fun f hf => hf.2, hmod⟩

theorem eisenstein_minpoly_Wq : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∀ π : O, Irreducible π → ∃ Ep : Polynomial (Wq l a), Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  intro l _ a _ O _ _ _ _ _ hinj hres π hπ
  exact eisenstein_of_totallyRamified (WittVector.irreducible l) hinj hres hπ

end GlobalTheory.TotRam
