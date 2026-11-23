import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaxVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.MaxLatDet

open IsDedekindDomain

section Form

variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]

theorem form_eq_sum (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Module.Basis ι K V)
    (he : ∀ i l, i ≠ l → h (e i) (e l) = 0) (x y : V) :
    h x y = ∑ i, star (e.repr x i) * h (e i) (e i) * e.repr y i := by
  conv_lhs => rw [← e.sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, mul_assoc]
  congr 1
  conv_lhs => rw [← e.sum_repr y]
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_smul, smul_eq_mul, mul_comm]
  · intro l _ hl
    rw [map_smul, he i l hl.symm, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem det_gram [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (e b : Module.Basis ι K V)
    (he : ∀ i l, i ≠ l → h (e i) (e l) = 0) :
    ∃ δ : K, δ ≠ 0 ∧ (Matrix.of fun i l => h (b i) (b l)).det = star δ * δ * ∏ i, h (e i) (e i) := by
  have hT : IsUnit (e.toMatrix b).det := by
    letI := e.invertibleToMatrix b
    exact Matrix.isUnit_det_of_invertible _
  refine ⟨(e.toMatrix b).det, hT.ne_zero, ?_⟩
  have : (Matrix.of fun i l => h (b i) (b l)) =
      (e.toMatrix b)ᴴ * Matrix.diagonal (fun i => h (e i) (e i)) * e.toMatrix b := by
    ext i l
    rw [Matrix.of_apply, form_eq_sum h e he, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Module.Basis.toMatrix_apply,
      Module.Basis.toMatrix_apply]
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal]
  ring

end Form

section Val

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mem_locR_iff_le (w : HeightOneSpectrum (𝓞 K)) (hw : conjIdeal (K := K) w.asIdeal = w.asIdeal)
    (k : K) : k ∈ locR (K := K) w.asIdeal ↔ w.valuation K k ≤ 1 := by
  refine ⟨fun hk => ((GlobalTheory.MassOrth.mem_locR_iff w k).1 hk).1, fun hk => ?_⟩
  obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer k hk
  refine (locDual_mem_locR _ _).2 ⟨d, locBasic_mem_hcompl _ _ d.2 (by rw [hw]; exact d.2), ?_⟩
  rw [mul_comm, hnd]
  exact locDual_alg_mem _

theorem val_star (w : HeightOneSpectrum (𝓞 K)) (hw : conjIdeal (K := K) w.asIdeal = w.asIdeal)
    (k : K) : w.valuation K (star k) = w.valuation K k := by
  have h1 : ∀ k : K, w.valuation K k ≤ 1 → w.valuation K (star k) ≤ 1 := fun k hk =>
    ((GlobalTheory.MassOrth.mem_locR_iff w k).1 ((mem_locR_iff_le w hw k).2 hk)).2
  have h2 : ∀ k : K, k ≠ 0 → w.valuation K (star k) ≤ w.valuation K k →
      w.valuation K k ≤ w.valuation K (star k) := by
    intro k hk hle
    have p1 : 0 < w.valuation K k := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hk)
    have p2 : 0 < w.valuation K (star k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (star_ne_zero.2 hk))
    have := h1 (star k / k) (by rw [map_div₀, div_le_one₀ p1]; exact hle)
    rwa [star_div₀, star_star, map_div₀, div_le_one₀ p2] at this
  by_cases hk : k = 0
  · rw [hk, star_zero]
  rcases le_total (w.valuation K (star k)) (w.valuation K k) with hle | hle
  · exact le_antisymm hle (h2 k hk hle)
  · refine le_antisymm ?_ hle
    have := h2 (star k) (star_ne_zero.2 hk) (by rwa [star_star])
    rwa [star_star] at this

omit [StarRing K] in

theorem val_unif (w : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (h1 : a ∈ w.asIdeal) (h2 : a ∉ w.asIdeal ^ 2) :
    w.valuation K (algebraMap (𝓞 K) K a) = WithZero.exp (-1 : ℤ) := by
  rw [w.valuation_of_algebraMap]
  have a0 : a ≠ 0 := fun e => h2 (e ▸ Submodule.zero_mem _)
  have e1 := (w.intValuation_le_pow_iff_mem a 1).2 (by rwa [pow_one])
  have e2 := mt (w.intValuation_le_pow_iff_mem a 2).1 h2
  have n0 := w.intValuation_ne_zero a a0
  rw [← WithZero.exp_log n0, WithZero.exp_le_exp] at e1 e2
  rw [← WithZero.exp_log n0, WithZero.exp_inj]
  push_cast at e1 e2
  omega

end Val

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ (j : ℕ) (b : Module.Basis (Fin j) K V) (P : Ideal (𝓞 K)), P.IsMaximal → (P ∈ badP h M ↔ conjIdeal (K := K) P = P ∧ ¬ ∃ c : K, c ≠ 0 ∧ star c * c * (Matrix.of fun i l => h (b i) (b l)).det ∈ locR (K := K) P ∧ (star c * c * (Matrix.of fun i l => h (b i) (b l)).det)⁻¹ ∈ locR (K := K) P) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hnd M hM j b P hP
  have hstruct := (GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM).2.2.2 P
  by_cases hc : conjIdeal (K := K) P = P
  swap
  · exact ⟨fun hb => absurd (hstruct hb).1 hc, fun hb => absurd hb.1 hc⟩
  let w : HeightOneSpectrum (𝓞 K) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)⟩
  have hloc : ∀ k, k ∈ locR (K := K) P ↔ w.valuation K k ≤ 1 := mem_locR_iff_le w hc
  have hvs : ∀ k, w.valuation K (star k) = w.valuation K k := val_star w hc
  have hunif : ∀ a : 𝓞 K, a ∈ P → a ∉ P ^ 2 →
      w.valuation K (algebraMap (𝓞 K) K a) = WithZero.exp (-1 : ℤ) := fun a => val_unif w
  generalize w.valuation K = v at hloc hvs hunif
  obtain ⟨e, he, heM⟩ := GlobalTheory.MassOrth.main K V h hK hs hnd M hM.1.1 P hP
  simp only [hloc] at heM ⊢
  have hj : j = Module.finrank K V := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hj
  obtain ⟨δ, hδ, hdet⟩ := det_gram h e b he
  rw [hdet]
  have hform := form_eq_sum h e he
  have hrow : ∀ i y, h (e i) y = h (e i) (e i) * e.repr y i := by
    intro i y
    rw [hform, Finset.sum_eq_single i]
    · simp
    · intro l _ hl
      simp [Finsupp.single_apply, hl.symm]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hd0 : ∀ i, h (e i) (e i) ≠ 0 := fun i h0 =>
    e.ne_zero i (hnd.1 _ fun y => by rw [hrow, h0, zero_mul])
  have hv0 : ∀ i, v (h (e i) (e i)) ≠ 0 := fun i => (Valuation.ne_zero_iff _).2 (hd0 i)
  have heloc : ∀ i, e i ∈ loc (K := K) P M := fun i => (heM _).2 fun l => by
    rw [e.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  have hdual : ∀ y, y ∈ dualAt h P (loc (K := K) P M) ↔ ∀ i, v (h (e i) (e i) * e.repr y i) ≤ 1 := by
    intro y
    rw [locDual_mem_dualAt]
    simp only [hloc]
    refine ⟨fun hy i => by rw [← hrow]; exact hy _ (heloc i), fun hy x hx => ?_⟩
    rw [hform]
    refine v.map_sum_le fun i _ => ?_
    rw [mul_assoc, map_mul, hvs]
    exact mul_le_one' ((heM x).1 hx i) (hy i)
  obtain ⟨σ, hσ⟩ := GlobalTheory.MaxLatStruct.star_int (K := K)
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    fun r => ⟨σ r, hσ r⟩
  have hLD : loc (K := K) P (dual h M) = dualAt h P (loc (K := K) P M) := by
    rw [locDual_dualAt_loc h (IsFractionRing.injective _ _) hstar]
    exact le_antisymm (locDual_loc_dual_le h P M) (locDual_dualAt_le h hstar P M hM.1.1.fg)
  have hMd : M ≤ dual h M := fun x hx => (dualBasic_mem_dual h M x).2 fun y hy => hM.1.2 y hy x hx
  have hd1 : ∀ i, v (h (e i) (e i)) ≤ 1 := fun i => by
    have h1 : e i ∈ loc (K := K) P (dual h M) := locBasic_locS_mono _ hMd (heloc i)
    rw [hLD, hdual] at h1
    simpa using h1 i
  have hdy : ∀ i, (h (e i) (e i))⁻¹ • e i ∈ dualAt h P (loc (K := K) P M) := fun i => by
    rw [hdual]
    intro l
    rw [map_smul, e.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with hil
    · subst hil
      rw [smul_eq_mul, mul_one, mul_inv_cancel₀ (hd0 i), map_one]
    · simp
  have hU : IsUnimodularAt h P M ↔ ∀ i, v (h (e i) (e i)) = 1 := by
    unfold IsUnimodularAt
    constructor
    · intro hu i
      have h1 := hdy i
      rw [hu, heM] at h1
      have h2 := h1 i
      rw [map_smul, e.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
        map_inv₀, inv_le_one₀ (zero_lt_iff.2 (hv0 i))] at h2
      exact le_antisymm (hd1 i) h2
    · intro hu
      ext y
      rw [hdual, heM]
      simp only [map_mul, hu, one_mul]
  constructor
  · intro hb
    refine ⟨hc, ?_⟩
    obtain ⟨-, -, -, x, hx, ⟨a, ha, ha1, ha2⟩, hgen⟩ := hstruct hb
    have hxx : v (h x x) = WithZero.exp (-1 : ℤ) := by rw [← ha]; exact hunif a ha1 ha2
    have hx1 : ∀ i, v (e.repr x i) ≤ 1 := (heM x).1 (locBasic_le_locS _ _ hx)
    have key : ∀ i, v (h (e i) (e i)) ≠ 1 → v (h (e i) (e i)) = WithZero.exp (-1 : ℤ) ∧
        v (e.repr x i) = 1 ∧ ∀ l, l ≠ i → v (e.repr x l) ≠ 1 := by
      intro i hi
      obtain ⟨c, hc1, hc2⟩ := hgen _ (hLD ▸ hdy i)
      rw [hloc] at hc1
      rw [heM] at hc2
      have hco : ∀ l, v ((h (e i) (e i))⁻¹ * (if i = l then 1 else 0) - c * (h x x)⁻¹ * e.repr x l) ≤ 1 := by
        intro l
        have := hc2 l
        rwa [map_sub, map_smul, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.smul_apply,
          e.repr_self, Finsupp.single_apply, smul_eq_mul, smul_eq_mul] at this
      have h1 := hco i
      rw [if_pos rfl, mul_one] at h1
      have h2 : 1 < v (h (e i) (e i))⁻¹ := by
        rw [map_inv₀, one_lt_inv₀ (zero_lt_iff.2 (hv0 i))]
        exact lt_of_le_of_ne (hd1 i) hi
      have h3 : v (c * (h x x)⁻¹ * e.repr x i) = v (h (e i) (e i))⁻¹ :=
        v.map_eq_of_sub_lt (by rw [v.map_sub_swap]; exact h1.trans_lt h2)
      have hc0 : v c ≠ 0 := fun h0 => by
        rw [← h3, map_mul, map_mul, h0, zero_mul, zero_mul] at h2; exact not_lt_zero h2
      have hx0 : v (e.repr x i) ≠ 0 := fun h0 => by
        rw [← h3, map_mul, h0, mul_zero] at h2; exact not_lt_zero h2
      have h4 := hx1 i
      rw [map_mul, map_mul, map_inv₀, map_inv₀, hxx] at h3
      rw [map_inv₀] at h2
      obtain ⟨n1, hn1⟩ : ∃ n : ℤ, v c = WithZero.exp n := ⟨_, (WithZero.exp_log hc0).symm⟩
      obtain ⟨n2, hn2⟩ : ∃ n : ℤ, v (e.repr x i) = WithZero.exp n := ⟨_, (WithZero.exp_log hx0).symm⟩
      obtain ⟨n3, hn3⟩ : ∃ n : ℤ, v (h (e i) (e i)) = WithZero.exp n := ⟨_, (WithZero.exp_log (hv0 i)).symm⟩
      rw [hn1, hn2, hn3, ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_add,
        WithZero.exp_inj] at h3
      rw [hn3, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h2
      rw [hn2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h4
      rw [hn1, ← WithZero.exp_zero, WithZero.exp_le_exp] at hc1
      refine ⟨by rw [hn3, WithZero.exp_inj]; omega, by rw [hn2, ← WithZero.exp_zero, WithZero.exp_inj]; omega,
        fun l hl hl1 => ?_⟩
      have h5 := hco l
      rw [if_neg hl.symm, mul_zero, zero_sub, Valuation.map_neg, map_mul, map_mul, map_inv₀, hxx, hl1, mul_one,
        hn1, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at h5
      omega
    obtain ⟨i, hi⟩ := not_forall.1 (mt hU.2 hb.2)
    have hprod : v (∏ l, h (e l) (e l)) = WithZero.exp (-1 : ℤ) := by
      rw [map_prod, Finset.prod_eq_single i, (key i hi).1]
      · intro l _ hl
        by_contra hl1
        exact (key i hi).2.2 l hl (key l hl1).2.1
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rintro ⟨c, hc0, h1, h2⟩
    obtain ⟨n1, hn1⟩ : ∃ n : ℤ, v c = WithZero.exp n :=
      ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hc0)).symm⟩
    obtain ⟨n2, hn2⟩ : ∃ n : ℤ, v δ = WithZero.exp n :=
      ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hδ)).symm⟩
    have hval : v (star c * c * (star δ * δ * ∏ l, h (e l) (e l))) = WithZero.exp (n1 + n1 + (n2 + n2 + -1)) := by
      rw [map_mul, map_mul, map_mul, map_mul, hvs, hvs, hprod, hn1, hn2]
      simp only [WithZero.exp_add]
    rw [map_inv₀, hval, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · rintro ⟨-, hn⟩
    refine ⟨hP, fun hu => hn ⟨δ⁻¹, inv_ne_zero hδ, ?_⟩⟩
    have hsδ : star δ ≠ 0 := star_ne_zero.2 hδ
    have e1 : star δ⁻¹ * δ⁻¹ * (star δ * δ * ∏ l, h (e l) (e l)) = ∏ l, h (e l) (e l) := by
      rw [star_inv₀]; field_simp
    have e2 : v (∏ l, h (e l) (e l)) = 1 := by
      rw [map_prod]; exact Finset.prod_eq_one fun l _ => hU.1 hu l
    rw [e1, map_inv₀, e2, inv_one]
    exact ⟨le_rfl, le_rfl⟩

end GlobalTheory.MaxLatDet
