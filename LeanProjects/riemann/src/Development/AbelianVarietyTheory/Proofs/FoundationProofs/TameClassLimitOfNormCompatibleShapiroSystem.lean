import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapPadicIntQbarContinuous
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecCauchy
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormIntCastLeOfDvd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA.TameLim

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  haveI : Module.Finite ℤ_[l] c.O := c.fin
  have hi : IsIntegral ℤ_[l] x := by
    have h := (isIntegral_algHom_iff (c.O.val.restrictScalars ℤ_[l]) Subtype.val_injective).2
      (Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : c.O))
    simpa using h
  have hq : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  change spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem inv_pow_mem (c : Coef l) (e k : ℕ) (h : k = 0 ∨ ¬ l ∣ k) : (((k : ℕ) : Qbar l) ^ e)⁻¹ ∈ c.O := by
  rcases h with rfl | h
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · simpa using c.O.one_mem
    · simpa [zero_pow he.ne'] using c.O.zero_mem
  · have hk : IsUnit ((k : ℤ_[l])) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_def]
      push_cast
      rw [Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h
    obtain ⟨u, hu⟩ := hk.pow e
    have e1 : (((k : ℕ) : Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [map_units_inv (algebraMap ℤ_[l] (Qbar l)) u, hu, map_pow, map_natCast]
    rw [e1]
    exact c.O.algebraMap_mem _

theorem val_unit (r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    (x : ZMod (l ^ r)).val = 0 ∨ ¬ l ∣ (x : ZMod (l ^ r)).val := by
  have hp : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · left
    haveI : NeZero (l ^ 0) := ⟨by simp⟩
    have := ZMod.val_lt (x : ZMod (l ^ 0))
    exact Nat.lt_one_iff.mp (lt_of_lt_of_eq this (pow_zero l))
  · right
    intro hd
    have hc := ZMod.val_coe_unit_coprime x
    have h2 : l ∣ Nat.gcd (x : ZMod (l ^ r)).val (l ^ r) := Nat.dvd_gcd hd (dvd_pow_self l (by omega))
    rw [hc] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

theorem mul_sub_mul_le (a a' u u' : Qbar l) (C : ℝ) (ha' : ‖a'‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    (h1 : ‖a' - a‖ ≤ C) (h2 : ‖u' - u‖ ≤ C) : ‖a' * u' - a * u‖ ≤ C := by
  have e : a' * u' - a * u = a' * (u' - u) + (a' - a) * u := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) ha').trans h2
  · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans h1

end GlobalTheory.KA.TameLim

namespace GlobalTheory.KA.TameLim

theorem core (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ)
    (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l) (P : Qbar l) (b : ℕ → Fin 2 → Qbar l)
    (hWO : ∀ s i j, mat W s i j ∈ c.O) (hWρ : ∀ s, mat W s = (θ s : Qbar l) • ρ s)
    (hρO : ∀ s i j, ρ s i j ∈ c.O) (hηO : ∀ r x, η r x ∈ c.O)
    (hηc : ∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖η (r + 1) x - η r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hηa : ∀ r s x, ‖η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hSh : ∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r))
    (hcont : ∀ r x i, Continuous fun s => Yw r s x i)
    (hYO : ∀ r s x i, Yw r s x i ∈ c.O)
    (hnc : ∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s)
    (hb : ∀ r i, b r i ∈ c.O)
    (hrel : ∀ r s i, ‖(∑ a, spec (η r) (fun s x => Yw r s (a, x)) s) i - (P • y s + (mat W s *ᵥ b r - b r)) i‖ ≤
      ‖((l : ℕ) : Qbar l) ^ r‖) :
    ∃ (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (b' : Fin 2 → Qbar l), ShCoc (mat W) ψ Y ∧
      (∀ x i, Continuous fun s => Y s x i) ∧ (∀ s x i, Y s x i ∈ c.O) ∧ (∀ i, b' i ∈ c.O) ∧
      (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b')) ∧
      ∀ r s x i, ‖Y s x i - spec (η r) (fun s x' => Yw r s (x, x')) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hq := GlobalTheory.norm_natCast_prime_qbar l
  have hC : ∀ r : ℕ, (0 : ℝ) ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := fun r => norm_nonneg _
  have ht0 : Filter.Tendsto (fun r : ℕ => ‖((l : ℕ) : Qbar l) ^ r‖) Filter.atTop (nhds 0) := by
    simp only [norm_pow]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq
  have hzero : ∀ z : Qbar l, (∀ r, ‖z‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → z = 0 := fun z hz =>
    norm_le_zero_iff.mp (ge_of_tendsto' ht0 hz)
  have n1 : ∀ {x : Qbar l}, x ∈ c.O → ‖x‖ ≤ 1 := fun hx => norm_le_one_of_mem c hx
  have hMle : ∀ s i j, ‖mat W s i j‖ ≤ 1 := fun s i j => n1 (hWO s i j)
  have hρle : ∀ s i j, ‖ρ s i j‖ ≤ 1 := fun s i j => n1 (hρO s i j)

  set Yr : ℕ → G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l :=
    fun r s a => spec (η r) (fun s x => Yw r s (a, x)) s with hYr
  have hYr_apply : ∀ r s a i, Yr r s a i = ∑ x, η r x * Yw r s (a, x) i := by
    intro r s a i; simp only [hYr, spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hYrO : ∀ r s a i, Yr r s a i ∈ c.O := by
    intro r s a i; rw [hYr_apply]
    exact Subalgebra.sum_mem _ fun x _ => Subalgebra.mul_mem _ (hηO r x) (hYO r s (a, x) i)

  have hslice : ∀ a r s, (fun x => Yw r s (a, x)) = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (fun s x' => Yw (r + 1) s (a, x')) s := by
    intro a r s; funext x
    rw [hnc r s]
    simp only [push]
    refine Finset.sum_nbij' (fun p => p.2) (fun x' => (a, x')) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq] at hp ⊢; exact hp.2
    · intro x' hx'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq, id] at hx' ⊢; first | exact hx' | exact ⟨rfl, hx'⟩
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq, id] at hp
      exact Prod.ext hp.1.symm rfl
    · intro x' _; rfl
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq, id] at hp
      rw [← hp.1]
  have hstep : ∀ r s a i, ‖Yr (r + 1) s a i - Yr r s a i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    intro r s a i
    exact spec_cauchy l (fun r s x => Yw r s (a, x)) η (fun r s x i => n1 (hYO r s (a, x) i))
      (fun r x => n1 (hηO r x)) (fun r s => hslice a r s) hηc r s i
  have hlim : ∀ s a i, ∃ v ∈ c.O, ∀ r, ‖v - Yr r s a i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
    fun s a i => GlobalTheory.coef_limit l c (fun r => Yr r s a i) (fun r => hYrO r s a i) (fun r => hstep r s a i)
  choose Y hYO' hYap using hlim

  have happ : ∀ r s t a i, ‖Yr r (s * t) a i - (Yr r s a + mat W s *ᵥ Yr r t (a * ψ s)) i‖ ≤
      ‖((l : ℕ) : Qbar l) ^ r‖ := by
    intro r s t a i
    have key : Yr r (s * t) a - (Yr r s a + mat W s *ᵥ Yr r t (a * ψ s)) =
        ρ s *ᵥ ∑ x, (η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)) • Yw r t (a * ψ s, x) := by
      have h1 : Yr r (s * t) a = Yr r s a +
          ρ s *ᵥ ∑ x, η r x • Yw r t (a * ψ s, x * (cycMod ℚ Ω l r s)⁻¹) := by
        simp only [hYr, spec, hSh r s t, smul_add, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul,
          Prod.mk_mul_mk, MonoidHom.prod_apply, MonoidHom.inv_apply]
      have hre : ∑ x, η r x • Yw r t (a * ψ s, x * (cycMod ℚ Ω l r s)⁻¹) =
          ∑ x, η r (x * cycMod ℚ Ω l r s) • Yw r t (a * ψ s, x) :=
        Fintype.sum_equiv (Equiv.mulRight (cycMod ℚ Ω l r s)⁻¹) _ _ (fun x => by simp)
      rw [h1, hre, hWρ s]
      simp only [hYr, spec]
      rw [Matrix.smul_mulVec, ← Matrix.mulVec_smul, add_sub_add_left_eq_sub, ← Matrix.mulVec_sub]
      congr 1
      simp only [Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, sub_smul, mul_comm (θ s : Qbar l)]
    rw [← Pi.sub_apply, key]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hC r)
    intro j _
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hρle s i j)) ?_
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hC r)
    intro x _
    rw [norm_mul]
    exact le_trans (mul_le_of_le_one_right (norm_nonneg _) (n1 (hYO r t _ j))) (hηa r s x)

  have hcoc : ShCoc (mat W) ψ Y := by
    intro s t a
    funext i
    rw [← sub_eq_zero]
    apply hzero
    intro r
    have e : Y (s * t) a i - (Y s a + mat W s *ᵥ Y t (a * ψ s)) i =
        (Y (s * t) a i - Yr r (s * t) a i) + (Yr r (s * t) a i - (Yr r s a + mat W s *ᵥ Yr r t (a * ψ s)) i)
          + (Yr r s a i - Y s a i) + (mat W s *ᵥ (Yr r t (a * ψ s) - Y t (a * ψ s))) i := by
      simp only [Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]; ring
    rw [e]
    have hM : ‖(mat W s *ᵥ (Yr r t (a * ψ s) - Y t (a * ψ s))) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hC r)
      intro j _
      rw [norm_mul, norm_sub_rev]
      exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hMle s i j)) (hYap t (a * ψ s) j r)
    have h3 : ‖Yr r s a i - Y s a i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
      rw [norm_sub_rev]; exact hYap s a i r
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hYap _ _ _ r) (happ r s t a i))) h3)) hM)

  have hcontY : ∀ x i, Continuous fun s => Y s x i := by
    intro x i
    have hu : TendstoUniformly (fun r s => Yr r s x i) (fun s => Y s x i) Filter.atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [ht0.eventually (gt_mem_nhds hε)] with r hr s
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hYap s x i r) hr
    refine hu.continuous (Filter.Frequently.of_forall fun r => ?_)
    simp only [hYr_apply]
    exact continuous_finset_sum _ fun x' _ => continuous_const.mul (hcont r (x, x') i)

  obtain ⟨b', hb'K, φ, hφ, hφt⟩ := (isCompact_univ_pi (fun _ : Fin 2 => GlobalTheory.Coef.isCompact_O l c)).tendsto_subseq
    (x := b) (fun r => Set.mem_univ_pi.mpr (hb r))
  have hb'O : ∀ i, b' i ∈ c.O := fun i => Set.mem_univ_pi.mp hb'K i
  have hsum : ∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b') := by
    intro s; funext i
    have hφ0 : Filter.Tendsto (fun k => ‖((l : ℕ) : Qbar l) ^ φ k‖) Filter.atTop (nhds 0) :=
      ht0.comp hφ.tendsto_atTop
    have h1 : Filter.Tendsto (fun k => (∑ x, Yr (φ k) s x) i) Filter.atTop (nhds ((∑ x, Y s x) i)) := by
      simp only [Finset.sum_apply]
      refine tendsto_finset_sum _ fun x _ => ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hφ0
      rw [norm_sub_rev]; exact hYap s x i (φ k)
    have hg : Continuous fun v : Fin 2 → Qbar l => (P • y s + (mat W s *ᵥ v - v)) i := by
      fun_prop
    have h2 : Filter.Tendsto (fun k => (P • y s + (mat W s *ᵥ b (φ k) - b (φ k))) i) Filter.atTop
        (nhds ((P • y s + (mat W s *ᵥ b' - b')) i)) :=
      (hg.tendsto b').comp hφt
    have h3 : Filter.Tendsto (fun k => (∑ x, Yr (φ k) s x) i - (P • y s + (mat W s *ᵥ b (φ k) - b (φ k))) i)
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hrel (φ k) s i) hφ0
    exact sub_eq_zero.mp (tendsto_nhds_unique (h1.sub h2) h3)
  exact ⟨Y, b', hcoc, hcontY, hYO', hb'O, hsum, fun r s x i => hYap s x i r⟩

end GlobalTheory.KA.TameLim

namespace GlobalTheory.KA

theorem tame_limit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (e n : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l) (P : Qbar l) (b : ℕ → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x, χ r x ∈ c.O) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) → (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) → P ∈ c.O → (∀ r i, b r i ∈ c.O) → (∀ s i, y s i ∈ c.O) → (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i - (P • y s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∃ (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (b' : Fin 2 → Qbar l), ShCoc (mat W) ψ Y ∧ (∀ x i, Continuous fun s => Y s x i) ∧ (∀ s x i, Y s x i ∈ c.O) ∧ (∀ i, b' i ∈ c.O) ∧ (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b')) ∧ ∀ r s x i, ‖Y s x i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x' => Yw r s (x, x')) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l _ Ω _ _ W c e n χ θ ρ ψ Yw y P b hWO hWρ hρO hχO hχc hηa hSh hcont hYO hnc _ hb _ hrel
  refine TameLim.core l Ω W c n (fun r x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) θ ρ ψ Yw y P b
    hWO hWρ hρO (fun r x => Subalgebra.mul_mem _ (TameLim.inv_pow_mem c e _ (TameLim.val_unit r x)) (hχO r x))
    (fun r x => ?_) hηa hSh hcont hYO hnc hb hrel
  exact TameLim.mul_sub_mul_le _ _ _ _ _
    (TameLim.norm_le_one_of_mem c (TameLim.inv_pow_mem c e _ (TameLim.val_unit (r + 1) x)))
    (TameLim.norm_le_one_of_mem c (hχO r _)) (GlobalTheory.PowCong.powCong l e r x).1 (hχc r x)

end GlobalTheory.KA
