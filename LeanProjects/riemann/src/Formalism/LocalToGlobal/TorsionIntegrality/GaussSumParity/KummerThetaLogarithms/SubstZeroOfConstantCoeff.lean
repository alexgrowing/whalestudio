import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.LetterShift
import Formalism.GL3MeanSquares.HookFormulaTorsion.BimultiplicativeDivisibleTorsion

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)

namespace TorusDerivation

section Gen

variable {K : Type} [Field K]

theorem coeff_subst_scale {τ : Type} [Fintype τ] (a : τ → K) (f : MvPowerSeries τ K) (n : τ →₀ ℕ) :
    MvPowerSeries.coeff n
        (MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) f) =
      (∏ s, a s ^ n s) * MvPowerSeries.coeff n f := by
  have ht : (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) =
      a • (MvPowerSeries.X : τ → MvPowerSeries τ K) := by
    funext s
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [ht, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem hasSubst_scale {τ : Type} [Finite τ] (a : τ → K) :
    MvPowerSeries.HasSubst (fun s => MvPowerSeries.C (a s) * (MvPowerSeries.X s : MvPowerSeries τ K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp)

theorem subst_sum {σ' τ α : Type} {a : σ' → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (S : Finset α) (F : α → MvPowerSeries σ' K) :
    MvPowerSeries.subst a (∑ i ∈ S, F i) = ∑ i ∈ S, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]

theorem subst_C_mul {σ' τ : Type} {a : σ' → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (c : K) (f : MvPowerSeries σ' K) :
    MvPowerSeries.subst a (MvPowerSeries.C c * f) = MvPowerSeries.C c * MvPowerSeries.subst a f := by
  rw [← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.subst_smul ha, MvPowerSeries.smul_eq_C_mul]

theorem subst_zero {σ' τ : Type} {a : σ' → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (0 : MvPowerSeries σ' K) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_zero]

theorem hasSubst_pair {τ : Type} {A B : MvPowerSeries τ K} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) : MvPowerSeries.HasSubst ![A, B] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hA, hB])

theorem subst_pair {τ κ : Type} {A B : MvPowerSeries τ K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0)
    {b : τ → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b) (G : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.subst b (MvPowerSeries.subst ![A, B] G) =
      MvPowerSeries.subst ![MvPowerSeries.subst b A, MvPowerSeries.subst b B] G := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair hA hB) hb]
  congr 1
  funext i
  fin_cases i <;> simp

theorem subst_right_zero {τ : Type} {G : MvPowerSeries (Fin 2) K} (hG : DivAB G)
    {A : MvPowerSeries τ K} (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.subst ![A, 0] G = 0 := by
  ext e
  rw [MvPowerSeries.coeff_subst (hasSubst_pair hA (map_zero _)), map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  by_cases h : m 1 = 0
  · rw [hG m (Or.inr h), zero_smul]
  · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp [zero_pow h]

theorem subst_left_zero {τ : Type} {G : MvPowerSeries (Fin 2) K} (hG : DivAB G)
    {B : MvPowerSeries τ K} (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.subst ![0, B] G = 0 := by
  ext e
  rw [MvPowerSeries.coeff_subst (hasSubst_pair (map_zero _) hB), map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  by_cases h : m 0 = 0
  · rw [hG m (Or.inl h), zero_smul]
  · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp [zero_pow h]

theorem divAB_of_axes {H : MvPowerSeries (Fin 2) K}
    (h1 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H = 0)
    (h0 : MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H = 0) :
    DivAB H := by
  intro n hn
  rcases hn with hn | hn
  · have e : (fun s : Fin 2 => MvPowerSeries.C ((![0, 1] : Fin 2 → K) s) * MvPowerSeries.X s) =
        ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := by
      funext i
      fin_cases i <;> simp
    have := coeff_subst_scale (![0, 1] : Fin 2 → K) H n
    rw [e, h0, Fin.prod_univ_two] at this
    simpa [hn] using this.symm
  · have e : (fun s : Fin 2 => MvPowerSeries.C ((![1, 0] : Fin 2 → K) s) * MvPowerSeries.X s) =
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] := by
      funext i
      fin_cases i <;> simp
    have := coeff_subst_scale (![1, 0] : Fin 2 → K) H n
    rw [e, h1, Fin.prod_univ_two] at this
    simpa [hn] using this.symm

theorem constantCoeff_expF (l : ℕ) : PowerSeries.constantCoeff (expF K l) = 0 := by
  unfold expF
  split_ifs with h
  · simp
  · simp

theorem constantCoeff_inVar {ι : Type} (x : ι) (f : PowerSeries K)
    (hf : PowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (at1 x f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf

theorem subst_single_var {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : MvPowerSeries.HasSubst b)
    (x : ι) (f : PowerSeries K) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  have h := MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X x :
    PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K)).const hb f
  rw [MvPowerSeries.subst_X hb] at h
  exact h

theorem subst_zero_of_constantCoeff {κ : Type} (f : PowerSeries K)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries κ K) f = 0 := by
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)), map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : PowerSeries.coeff 0 f = 0 := by simpa using hf
    rw [this, zero_smul]
  · rw [zero_pow hm.ne', map_zero, smul_zero]

theorem divAB_addC (l : ℕ) {be0 : MvPowerSeries (Fin 2) K} (h : DivAB be0) :
    DivAB (addC l be0) := by
  have hE := constantCoeff_expF (K := K) l
  have h0 := constantCoeff_inVar (0 : Fin 2) _ hE
  have h1 := constantCoeff_inVar (1 : Fin 2) _ hE
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  refine divAB_of_axes ?_ ?_
  · have hb := hasSubst_pair hX0 (map_zero (MvPowerSeries.constantCoeff (σ := Fin 2) (R := K)))
    unfold addC
    rw [subst_pair h0 h1 hb, subst_single_var hb, subst_single_var hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [subst_zero_of_constantCoeff _ hE]
    exact subst_right_zero h (PowerSeries.constantCoeff_subst_eq_zero hX0 _ hE)
  · have hb := hasSubst_pair (map_zero (MvPowerSeries.constantCoeff (σ := Fin 2) (R := K))) hX1
    unfold addC
    rw [subst_pair h0 h1 hb, subst_single_var hb, subst_single_var hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [subst_zero_of_constantCoeff _ hE]
    exact subst_left_zero h (PowerSeries.constantCoeff_subst_eq_zero hX1 _ hE)

variable {d : ℕ} [NeZero d]

theorem constantCoeff_linE (σ : K →+* K) (c : K) :
    MvPowerSeries.constantCoeff (linE (d := d) σ c) = 0 := by
  unfold linE
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  split_ifs <;> simp

theorem constantCoeff_linO (σ : K →+* K) (c : K) :
    MvPowerSeries.constantCoeff (linO (d := d) σ c) = 0 := by
  unfold linO
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  split_ifs <;> simp

theorem subst_scale_linE (σ : K →+* K) (c : K) (a : ZMod d → K) :
    MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) (linE (d := d) σ c) =
      ∑ s : ZMod d, if s.val % 2 = 0 then MvPowerSeries.C (σ^[s.val] c * a s) * MvPowerSeries.X s
        else 0 := by
  have hs := hasSubst_scale a
  unfold linE
  rw [subst_sum hs]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [subst_C_mul hs, MvPowerSeries.subst_X hs, map_mul, mul_assoc]
  · exact subst_zero hs

theorem subst_scale_linO (σ : K →+* K) (c : K) (a : ZMod d → K) :
    MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) (linO (d := d) σ c) =
      ∑ s : ZMod d, if s.val % 2 = 0 then 0
        else MvPowerSeries.C (σ^[s.val] c * a s) * MvPowerSeries.X s := by
  have hs := hasSubst_scale a
  unfold linO
  rw [subst_sum hs]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · exact subst_zero hs
  · rw [subst_C_mul hs, MvPowerSeries.subst_X hs, map_mul, mul_assoc]

theorem iter_pow (σ : K →+* K) {u : K} {l : ℕ} (h : σ u = u ^ l) (k : ℕ) :
    σ^[k] u = u ^ (l ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, map_pow, h, ← pow_mul, pow_succ, mul_comm]

end Gen

end TorusDerivation

open TorusDerivation

theorem torus_coefficient : TorusCoeff := by
  intro K _ l d _ u f n
  exact coeff_subst_scale (fun s => u ^ lw l s) f n

theorem torus_tilde : TorusTil := by
  intro K _ l d _ σ _ be0 ι _ om oms u hu hσ
  have hs : MvPowerSeries.HasSubst (torus (d := d) l u) := hasSubst_scale (fun s => u ^ lw l s)
  unfold beTil
  rw [subst_sum hs]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [subst_pair (constantCoeff_linE _ _) (constantCoeff_linO _ _) hs]
  have hE : MvPowerSeries.subst (torus (d := d) l u) (linE σ (oms r)) = linE σ (u * oms r) := by
    refine (subst_scale_linE σ (oms r) (fun s => u ^ lw l s)).trans ?_
    unfold linE
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · have e : σ^[s.val] (oms r) * u ^ lw l s = σ^[s.val] (u * oms r) := by
        rw [← RingHom.coe_pow, map_mul, RingHom.coe_pow, iter_pow σ hσ, lw, if_pos h, one_mul,
          ← Nat.cast_pow, zpow_natCast, mul_comm]
      rw [e]
    · rfl
  have hO : MvPowerSeries.subst (torus (d := d) l u) (linO σ (om r)) = linO σ (u⁻¹ * om r) := by
    refine (subst_scale_linO σ (om r) (fun s => u ^ lw l s)).trans ?_
    unfold linO
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · rfl
    · have e : σ^[s.val] (om r) * u ^ lw l s = σ^[s.val] (u⁻¹ * om r) := by
        rw [← RingHom.coe_pow, map_mul, map_inv₀, RingHom.coe_pow, iter_pow σ hσ, lw, if_neg h,
          neg_one_mul, zpow_neg, ← Nat.cast_pow, zpow_natCast, mul_comm]
      rw [e]
  rw [hE, hO]

namespace TorusDerivation

section Mean

variable {K : Type} [Field K] {d : ℕ} [NeZero d]

def wt (l : ℕ) (ζ : K) (n : ZMod d →₀ ℕ) : K := ∏ s : ZMod d, (ζ ^ lw l s) ^ n s

theorem coeff_beMean {ι : Type} [Fintype ι] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K)
    (om oms : ι → K) (ζ : K) (n : ZMod d →₀ ℕ) :
    MvPowerSeries.coeff n (beMean l σ be0 om oms ζ) =
      (((l ^ d - 1 : ℕ) : K)⁻¹) * ((∑ k ∈ Finset.range (l ^ d - 1), wt l ζ n ^ k) *
        MvPowerSeries.coeff n (beTil l σ be0 om oms)) := by
  unfold beMean
  rw [MvPowerSeries.coeff_C_mul, map_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [torus_coefficient]
  congr 1
  unfold wt
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun s _ => ?_
  have e : (ζ ^ k) ^ lw l s = (ζ ^ lw l s) ^ k := by
    rw [← zpow_natCast ζ k, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  rw [e, ← pow_mul, ← pow_mul, mul_comm]

theorem wt_pow {l N : ℕ} {ζ : K} (h : ζ ^ N = 1) (n : ZMod d →₀ ℕ) : wt l ζ n ^ N = 1 := by
  unfold wt
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun s _ => ?_
  have e : (ζ ^ lw l s) ^ N = 1 := by
    rw [← zpow_natCast (ζ ^ lw l s) N, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]
  rw [← pow_mul, mul_comm, pow_mul, e, one_pow]

theorem mul_geom {w : K} {N : ℕ} (h : w ^ N = 1) :
    w * ∑ k ∈ Finset.range N, w ^ k = ∑ k ∈ Finset.range N, w ^ k := by
  have h1 := Finset.sum_range_succ (fun k => w ^ k) N
  have h2 := Finset.sum_range_succ' (fun k => w ^ k) N
  have h3 := h2.symm.trans h1
  rw [h, pow_zero] at h3
  rw [Finset.mul_sum, ← add_right_cancel h3]
  exact Finset.sum_congr rfl fun k _ => (pow_succ' w k).symm

theorem geom_zero {w : K} {N : ℕ} (h : w ^ N = 1) (h1 : w ≠ 1) :
    ∑ k ∈ Finset.range N, w ^ k = 0 := by
  have h2 := mul_geom_sum w N
  rw [h, sub_self] at h2
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h1)

theorem coeff_pair_degO {G : MvPowerSeries (Fin 2) K} (hG : DivAB G) (σ : K →+* K) (c c' : K)
    {n : ZMod d →₀ ℕ} (hn : degO n = 0) :
    MvPowerSeries.coeff n (MvPowerSeries.subst ![linE σ c, linO σ c'] G) = 0 := by
  set a : ZMod d → K := fun s => if s.val % 2 = 0 then 1 else 0 with ha
  have h := coeff_subst_scale a (MvPowerSeries.subst ![linE σ c, linO σ c'] G) n
  have hp : ∏ s, a s ^ n s = 1 := by
    refine Finset.prod_eq_one fun s _ => ?_
    by_cases hs : s.val % 2 = 0
    · simp [ha, hs]
    · have := (Finset.sum_eq_zero_iff.1 hn) s (Finset.mem_univ s)
      rw [if_neg hs] at this
      rw [this, pow_zero]
  have hO : MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s)
      (linO (d := d) σ c') = 0 := by
    rw [subst_scale_linO]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · rfl
    · simp [ha, hs]
  have hE : MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s)
      (linE (d := d) σ c) = linE σ c := by
    rw [subst_scale_linE]
    unfold linE
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with hs
    · simp [ha, hs]
    · rfl
  rw [hp, one_mul, subst_pair (constantCoeff_linE _ _) (constantCoeff_linO _ _) (hasSubst_scale a),
    hO, hE, subst_right_zero hG (constantCoeff_linE _ _), map_zero] at h
  exact h.symm

theorem coeff_pair_degE {G : MvPowerSeries (Fin 2) K} (hG : DivAB G) (σ : K →+* K) (c c' : K)
    {n : ZMod d →₀ ℕ} (hn : degE n = 0) :
    MvPowerSeries.coeff n (MvPowerSeries.subst ![linE σ c, linO σ c'] G) = 0 := by
  set a : ZMod d → K := fun s => if s.val % 2 = 0 then 0 else 1 with ha
  have h := coeff_subst_scale a (MvPowerSeries.subst ![linE σ c, linO σ c'] G) n
  have hp : ∏ s, a s ^ n s = 1 := by
    refine Finset.prod_eq_one fun s _ => ?_
    by_cases hs : s.val % 2 = 0
    · have := (Finset.sum_eq_zero_iff.1 hn) s (Finset.mem_univ s)
      rw [if_pos hs] at this
      rw [this, pow_zero]
    · simp [ha, hs]
  have hE : MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s)
      (linE (d := d) σ c) = 0 := by
    rw [subst_scale_linE]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · simp [ha, hs]
    · rfl
  have hO : MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s)
      (linO (d := d) σ c') = linO σ c' := by
    rw [subst_scale_linO]
    unfold linO
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with hs
    · rfl
    · simp [ha, hs]
  rw [hp, one_mul, subst_pair (constantCoeff_linE _ _) (constantCoeff_linO _ _) (hasSubst_scale a),
    hO, hE, subst_left_zero hG (constantCoeff_linO _ _), map_zero] at h
  exact h.symm

theorem exists_of_sum_eq_one {α : Type} [Fintype α] (f : α → ℕ) (h : ∑ s, f s = 1) :
    ∃ s, f s = 1 ∧ ∀ t, t ≠ s → f t = 0 := by
  classical
  have h0 : ∃ s, f s ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at h
  obtain ⟨s, hs⟩ := h0
  have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ s)
  rw [h] at h2
  have h3 : ∑ t ∈ Finset.univ.erase s, f t = 0 := by omega
  exact ⟨s, by omega, fun t ht =>
    (Finset.sum_eq_zero_iff.1 h3) t (Finset.mem_erase.2 ⟨ht, Finset.mem_univ t⟩)⟩

theorem wt_ne_one {l : ℕ} (hl : 2 ≤ l) {ζ : K} (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    {n : ZMod d →₀ ℕ} (hE : degE n = 1) (hO : degO n = 1) : wt l ζ n ≠ 1 := by
  classical
  have hd : d ≠ 0 := NeZero.ne d
  have hN : l ^ d - 1 ≠ 0 := by
    have := Nat.one_lt_pow hd (show 1 < l by omega)
    omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  obtain ⟨s, hs1, hs⟩ := exists_of_sum_eq_one _ hE
  obtain ⟨t, ht1, ht⟩ := exists_of_sum_eq_one _ hO
  have hse : s.val % 2 = 0 := by
    by_contra hc
    rw [if_neg hc] at hs1
    omega
  have hto : ¬ t.val % 2 = 0 := by
    intro hc
    rw [if_pos hc] at ht1
    omega
  rw [if_pos hse] at hs1
  rw [if_neg hto] at ht1
  have hst : s ≠ t := fun h => hto (h ▸ hse)
  have hw : wt l ζ n = ζ ^ (lw l s + lw l t) := by
    unfold wt
    rw [Finset.prod_eq_mul s t hst, hs1, ht1, pow_one, pow_one, zpow_add₀ hζ0]
    · rintro c - ⟨hcs, hct⟩
      have hc0 : n c = 0 := by
        by_cases hc : c.val % 2 = 0
        · have := hs c hcs
          rwa [if_pos hc] at this
        · have := ht c hct
          rwa [if_neg hc] at this
      rw [hc0, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ s) h
    · intro h
      exact absurd (Finset.mem_univ t) h
  intro h1
  rw [hw, hζ.zpow_eq_one_iff_dvd] at h1
  have e : lw l s + lw l t = (l : ℤ) ^ s.val - (l : ℤ) ^ t.val := by
    unfold lw
    rw [if_pos hse, if_neg hto]
    ring
  rw [e] at h1
  have := Formalism.HermitianLattices.IntegralLatticeDensity.no_form_of_bidegree_one_one l d s.val t.val hl (ZMod.val_lt s) (ZMod.val_lt t) h1
  rw [this] at hse
  exact hto hse

end Mean

end TorusDerivation

theorem second_mean_condition : MeanTorusInvariant := by
  intro K _ l d _ σ be0 ι _ om oms ζ hζ
  ext n
  rw [torus_coefficient, coeff_beMean]
  change wt l ζ n * _ = _
  rw [mul_left_comm, ← mul_assoc (wt l ζ n), mul_geom (wt_pow hζ n)]

theorem third_mean_condition : MeanNoLowBidegreeTerms := by
  intro K _ _ l d _ σ hl _ _ be0 hbe ι _ om oms ζ hζ n hn
  rw [coeff_beMean] at hn
  have hG := divAB_addC l hbe
  have hT : MvPowerSeries.coeff n (beTil l σ be0 om oms) ≠ 0 := by
    intro h
    apply hn
    rw [h, mul_zero, mul_zero]
  have hS : ∑ k ∈ Finset.range (l ^ d - 1), wt l ζ n ^ k ≠ 0 := by
    intro h
    apply hn
    rw [h, zero_mul, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => hT ?_
    unfold beTil
    rw [map_sum]
    exact Finset.sum_eq_zero fun r _ => coeff_pair_degE hG σ _ _ h
  · refine Nat.pos_of_ne_zero fun h => hT ?_
    unfold beTil
    rw [map_sum]
    exact Finset.sum_eq_zero fun r _ => coeff_pair_degO hG σ _ _ h
  · rintro ⟨hE, hO⟩
    exact hS (geom_zero (wt_pow hζ.pow_eq_one n) (wt_ne_one hl hζ hE hO))

end Formalism.L2.Th1.D
