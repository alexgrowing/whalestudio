import Mathlib
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import GroundTheory.PAdicHodge.FieldOfNormsRam
import GroundTheory.PAdicHodge.NormalizedTrace
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel Polynomial Module

theorem sum_range_X_add_one_pow (n : ℕ) :
    ∑ j ∈ Finset.range n, ((X : ℤ[X]) + 1) ^ j =
      ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℤ[X]) * X ^ i := by
  apply mul_left_cancel₀ (X_ne_zero : (X : ℤ[X]) ≠ 0)
  have h1 : (X : ℤ[X]) * ∑ j ∈ Finset.range n, (X + 1) ^ j = (X + 1) ^ n - 1 := by
    have := geom_sum_mul ((X : ℤ[X]) + 1) n
    rw [add_sub_cancel_right] at this
    rw [mul_comm, this]
  have h2 : (X + 1 : ℤ[X]) ^ n - 1 =
      ∑ i ∈ Finset.range n, (X : ℤ[X]) ^ (i + 1) * (n.choose (i + 1) : ℤ[X]) := by
    rw [add_pow, Finset.sum_range_succ']
    simp
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] K]

def galOver (M : IntermediateField K (PadicAlgCl p)) (σ : Gal(PadicAlgCl p/K))
    (hσ : σ ∈ M.fixingSubgroup) : PadicAlgCl p ≃ₐ[M] PadicAlgCl p :=
  { σ.toRingEquiv with
    commutes' := fun m => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ m m.2 }

omit [FiniteDimensional ℚ_[p] K] in
theorem galOver_apply (M : IntermediateField K (PadicAlgCl p)) (σ : Gal(PadicAlgCl p/K))
    (hσ : σ ∈ M.fixingSubgroup) (y : PadicAlgCl p) : galOver M σ hσ y = σ y := rfl

variable (M M' : IntermediateField K (PadicAlgCl p)) (hMM' : M ≤ M') [FiniteDimensional K M']
  {τ : Gal(PadicAlgCl p/K)} (hτM : τ ∈ M.fixingSubgroup)
  (hτp : τ ^ p ∈ M'.fixingSubgroup) (hτ1 : τ ∉ M'.fixingSubgroup)
  (hgen : ∀ σ ∈ M.fixingSubgroup, ∃ j : ℕ, ∀ y ∈ M', σ y = (τ ^ j) y)

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
include hτp hτ1 in

theorem pow_mem_fixingSubgroup_iff (m : ℕ) : τ ^ m ∈ M'.fixingSubgroup ↔ p ∣ m := by
  constructor
  · intro hm
    by_contra hdvd
    have hcop : Nat.Coprime m p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hdvd))
    have hg := Nat.gcd_eq_gcd_ab m p
    rw [hcop.gcd_eq_one, Nat.cast_one] at hg
    have : τ = (τ ^ m) ^ (Nat.gcdA m p) * (τ ^ p) ^ (Nat.gcdB m p) := by
      rw [← zpow_natCast, ← zpow_natCast τ p, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
    exact hτ1 (this ▸ mul_mem (zpow_mem hm _) (zpow_mem hτp _))
  · rintro ⟨c, rfl⟩
    rw [pow_mul]
    exact pow_mem hτp c

section Embeddings

variable {M M'} {hMM'}

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
include hτM in
theorem pow_mem_fixingSubgroup_base (j : ℕ) : τ ^ j ∈ M.fixingSubgroup := pow_mem hτM j

variable (hMM') in

def stepEmb (hτM : τ ∈ M.fixingSubgroup) (j : ℕ) :
    IntermediateField.extendScalars hMM' →ₐ[M] PadicAlgCl p :=
  (galOver M (τ ^ j) (pow_mem hτM j)).toAlgHom.comp (IntermediateField.extendScalars hMM').val

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
theorem stepEmb_apply (j : ℕ) (y : IntermediateField.extendScalars hMM') :
    stepEmb hMM' hτM j y = (τ ^ j) (y : PadicAlgCl p) := rfl

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
include hτp hτ1 in
theorem stepEmb_injective {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : stepEmb hMM' hτM i = stepEmb hMM' hτM j) : i = j := by
  have key : ∀ {a b : ℕ}, a ≤ b → b < p → stepEmb hMM' hτM a = stepEmb hMM' hτM b → a = b := by
    intro a b hab hb h
    have hfix : τ ^ (b - a) ∈ M'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h1 := congrArg (fun φ => φ (⟨y, hy⟩ : IntermediateField.extendScalars hMM')) h
      simp only [stepEmb_apply] at h1
      have e : τ ^ b = τ ^ a * τ ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab]
      rw [e, AlgEquiv.mul_apply] at h1
      exact ((τ ^ a).injective h1).symm
    have hdvd := (pow_mem_fixingSubgroup_iff M' hτp hτ1 (b - a)).1 hfix
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  rcases le_total i j with hij | hji
  · exact key hij hj h
  · exact (key hji hi h.symm).symm

instance isAlgClosure_padicAlgCl_over (E : IntermediateField K (PadicAlgCl p)) :
    IsAlgClosure E (PadicAlgCl p) :=
  haveI : Algebra.IsAlgebraic K (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) E⟩

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional K M'] in
include hτp hgen in
theorem stepEmb_surjective (φ : IntermediateField.extendScalars hMM' →ₐ[M] PadicAlgCl p) :
    ∃ j < p, stepEmb hMM' hτM j = φ := by
  set φ' := φ.liftNormal (PadicAlgCl p)
  have hbij : Function.Bijective φ' := Algebra.IsAlgebraic.algHom_bijective φ'
  let σ : Gal(PadicAlgCl p/K) := (AlgEquiv.ofBijective φ' hbij).restrictScalars K
  have hσ : σ ∈ M.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro m hm
    change φ' (algebraMap M (PadicAlgCl p) ⟨m, hm⟩) = m
    rw [AlgHom.commutes]
    rfl
  obtain ⟨j, hj⟩ := hgen σ hσ
  have hp0 : 0 < p := hp.out.pos
  refine ⟨j % p, Nat.mod_lt _ hp0, ?_⟩
  ext y
  rw [stepEmb_apply]
  have h1 : φ y = φ' (y : PadicAlgCl p) := by
    have := AlgHom.liftNormal_commutes φ (PadicAlgCl p) y
    exact this.symm
  rw [h1]
  change (τ ^ (j % p)) (y : PadicAlgCl p) = σ y
  rw [hj y y.2]
  have e : τ ^ j = τ ^ (j % p) * (τ ^ p) ^ (j / p) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [e, AlgEquiv.mul_apply]
  congr 1
  exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (pow_mem hτp _) y y.2).symm

end Embeddings

variable {M M'} {hMM'}

omit [FiniteDimensional ℚ_[p] K] in
theorem finiteDimensional_extendScalars_of_le :
    FiniteDimensional M (IntermediateField.extendScalars hMM') := by
  apply Module.finite_of_finrank_pos
  have h : 0 < Module.finrank K M' := Module.finrank_pos
  rw [finrank_eq_mul_finrank_extendScalars hMM'] at h
  exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at h

include hMM' hτM hτp hτ1 hgen in
omit [FiniteDimensional ℚ_[p] K] in

theorem natCast_mul_normTrace_eq_sum {y : PadicAlgCl p} (hy : y ∈ M') :
    (p : PadicAlgCl p) * normTrace M y = ∑ j ∈ Finset.range p, (τ ^ j) y := by
  have := finiteDimensional_extendScalars_of_le (M := M) (M' := M') (hMM' := hMM')
  set E := IntermediateField.extendScalars hMM'
  let e : Fin p → (E →ₐ[M] PadicAlgCl p) := fun j => stepEmb hMM' hτM j.1
  have he : Function.Bijective e := by
    refine ⟨fun i j h => Fin.ext (stepEmb_injective hτM hτp hτ1 i.2 j.2 h), fun φ => ?_⟩
    obtain ⟨j, hj, hφ⟩ := stepEmb_surjective hτM hτp hgen φ
    exact ⟨⟨j, hj⟩, hφ⟩
  have hcard : Module.finrank M E = p := by
    rw [← AlgHom.card M E (PadicAlgCl p), ← Fintype.card_of_bijective he, Fintype.card_fin]
  set y' : E := ⟨y, hy⟩
  have hyy : y = algebraMap E (PadicAlgCl p) y' := rfl
  have htr := trace_eq_sum_embeddings (K := M) (L := E) (PadicAlgCl p) (x := y')
  have hsum : ∑ σ : E →ₐ[M] PadicAlgCl p, σ y' = ∑ j ∈ Finset.range p, (τ ^ j) y := by
    rw [← Fintype.sum_bijective e he (fun j => e j y') (fun σ => σ y') (fun _ => rfl),
      ← Fin.sum_univ_eq_sum_range (fun j => (τ ^ j) y)]
    rfl
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [normTrace, hyy, normTraceF_eq_trace_div M E y', hcard, map_div₀, htr, hsum, map_natCast,
    mul_div_cancel₀ _ hp0]
  rfl

omit [FiniteDimensional ℚ_[p] K] in

theorem sum_range_pow_apply_eq (τ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    ∑ j ∈ Finset.range n, (τ ^ j) y = ∑ i ∈ Finset.range n, (n.choose (i + 1) : PadicAlgCl p) *
      (((τ.toLinearMap : Module.End K (PadicAlgCl p)) - 1) ^ i) y := by
  set T : Module.End K (PadicAlgCl p) := τ.toLinearMap
  set D := T - 1
  have hT : ∀ (j : ℕ) (z : PadicAlgCl p), (T ^ j) z = (τ ^ j) z := by
    intro j
    induction j with
    | zero => intro z; rfl
    | succ j ih =>
      intro z
      rw [pow_succ, Module.End.mul_apply, pow_succ, AlgEquiv.mul_apply, ih]
      rfl
  have key := congrArg (fun P => (Polynomial.aeval D P) y) (sum_range_X_add_one_pow n)
  simp only [map_sum, map_pow, map_add, aeval_X, map_one, map_mul, map_natCast] at key
  rw [LinearMap.sum_apply, LinearMap.sum_apply] at key
  simp only [Module.End.mul_apply, Module.End.natCast_apply, nsmul_eq_mul] at key
  rw [sub_add_cancel] at key
  rw [← key]
  exact Finset.sum_congr rfl fun j _ => (hT j y).symm

omit [FiniteDimensional K M'] in

theorem nrm_pow_sub_one_apply_le (τ : Gal(PadicAlgCl p/K)) (hτM' : ∀ z ∈ M', τ z ∈ M') {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ z ∈ M', nrm K (τ z - z) ≤ ρ * nrm K z) {y : PadicAlgCl p} (hy : y ∈ M') (i : ℕ) :
    (((τ.toLinearMap : Module.End K (PadicAlgCl p)) - 1) ^ i) y ∈ M' ∧
      nrm K ((((τ.toLinearMap : Module.End K (PadicAlgCl p)) - 1) ^ i) y) ≤ ρ ^ i * nrm K y := by
  induction i with
  | zero => simpa using hy
  | succ i ih =>
    set D : Module.End K (PadicAlgCl p) := τ.toLinearMap - 1
    have e : (D ^ (i + 1)) y = τ ((D ^ i) y) - (D ^ i) y := by
      rw [pow_succ', Module.End.mul_apply]
      rfl
    rw [e]
    refine ⟨sub_mem (hτM' _ ih.1) ih.1, ?_⟩
    calc nrm K (τ ((D ^ i) y) - (D ^ i) y) ≤ ρ * nrm K ((D ^ i) y) := hρ _ ih.1
      _ ≤ ρ * (ρ ^ i * nrm K y) := mul_le_mul_of_nonneg_left ih.2 hρ0
      _ = ρ ^ (i + 1) * nrm K y := by ring

include hMM' hτM hτp hτ1 hgen in

theorem nrm_normTrace_mul_le (hτM' : ∀ z ∈ M', τ z ∈ M') {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρ : ∀ z ∈ M', nrm K (τ z - z) ≤ ρ * nrm K z) {y : PadicAlgCl p} (hy : y ∈ M') :
    nrm K (normTrace M y) * nrm K (p : PadicAlgCl p) ≤
      max (nrm K (p : PadicAlgCl p)) (ρ ^ (p - 1)) * nrm K y := by
  have hsum := natCast_mul_normTrace_eq_sum (hMM' := hMM') hτM hτp hτ1 hgen hy
  rw [sum_range_pow_apply_eq] at hsum
  rw [mul_comm, ← nrm_mul, hsum]
  set C := max (nrm K (p : PadicAlgCl p)) (ρ ^ (p - 1)) * nrm K y
  have hC : 0 ≤ C := mul_nonneg (le_trans (nrm_nonneg _) (le_max_left _ _)) (nrm_nonneg _)
  refine nrm_sum_le hC fun i hi => ?_
  rw [Finset.mem_range] at hi
  obtain ⟨-, hDi⟩ := nrm_pow_sub_one_apply_le τ hτM' hρ0 hρ hy i
  rw [nrm_mul]
  have hρi : ρ ^ i ≤ 1 := pow_le_one₀ hρ0 hρ1
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 (show i < p - 1 + 1 by omega)) with hlt | heq
  ·
    obtain ⟨c, hc⟩ := hp.out.dvd_choose_self (by omega : i + 1 ≠ 0) (by omega : i + 1 < p)
    rw [hc, Nat.cast_mul, nrm_mul]
    have hc1 := nrm_natCast_le_one (K := K) (Ω := PadicAlgCl p) c
    have hp1 := nrm_natCast_le_one (K := K) (Ω := PadicAlgCl p) p
    calc nrm K (p : PadicAlgCl p) * nrm K (c : PadicAlgCl p) *
          nrm K ((((τ.toLinearMap : Module.End K (PadicAlgCl p)) - 1) ^ i) y)
        ≤ nrm K (p : PadicAlgCl p) * 1 * (1 * nrm K y) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc1 (nrm_nonneg _))
            (hDi.trans (mul_le_mul_of_nonneg_right hρi (nrm_nonneg _))) (nrm_nonneg _)
            (by rw [mul_one]; exact nrm_nonneg _)
      _ ≤ C := by
          rw [one_mul, mul_one]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (nrm_nonneg _)
  ·
    have hi' : i + 1 = p := by omega
    rw [hi', Nat.choose_self, Nat.cast_one, nrm_one, one_mul]
    rw [heq] at hDi
    rw [heq]
    exact hDi.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (nrm_nonneg _))

end SenTateChar

end GroundTheory.PAdicHodge
