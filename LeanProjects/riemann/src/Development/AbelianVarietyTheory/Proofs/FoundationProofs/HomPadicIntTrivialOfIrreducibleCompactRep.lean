import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeightCommutatorInvariance
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationCombinationEqIdTracelessIrreduStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisHomZlLipschitzOfKerLeLinearGroupStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

open GlobalTheory.SmallMat

theorem noab_inv_det_one {K : Type} [Field K] (A : GL (Fin 2) K) (h : (A : Matrix (Fin 2) (Fin 2) K).det = 1) :
    ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K).trace • 1 - A := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, h, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.trace_fin_two]

theorem noab_trace_eq {K : Type} [Field K] (Z : Matrix (Fin 2) (Fin 2) K) (h : (1 + Z).det = 1) : Z.trace = - Z.det := by
  rw [Matrix.det_fin_two] at h
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  simp [Matrix.add_apply, Matrix.one_apply] at h
  linear_combination h

theorem noab_norm_two (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ ≤ ‖(2 : Qbar l)‖ := by
  have e : ∀ m : ℕ, ‖((m : ℕ) : Qbar l)‖ = ‖((m : ℕ) : ℚ_[l])‖ := fun m => by
    rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  have e2 : (2 : Qbar l) = ((2 : ℕ) : Qbar l) := by norm_num
  rw [e2, e, e]
  by_cases h2 : l = 2
  · subst h2; exact le_rfl
  · rw [Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 h2), Padic.norm_p]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)

theorem noab_pow : ∀ (l : ℕ) [Fact l.Prime] (ε : ℝ) (Z : Matrix (Fin 2) (Fin 2) (Qbar l)), 0 ≤ ε → ε ≤ 1 →
    GlobalTheory.SmallMat.Sm ε Z → ∀ b : ℕ, GlobalTheory.SmallMat.Sm (ε ^ 2) ((1 + Z) ^ b - 1 - (b : Qbar l) • Z) := by
  intro l _ ε Z hε0 hε1 hZ b
  have hε2 : ε ^ 2 * ε ≤ ε ^ 2 := by simpa using mul_le_mul_of_nonneg_left hε1 (sq_nonneg ε)
  induction b with
  | zero => simpa using GlobalTheory.SmallMat.sm_zero (l := l) (sq_nonneg ε)
  | succ b ih =>
    have e : (1 + Z) ^ (b + 1) - 1 - ((b + 1 : ℕ) : Qbar l) • Z = ((1 + Z) ^ b - 1 - (b : Qbar l) • Z)
        + ((1 + Z) ^ b - 1 - (b : Qbar l) • Z) * Z + (b : Qbar l) • (Z * Z) := by
      simp only [pow_succ, Nat.cast_succ, add_smul, one_smul, mul_add, add_mul, sub_mul, mul_one, one_mul,
        Matrix.smul_mul]
      abel
    rw [e]
    refine (ih.add ((ih.mul hZ (sq_nonneg ε)).mono hε2)).add ?_
    refine ((hZ.mul hZ hε0).smul_le (mul_nonneg hε0 hε0) (GlobalTheory.SmallMat.norm_natCast_le_one b)).mono (le_of_eq (sq ε).symm)

theorem noab_sum_list : ∀ (l : ℕ) [Fact l.Prime] (ε : ℝ) (L : List (Matrix (Fin 2) (Fin 2) (Qbar l))), 0 ≤ ε →
    (∀ M ∈ L, GlobalTheory.SmallMat.Sm ε (M - 1)) → GlobalTheory.SmallMat.Sm ε ((L.map (fun M => M - 1)).sum) := by
  intro l _ ε L hε0 hL
  induction L with
  | nil => simpa using GlobalTheory.SmallMat.sm_zero (l := l) hε0
  | cons M L ih =>
    rw [List.map_cons, List.sum_cons]
    exact (hL M (by simp)).add (ih fun N hN => hL N (by simp [hN]))

theorem noab_prod : ∀ (l : ℕ) [Fact l.Prime] (ε : ℝ) (L : List (Matrix (Fin 2) (Fin 2) (Qbar l))), 0 ≤ ε → ε ≤ 1 →
    (∀ M ∈ L, GlobalTheory.SmallMat.Sm ε (M - 1)) →
    GlobalTheory.SmallMat.Sm (ε ^ 2) (L.prod - 1 - (L.map (fun M => M - 1)).sum) := by
  intro l _ ε L hε0 hε1 hL
  have hε2 : ε ^ 2 ≤ ε := by simpa [sq] using mul_le_mul_of_nonneg_left hε1 hε0
  induction L with
  | nil => simpa using GlobalTheory.SmallMat.sm_zero (l := l) (sq_nonneg ε)
  | cons M L ih =>
    have hL' : ∀ N ∈ L, GlobalTheory.SmallMat.Sm ε (N - 1) := fun N hN => hL N (by simp [hN])
    have hM : GlobalTheory.SmallMat.Sm ε (M - 1) := hL M (by simp)
    have ih' := ih hL'
    have hS := noab_sum_list l ε L hε0 hL'
    have hP : GlobalTheory.SmallMat.Sm ε (L.prod - 1) := by
      have := (ih'.mono hε2).add hS; rwa [sub_add_cancel] at this
    have e : (M :: L).prod - 1 - ((M :: L).map (fun M => M - 1)).sum =
        (M - 1) * (L.prod - 1) + (L.prod - 1 - (L.map (fun M => M - 1)).sum) := by
      rw [List.prod_cons, List.map_cons, List.sum_cons]
      simp only [sub_mul, mul_sub, one_mul, mul_one]
      abel
    rw [e]
    exact ((hM.mul hP hε0).mono (le_of_eq (sq ε).symm)).add ih'

theorem noab_denom : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (a : Fin N → ℚ_[l]), ∃ s : ℕ, ∀ i, ‖((l : ℕ) : ℚ_[l]) ^ s * a i‖ ≤ 1 := by
  intro l _ N a
  have hρ : ‖((l : ℕ) : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hex : ∀ i, ∃ s : ℕ, ‖((l : ℕ) : ℚ_[l])‖ ^ s * ‖a i‖ ≤ 1 := fun i => by
    by_cases h : a i = 0
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 h)) hρ
      refine ⟨s, ?_⟩
      rw [← le_div_iff₀ (norm_pos_iff.2 h), one_div]
      exact hs.le
  choose f hf using hex
  refine ⟨∑ i, f i, fun i => ?_⟩
  rw [norm_mul, norm_pow]
  exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (norm_nonneg _) hρ.le
    (Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i))) (norm_nonneg _)) (hf i)

theorem noab_comm : ∀ (l : ℕ) [Fact l.Prime] (ε : ℝ) (A A' Z Z' : Matrix (Fin 2) (Fin 2) (Qbar l)) (β : ℕ), 0 ≤ ε → ε ≤ 1 →
    A * A' = 1 → GlobalTheory.SmallMat.Sm 1 A → GlobalTheory.SmallMat.Sm 1 A' → GlobalTheory.SmallMat.Sm ε Z → GlobalTheory.SmallMat.Sm (ε ^ 2) (Z' + Z) →
    GlobalTheory.SmallMat.Sm (ε ^ 2) (A * (1 + Z) ^ β * A' * (1 + Z') ^ β - 1 - (β : Qbar l) • (A * Z * A' - Z)) := by
  intro l _ ε A A' Z Z' β hε0 hε1 hAA' hA hA' hZ hZZ
  have hε2 : ε ^ 2 ≤ ε := by simpa [sq] using mul_le_mul_of_nonneg_left hε1 hε0
  have hZ' : GlobalTheory.SmallMat.Sm ε Z' := by
    have := (hZZ.mono hε2).sub hZ; rwa [add_sub_cancel_right] at this
  have hE := noab_pow l ε Z hε0 hε1 hZ β
  have hE' := noab_pow l ε Z' hε0 hε1 hZ' β
  have hU : GlobalTheory.SmallMat.Sm ε ((1 + Z) ^ β - 1) := by
    have := (hE.mono hε2).add (hZ.smul_le hε0 (GlobalTheory.SmallMat.norm_natCast_le_one β)); rwa [sub_add_cancel] at this
  have hV : GlobalTheory.SmallMat.Sm ε ((1 + Z') ^ β - 1) := by
    have := (hE'.mono hε2).add (hZ'.smul_le hε0 (GlobalTheory.SmallMat.norm_natCast_le_one β)); rwa [sub_add_cancel] at this
  have e : A * (1 + Z) ^ β * A' * (1 + Z') ^ β - 1 - (β : Qbar l) • (A * Z * A' - Z) =
      A * ((1 + Z) ^ β - 1 - (β : Qbar l) • Z) * A' + ((1 + Z') ^ β - 1 - (β : Qbar l) • Z') + (β : Qbar l) • (Z' + Z)
      + (A * ((1 + Z) ^ β - 1) * A') * ((1 + Z') ^ β - 1) := by
    generalize (1 + Z) ^ β = P
    generalize (1 + Z') ^ β = P'
    simp only [mul_sub, sub_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub, mul_assoc,
      ← mul_assoc A A', hAA']
    abel
  rw [e]
  have h1 : GlobalTheory.SmallMat.Sm (ε ^ 2) (A * ((1 + Z) ^ β - 1 - (β : Qbar l) • Z) * A') := by
    have := (hA.mul hE zero_le_one).mul hA' (by positivity); rwa [one_mul, mul_one] at this
  have h3 : GlobalTheory.SmallMat.Sm (ε ^ 2) ((β : Qbar l) • (Z' + Z)) :=
    hZZ.smul_le (sq_nonneg ε) (GlobalTheory.SmallMat.norm_natCast_le_one β)
  have h4 : GlobalTheory.SmallMat.Sm (ε ^ 2) ((A * ((1 + Z) ^ β - 1) * A') * ((1 + Z') ^ β - 1)) := by
    have := ((hA.mul hU zero_le_one).mul hA' (by positivity)).mul hV (by positivity)
    rwa [one_mul, mul_one, ← sq] at this
  exact ((h1.add hE').add h3).add h4

theorem noab_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)), Continuous r →
    (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) →
    (∀ g, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det ^ 2 = 1) → ∀ g : Γ, ∃ k : ℕ, 0 < k ∧
      (r (g ^ k) : Matrix (Fin 2) (Fin 2) (Qbar l)).det = 1 ∧
      GlobalTheory.SmallMat.Sm ‖((l : ℕ) : Qbar l)‖ ((r (g ^ k) : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) := by
  intro l _ c Γ _ _ _ _ r hr hint hdet g
  set R : Γ →* Matrix (Fin 2) (Fin 2) (Qbar l) := (Units.coeHom _).comp r with hRdef
  have hRint : ∀ x, Sm 1 (R x) := fun x i j => commHt_norm_le_one_of_mem c _ (hint x i j)
  set ρ : ℝ := ‖((l : ℕ) : Qbar l)‖ with hρ
  have hρeq : ρ = (l : ℝ)⁻¹ := by
    rw [hρ, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ0 : 0 < ρ := by rw [hρeq]; positivity
  have hρ1 : ρ < 1 := by rw [hρeq]; exact inv_lt_one_of_one_lt₀ hl1
  have hρρ : ρ * ρ ≤ ρ := by simpa using mul_le_mul_of_nonneg_left hρ1.le hρ0.le
  let U : Subgroup Γ :=
    { carrier := {x | (R x).det = 1 ∧ Sm ρ (R x - 1)}
      one_mem' := by
        refine ⟨by simp, ?_⟩
        rw [map_one, sub_self]; exact sm_zero hρ0.le
      mul_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨by rw [map_mul, Matrix.det_mul, hx1, hy1, one_mul], ?_⟩
        have e : R (x * y) - 1 = (R x - 1) + (R y - 1) + (R x - 1) * (R y - 1) := by
          rw [map_mul]; simp only [sub_mul, mul_sub, one_mul, mul_one]; abel
        rw [e]
        exact (hx2.add hy2).add ((hx2.mul hy2 hρ0.le).mono hρρ)
      inv_mem' := by
        rintro x ⟨hx1, hx2⟩
        have hinv : R x⁻¹ = (R x).trace • 1 - R x := by
          simp only [hRdef, MonoidHom.coe_comp, Function.comp_apply, map_inv, Units.coeHom_apply]
          exact noab_inv_det_one (r x) hx1
        refine ⟨?_, ?_⟩
        · have h := Matrix.det_mul (R x⁻¹) (R x)
          rw [← map_mul, inv_mul_cancel, map_one, Matrix.det_one, hx1, mul_one] at h
          exact h.symm
        · set Z := R x - 1 with hZ
          have hRx : R x = 1 + Z := by rw [hZ, add_sub_cancel]
          have htr : Z.trace = - Z.det := noab_trace_eq Z (by rw [← hRx]; exact hx1)
          have e : R x⁻¹ - 1 = Z.trace • (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) - Z := by
            rw [hinv, hRx, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]; module
          rw [e]
          refine (sm_scalar ?_ hρ0.le).sub hx2
          rw [htr, norm_neg]
          exact (hx2.det hρ0.le).trans (by rw [sq]; exact hρρ) }
  have hRc : Continuous R := Units.continuous_val.comp hr
  have hdeq : ∀ x, (R x).det = 1 ↔ (R x).det ≠ -1 := fun x => by
    constructor
    · intro h; rw [h]; norm_num
    · intro h
      have h2 := hdet x
      rw [sq] at h2
      exact (mul_self_eq_one_iff.1 h2).resolve_right h
  have hU : IsOpen (U : Set Γ) := by
    have hset : (U : Set Γ) = {x | (R x).det ≠ -1} ∩
        ⋂ i, ⋂ j, (fun x => (R x - 1) i j) ⁻¹' Metric.closedBall 0 ρ := by
      ext x
      rw [show x ∈ (U : Set Γ) ↔ ((R x).det = 1 ∧ Sm ρ (R x - 1)) from Iff.rfl, hdeq x]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        Set.mem_setOf_eq]
      rfl
    rw [hset]
    refine (isOpen_ne_fun (hRc.matrix_det) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    exact (IsUltrametricDist.isOpen_closedBall 0 hρ0.ne').preimage ((hRc.sub continuous_const).matrix_elem i j)
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  obtain ⟨k, hk0, -, hk⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := U)) g
  exact ⟨k, hk0, hk.1, hk.2⟩

theorem hom_padicInt_trivial : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]),
    Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) →
    (∀ g, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det ^ 2 = 1) → IsIrr r → Continuous lam → r.ker ≤ lam.ker →
    lam = 1 := by
  intro l _ c Γ _ _ _ _ r lam hr hint hdet hirr hlam hker
  set R : Γ →* Matrix (Fin 2) (Fin 2) (Qbar l) := (Units.coeHom _).comp r with hRdef
  have hRint : ∀ x, Sm 1 (R x) := fun x i j => commHt_norm_le_one_of_mem c _ (hint x i j)
  set ρ : ℝ := ‖((l : ℕ) : Qbar l)‖ with hρ
  have hρeq : ρ = (l : ℝ)⁻¹ := by
    rw [hρ, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ0 : 0 < ρ := by rw [hρeq]; positivity
  have hρ1 : ρ < 1 := by rw [hρeq]; exact inv_lt_one_of_one_lt₀ hl1
  have hρZ : ‖((l : ℕ) : ℤ_[l])‖ = ρ := by rw [PadicInt.norm_p, hρeq]
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, lam g ≠ 1 := by
    by_contra h; push_neg at h; exact hne (MonoidHom.ext fun x => by simpa using h x)
  obtain ⟨k, hk0, hkdet, hksm⟩ := noab_congr_pow l c Γ r hr hint hdet g
  set h0 := g ^ k with hh0
  set v0 : ℤ_[l] := Multiplicative.toAdd (lam h0) with hv0def
  have hv0 : v0 ≠ 0 := by
    have hg' : Multiplicative.toAdd (lam g) ≠ 0 := fun h => hg (by simpa using congrArg Multiplicative.ofAdd h)
    rw [hv0def, hh0, map_pow, toAdd_pow, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hk0.ne') hg'
  have hpow : ∀ n : ℕ, (R (h0 ^ l ^ n)).det = 1 ∧ Sm (ρ ^ (n + 1)) (R (h0 ^ l ^ n) - 1) := by
    intro n
    induction n with
    | zero => simpa using ⟨hkdet, hksm⟩
    | succ n ih =>
      have he : R (h0 ^ l ^ (n + 1)) = R (h0 ^ l ^ n) ^ l := by rw [pow_succ, pow_mul, map_pow]
      refine ⟨by rw [he, Matrix.det_pow, ih.1, one_pow], ?_⟩
      have h1 := noab_pow l (ρ ^ (n + 1)) (R (h0 ^ l ^ n) - 1) (by positivity) (pow_le_one₀ hρ0.le hρ1.le) ih.2 l
      rw [add_sub_cancel] at h1
      have h2 := ih.2.smul ((l : ℕ) : Qbar l)
      have e : R (h0 ^ l ^ (n + 1)) - 1 =
          (R (h0 ^ l ^ n) ^ l - 1 - ((l : ℕ) : Qbar l) • (R (h0 ^ l ^ n) - 1)) + ((l : ℕ) : Qbar l) • (R (h0 ^ l ^ n) - 1) := by
        rw [he]; abel
      rw [e]
      refine (h1.mono ?_).add (h2.mono ?_)
      · rw [← pow_mul]; exact pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
      · rw [← hρ, pow_succ' ρ (n + 1)]
  obtain ⟨N, γ, a, haug⟩ := GlobalTheory.T.exists_augmentation_combination_eq_id_traceless_irreducible l c Γ r hint hirr
  obtain ⟨s, hs⟩ := noab_denom l N a
  set b : Fin N → ℤ_[l] := fun i => ⟨((l : ℕ) : ℚ_[l]) ^ s * a i, hs i⟩ with hbdef
  obtain ⟨C, hC⟩ := GlobalTheory.T.galoisHom_zl_lipschitz_of_ker_le_linearGroup l c Γ r lam hr hint hlam hker
  have key : ∀ n : ℕ, ρ ^ (s + n) * ‖v0‖ ≤ C * ρ ^ (2 * n + 1) := by
    intro n

    set h := h0 ^ l ^ n with hhdef
    set Z := R h - 1 with hZdef
    set Z' := R h⁻¹ - 1 with hZ'def
    set ε : ℝ := ρ ^ (n + 1) with hεdef
    set τ : ℝ := ρ ^ (2 * n + 1) with hτdef
    obtain ⟨hdet1, hZ⟩ := hpow n
    have hε0 : 0 ≤ ε := by positivity
    have hε1 : ε ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    have hτ0 : 0 ≤ τ := by positivity
    have hεε : ε ^ 2 ≤ τ := by rw [← pow_mul]; exact pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
    have hτε : τ ≤ ε := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
    have hε2ε : ε ^ 2 ≤ ε := hεε.trans hτε
    have hRh : R h = 1 + Z := by rw [hZdef, add_sub_cancel]
    have hRh' : R h⁻¹ = 1 + Z' := by rw [hZ'def, add_sub_cancel]
    have htr : Z.trace = - Z.det := noab_trace_eq Z (by rw [← hRh]; exact hdet1)
    have htrn : ‖Z.trace‖ ≤ ε ^ 2 := by rw [htr, norm_neg]; exact hZ.det hε0
    have hZ'Z : Z' + Z = Z.trace • (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      have hinv : R h⁻¹ = (R h).trace • 1 - R h := by
        simp only [hRdef, MonoidHom.coe_comp, Function.comp_apply, map_inv, Units.coeHom_apply]
        exact noab_inv_det_one (r h) hdet1
      rw [hZ'def, hinv, hRh, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
      module
    have hZ'Zs : Sm (ε ^ 2) (Z' + Z) := by rw [hZ'Z]; exact sm_scalar htrn (by positivity)
    have hZ' : Sm ε Z' := by
      have := (hZ'Zs.mono hε2ε).sub hZ
      rwa [add_sub_cancel_right] at this
    set β : Fin N → ℕ := fun i => (b i).appr (2 * n + 1) with hβdef
    set A : Fin N → Matrix (Fin 2) (Fin 2) (Qbar l) := fun i => R (γ i) with hAdef
    set A' : Fin N → Matrix (Fin 2) (Fin 2) (Qbar l) := fun i => R (γ i)⁻¹ with hA'def
    have hAA' : ∀ i, A i * A' i = 1 := fun i => by simp only [hAdef, hA'def, ← map_mul, mul_inv_cancel, map_one]
    set D : Fin N → Matrix (Fin 2) (Fin 2) (Qbar l) := fun i => A i * Z * A' i - Z with hDdef
    set F : Fin N → Matrix (Fin 2) (Fin 2) (Qbar l) := fun i => A i * (1 + Z) ^ β i * A' i * (1 + Z') ^ β i with hFdef
    have hE3 : ∀ i, Sm (ε ^ 2) (F i - 1 - (β i : Qbar l) • D i) := fun i =>
      noab_comm l ε (A i) (A' i) Z Z' (β i) hε0 hε1 (hAA' i) (hRint _) (hRint _) hZ hZ'Zs
    have hD : ∀ i, Sm ε (D i) := fun i => by
      have h1 := ((hRint (γ i)).mul hZ zero_le_one).mul (hRint (γ i)⁻¹) (by positivity)
      rw [one_mul, mul_one] at h1
      exact h1.sub hZ
    have hF : ∀ i, Sm ε (F i - 1) := fun i => by
      have := ((hE3 i).mono hε2ε).add ((hD i).smul_le hε0 (norm_natCast_le_one (β i)))
      rwa [sub_add_cancel] at this
    set P : Γ := (h⁻¹) ^ (l ^ s) * (List.ofFn fun i => γ i * h ^ β i * (γ i)⁻¹ * (h⁻¹) ^ β i).prod with hPdef
    have hRP : R P = (1 + Z') ^ (l ^ s) * (List.ofFn F).prod := by
      rw [hPdef, map_mul, map_pow, map_list_prod, List.map_ofFn, hRh']
      refine congrArg (fun L => _ * List.prod L) (congrArg List.ofFn (funext fun i => ?_))
      simp only [Function.comp_apply, map_mul, map_pow, hFdef, hAdef, hA'def, hRh, hRh']
    have hlamP : ‖Multiplicative.toAdd (lam P)‖ = ρ ^ (s + n) * ‖v0‖ := by
      have hfac : ∀ i, lam (γ i * h ^ β i * (γ i)⁻¹ * (h⁻¹) ^ β i) = 1 := fun i => by
        simp only [map_mul, map_pow, map_inv]
        rw [mul_comm (lam (γ i)) _, mul_assoc, mul_assoc, mul_inv_cancel_left, inv_pow, mul_inv_cancel]
      have hprod : lam (List.ofFn fun i => γ i * h ^ β i * (γ i)⁻¹ * (h⁻¹) ^ β i).prod = 1 := by
        rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
        exact Finset.prod_eq_one fun i _ => hfac i
      have e : Multiplicative.toAdd (lam P) = -(((l ^ s : ℕ) : ℤ_[l]) * (((l ^ n : ℕ) : ℤ_[l]) * v0)) := by
        rw [hPdef, map_mul lam, hprod, mul_one, map_pow lam, map_inv lam, hhdef, map_pow lam]
        simp only [toAdd_pow, toAdd_inv, nsmul_eq_mul, hv0def]
        ring
      rw [e, norm_neg, norm_mul, norm_mul, Nat.cast_pow, Nat.cast_pow, norm_pow, norm_pow, hρZ, pow_add]
      ring
    have hsm : Sm τ (R P - 1) := by
      set ls : Qbar l := ((l ^ s : ℕ) : Qbar l) with hlsdef
      have hls : ‖ls‖ ≤ 1 := norm_natCast_le_one _
      set t := Z.trace with htdef
      set aQ : Fin N → Qbar l := fun i => algebraMap ℚ_[l] (Qbar l) (a i) with haQ
      set bQ : Fin N → Qbar l := fun i => ls * aQ i with hbQ
      set Q1 := (1 + Z') ^ (l ^ s) with hQ1
      set Q2 := (List.ofFn F).prod with hQ2
      have hE1 : Sm (ε ^ 2) (Q1 - 1 - ls • Z') := noab_pow l ε Z' hε0 hε1 hZ' (l ^ s)
      have hE2 : Sm (ε ^ 2) (Q2 - 1 - ∑ i, (F i - 1)) := by
        have := noab_prod l ε (List.ofFn F) hε0 hε1 (fun M hM => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hM; exact hF i)
        convert this using 2
        rw [List.map_ofFn, List.sum_ofFn]; rfl
      have hβb : ∀ i, ‖(β i : Qbar l) - bQ i‖ ≤ τ := fun i => by
        have hsp := PadicInt.appr_spec (2 * n + 1) (b i)
        rw [← PadicInt.norm_le_pow_iff_mem_span_pow] at hsp
        have e : (β i : Qbar l) - bQ i = - algebraMap ℚ_[l] (Qbar l) ((b i - (β i : ℤ_[l]) : ℤ_[l]) : ℚ_[l]) := by
          rw [PadicInt.coe_sub, PadicInt.coe_natCast, map_sub, map_natCast]
          simp only [hβdef, hbQ, haQ, hlsdef, hbdef, map_mul, map_pow, map_natCast, Nat.cast_pow]
          ring
        rw [e, norm_neg, norm_algebraMap', ← PadicInt.norm_def]
        refine hsp.trans (le_of_eq ?_)
        rw [hτdef, hρeq, zpow_neg, zpow_natCast, inv_pow]
      set X := Z - (t / 2) • (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) with hXdef
      have hXtr : X.trace = 0 := by
        rw [hXdef, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, ← htdef]
        simp only [smul_eq_mul, Nat.cast_ofNat]
        ring
      have hsumD : ∑ i, aQ i • D i = X := by
        conv_rhs => rw [haug X hXtr]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [haQ, algebraMap_smul]
        congr 1
        have hA'i : (((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = A' i := by
          simp [hA'def, hRdef, map_inv]
        have hAi : ((r (γ i) : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = A i := rfl
        rw [hA'i, hAi, hDdef, hXdef]
        simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hAA' i]
        abel
      have hsumB : ∑ i, bQ i • D i = ls • X := by
        rw [← hsumD, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hbQ]; exact mul_smul _ _ _
      have hiden : R P - 1 = (Q1 - 1 - ls • Z') + (Q2 - 1 - ∑ i, (F i - 1)) + ∑ i, (F i - 1 - (β i : Qbar l) • D i)
          + ∑ i, ((β i : Qbar l) - bQ i) • D i + (Q1 - 1) * (Q2 - 1)
          + (ls * (t / 2)) • (1 : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
        have e1 : ∑ i, (F i - 1 - (β i : Qbar l) • D i) = ∑ i, (F i - 1) - ∑ i, (β i : Qbar l) • D i :=
          Finset.sum_sub_distrib _ _
        have e2 : ∑ i, ((β i : Qbar l) - bQ i) • D i = ∑ i, (β i : Qbar l) • D i - ls • X := by
          rw [← hsumB, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => sub_smul _ _ _
        have e3 : Z' = t • 1 - Z := eq_sub_of_add_eq hZ'Z
        rw [e1, e2, hRP, e3, hXdef]
        simp only [sub_mul, mul_sub, one_mul, mul_one]
        module
      have hQ1s : Sm ε (Q1 - 1) := by
        have := (hE1.mono hε2ε).add (hZ'.smul_le hε0 hls); rwa [sub_add_cancel] at this
      have hSF : Sm ε (∑ i, (F i - 1)) := Sm.sum _ hε0 _ fun i _ => hF i
      have hQ2s : Sm ε (Q2 - 1) := by
        have := (hE2.mono hε2ε).add hSF; rwa [sub_add_cancel] at this
      have hlast : Sm τ ((ls * (t / 2)) • (1 : Matrix (Fin 2) (Fin 2) (Qbar l))) := by
        refine sm_scalar ?_ hτ0
        rw [norm_mul, norm_div]
        have h2n := noab_norm_two l
        calc ‖ls‖ * (‖t‖ / ‖(2 : Qbar l)‖) ≤ 1 * (ε ^ 2 / ρ) :=
              mul_le_mul hls (div_le_div₀ (by positivity) htrn hρ0 h2n) (by positivity) zero_le_one
          _ = τ := by
            rw [one_mul, hεdef, hτdef, ← pow_mul, div_eq_iff hρ0.ne', ← pow_succ]; congr 1; ring
      rw [hiden]
      refine (((((hE1.mono hεε).add (hE2.mono hεε)).add (Sm.sum _ hτ0 _ fun i _ => (hE3 i).mono hεε)).add
        (Sm.sum _ hτ0 _ fun i _ => ?_)).add ((hQ1s.mul hQ2s hε0).mono ?_)).add hlast
      · exact ((hD i).smul _).mono ((mul_le_mul (hβb i) hε1 hε0 hτ0).trans (le_of_eq (mul_one τ)))
      · rw [← sq]; exact hεε
    have := hC (2 * n + 1) P (fun i j => by rw [norm_pow]; exact hsm i j)
    rw [hlamP, norm_pow] at this
    exact this

  have hbound : ∀ m : ℕ, ‖v0‖ ≤ C * ρ ^ (m + 1) := by
    intro m
    have h := key (s + m)
    have e : ρ ^ (2 * (s + m) + 1) = ρ ^ (s + (s + m)) * ρ ^ (m + 1) := by rw [← pow_add]; congr 1; omega
    rw [e, mul_left_comm] at h
    exact le_of_mul_le_mul_left h (by positivity)
  have ht : Filter.Tendsto (fun m : ℕ => C * ρ ^ (m + 1)) Filter.atTop (nhds (C * 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp (Filter.tendsto_add_atTop_nat 1)).const_mul C
  have h0' : ‖v0‖ ≤ C * 0 := ge_of_tendsto' ht hbound
  rw [mul_zero] at h0'
  exact hv0 (norm_le_zero_iff.1 h0')

end GlobalTheory.Ord2

end
