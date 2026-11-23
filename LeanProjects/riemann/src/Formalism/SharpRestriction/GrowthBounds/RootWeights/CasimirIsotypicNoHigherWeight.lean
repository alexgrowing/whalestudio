import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicComponentLeLowerWeights
import Formalism.SharpRestriction.GrowthBounds.RootWeights.CrAevalStable

noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_quot (E : GLOps n K V) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z) : GLOps n K (V ⧸ Z) :=
  fun a b => Z.mapQ Z (E a b) (fun x hx => hZ a b x hx)

theorem cr_quot_mk (E : GLOps n K V) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z) (a b : Fin n) (x : V) :
    cr_quot E Z hZ a b (Z.mkQ x) = Z.mkQ (E a b x) := rfl

theorem cr_quot_rel (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z) :
    SatisfiesGLRelations (cr_quot E Z hZ) := by
  intro a b c d
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective Z y
  have h := congrArg (fun f : Module.End K V => Z.mkQ (f x)) (hR a b c d)
  split_ifs at h ⊢ <;> simpa [cr_quot] using h

theorem cr_quot_wt (E : GLOps n K V) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) : Z.mkQ x ∈ weightSp (cr_quot E Z hZ) ν := by
  rw [weightSp, Submodule.mem_iInf] at hx ⊢
  intro a
  have h := LinearMap.mem_ker.mp (hx a)
  rw [LinearMap.mem_ker]
  have e : (cr_quot E Z hZ a a - (ν a : K) • (1 : Module.End K (V ⧸ Z))) (Z.mkQ x)
      = Z.mkQ ((E a a - (ν a : K) • (1 : Module.End K V)) x) := by
    simp [cr_quot]
  rw [e, h, map_zero]

theorem cr_quot_top (E : GLOps n K V) (Z : Submodule K V) (hZ : IsStableUnderOperators E Z)
    (hT : (⨆ ν, weightSp E ν) = ⊤) : (⊤ : Submodule K (V ⧸ Z)) ≤ ⨆ ν, weightSp (cr_quot E Z hZ) ν := by
  intro y _
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective Z y
  have hx : x ∈ ⨆ ν, weightSp E ν := by rw [hT]; exact Submodule.mem_top
  have h1 : Z.mkQ x ∈ Submodule.map Z.mkQ (⨆ ν, weightSp E ν) := Submodule.mem_map_of_mem hx
  rw [Submodule.map_iSup] at h1
  have hle : (⨆ ν, Submodule.map Z.mkQ (weightSp E ν)) ≤ ⨆ ν, weightSp (cr_quot E Z hZ) ν := by
    refine iSup_mono fun ν => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact cr_quot_wt E Z hZ ν w hw
  exact hle h1

private lemma casimir_commute_E (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) :
    cr_C E * E c d = E c d * cr_C E := by
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a)
      = E a b * ((if a = c then E b d else 0) - if d = b then E c a else 0)
        + ((if b = c then E a d else 0) - if d = a then E c b else 0) * E b a := by
    intro a b
    rw [← hR b a c d, ← hR a b c d]
    noncomm_ring
  have S1 : ∑ a, ∑ b, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  have S2 : ∑ a, ∑ b, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  have S3 : ∑ a, ∑ b, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  have S4 : ∑ a, ∑ b, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single d]
    · simp
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  have hexp : cr_C E * E c d - E c d * cr_C E
      = ∑ a, ∑ b, (E a b * E b a * E c d - E c d * (E a b * E b a)) := by
    simp only [cr_C, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← sub_eq_zero, hexp]
  simp only [key, mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4]
  abel

private lemma casimir_apply_eq_smul_of_isHWV (E : GLOps n K V) (hR : SatisfiesGLRelations E) (ν : Fin n → ℤ) (v : V) (hv : IsHWV E ν v) :
    cr_C E v = (cr_c ν : K) • v := by
  have hw : ∀ a, E a a v = (ν a : K) • v := by
    intro a
    have h0 := hv.2.1
    rw [weightSp, Submodule.mem_iInf] at h0
    have h := LinearMap.mem_ker.mp (h0 a)
    simpa [sub_eq_zero] using h
  have hterm : ∀ a b, E a b (E b a v)
      = (if a = b then (ν a : K) ^ 2 else if a < b then (ν a : K) - ν b else 0) • v := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · have hc := congrArg (fun f : Module.End K V => f v) (hR a b b a)
      rw [if_neg h.ne, if_pos h, sub_smul]
      simpa [hv.2.2 a b h, hw] using hc
    · simp [hw, sq, mul_smul]
    · rw [if_neg (ne_of_gt h), if_neg (not_lt.mpr h.le), hv.2.2 b a h, map_zero, zero_smul]
  have hs : (∑ a, ∑ b, (if a = b then (ν a : K) ^ 2 else if a < b then (ν a : K) - ν b else 0))
      = (cr_c ν : K) := by
    have split : ∀ a b, (if a = b then (ν a : K) ^ 2 else if a < b then (ν a : K) - ν b else 0)
        = (if a = b then (ν a : K) ^ 2 else 0) + (if a < b then (ν a : K) - ν b else 0) := by
      intro a b
      by_cases h : a = b
      · subst h
        simp
      · simp [h]
    simp only [cr_c, cr_h]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_congr rfl fun b _ => split a b, Finset.sum_add_distrib]
    simp
  rw [← hs, Finset.sum_smul]
  unfold cr_C
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← hterm]
  rfl

private lemma casimir_commute_of_mem_Umon (E : GLOps n K V) (hR : SatisfiesGLRelations E) (u : Module.End K V) (hu : u ∈ Umon E) :
    cr_C E * u = u * cr_C E := by
  have h : Umon E ≤ Submonoid.centralizer {cr_C E} := by
    unfold Umon
    rw [Submonoid.closure_le]
    rintro _ ⟨⟨c, d⟩, rfl⟩
    rw [SetLike.mem_coe, Submonoid.mem_centralizer_iff]
    rintro g rfl
    exact casimir_commute_E E hR c d
  exact Submonoid.mem_centralizer_iff.mp (h hu) _ rfl

private lemma aeval_apply_eq_eval_smul_of_eigenvector (f : Module.End K V) (c : K) (t : V) (ht : f t = c • t) (p : K[X]) :
    aeval f p t = p.eval c • t := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a
    simp
  · intro p q hp hq
    simp only [map_add, LinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  · intro k a h
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval_mul, Polynomial.eval_X]
    change (aeval f (Polynomial.C a * X ^ k)) (f t) = _
    rw [ht, map_smul, h, smul_smul, mul_comm]

private lemma casimir_apply_eq_smul_of_mem_isotypicPartIn (E : GLOps n K V) (hR : SatisfiesGLRelations E) (W : Submodule K V) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ isotypicPartIn E W ν) : cr_C E x = (cr_c ν : K) • x := by
  have hle : isotypicPartIn E W ν ≤ LinearMap.ker (cr_C E - (cr_c ν : K) • (1 : Module.End K V)) := by
    unfold isotypicPartIn
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, v, _, hH, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have h1 : cr_C E (u v) = u (cr_C E v) := by
      change (cr_C E * u) v = (u * cr_C E) v
      rw [casimir_commute_of_mem_Umon E hR u hu]
    simp [h1, casimir_apply_eq_smul_of_isHWV E hR ν v hH]
  have h := LinearMap.mem_ker.mp (hle hx)
  simpa [sub_eq_zero] using h

private lemma casimir_apply_eq_smul_of_mem_iSup_isotypic (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : (Fin n → ℤ) → Submodule K V) (c0 : ℤ) (z : V)
    (hz : z ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν) : cr_C E z = (c0 : K) • z := by
  have hle : (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν)
      ≤ LinearMap.ker (cr_C E - (c0 : K) • (1 : Module.End K V)) := by
    refine iSup₂_le fun ν hν => ?_
    intro x hx
    rw [LinearMap.mem_ker]
    have h := casimir_apply_eq_smul_of_mem_isotypicPartIn E hR (Wx ν) ν x hx
    rw [Set.mem_setOf_eq] at hν
    rw [hν] at h
    simp [h]
  have h := LinearMap.mem_ker.mp (hle hz)
  simpa [sub_eq_zero] using h

theorem casimir_polynomial_isolates_level [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : (Fin n → ℤ) → Submodule K V) (z : V)
    (hz : z ∈ ⨆ ν, isotypicPartIn E (Wx ν) ν) (c0 : ℤ) : ∃ r : K[X], r.eval (c0 : K) = 1 ∧
      aeval (cr_C E) r z ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν := by
  have hK2 : ∀ t ∈ (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν), ∀ p : K[X],
      aeval (cr_C E) p t = p.eval (c0 : K) • t := fun t ht p =>
    aeval_apply_eq_eval_smul_of_eigenvector _ _ t (casimir_apply_eq_smul_of_mem_iSup_isotypic E hR Wx c0 t ht) p
  refine Submodule.iSup_induction (x := z) (fun ν => isotypicPartIn E (Wx ν) ν) hz ?_ ?_ ?_
  · intro ν x hx
    have hxC := casimir_apply_eq_smul_of_mem_isotypicPartIn E hR (Wx ν) ν x hx
    by_cases hc : cr_c ν = c0
    · refine ⟨1, by simp, ?_⟩
      have hm : x ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν :=
        Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem hc hx)
      simpa using hm
    · have hne : (c0 : K) - (cr_c ν : K) ≠ 0 := by
        rw [sub_ne_zero]
        exact fun h => hc (Int.cast_injective h).symm
      refine ⟨Polynomial.C ((c0 : K) - cr_c ν)⁻¹ * (X - Polynomial.C (cr_c ν : K)), ?_, ?_⟩
      · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C]
        exact inv_mul_cancel₀ hne
      · rw [aeval_apply_eq_eval_smul_of_eigenvector _ _ x hxC]
        simp
  · exact ⟨1, by simp, by simp⟩
  · intro x y hx hy
    obtain ⟨r1, e1, m1⟩ := hx
    obtain ⟨r2, e2, m2⟩ := hy
    refine ⟨r1 * r2, by simp [e1, e2], ?_⟩
    rw [LinearMap.map_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, map_mul]
      change aeval (cr_C E) r2 (aeval (cr_C E) r1 x) ∈ _
      rw [hK2 _ m1]
      exact Submodule.smul_mem _ _ m1
    · rw [map_mul]
      change aeval (cr_C E) r1 (aeval (cr_C E) r2 y) ∈ _
      rw [hK2 _ m2]
      exact Submodule.smul_mem _ _ m2

theorem casimir_acts_scalar_on_level (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Wx : (Fin n → ℤ) → Submodule K V) (c0 : ℤ) (z : V)
    (hz : z ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = c0}, isotypicPartIn E (Wx ν) ν) : cr_C E z = (c0 : K) • z := by
  exact casimir_apply_eq_smul_of_mem_iSup_isotypic E hR Wx c0 z hz

theorem cr_Pos_zero_or {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : β = 0 ∨ 0 < weightHeight' β := by
  unfold weightHeight'
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    right
    have e : (∑ i : Fin n, ((i : ℕ) : ℤ) * rootW a b i) = ((a : ℕ) : ℤ) - ((b : ℕ) : ℤ) := by
      simp [rootW, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    rw [e]
    have hab' : (a : ℕ) < (b : ℕ) := hab
    omega
  | zero => left; rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · left
      simp
    · right
      simpa using hy
    · right
      simpa using hx
    · right
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add]
      linarith

theorem casimir_isotypic_no_higher_weight [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (Wx : (Fin n → ℤ) → Submodule K V) (mu : Fin n → ℤ) (hmu : Dominant mu) (ν' : Fin n → ℤ)
    (hν' : ν' - mu ∈ cr_Pos n) (hpos : 0 < weightHeight' (ν' - mu)) (z : V)
    (hz : z ∈ ⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = cr_c mu}, isotypicPartIn E (Wx ν) ν) (hzw : z ∈ weightSp E ν') : z = 0 := by
  by_contra hne
  have hle : (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = cr_c mu}, isotypicPartIn E (Wx ν) ν) ≤
      cr_WS E {τ | ∃ ν, Dominant ν ∧ cr_c ν = cr_c mu ∧ ν - τ ∈ cr_Pos n} := by
    refine iSup₂_le fun ν hν x hx => ?_
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · have hd := cr_isoIn_dom E hR (Wx ν) hx hx0
      have hsub : weightsBelow ν ⊆ {τ | ∃ ν, Dominant ν ∧ cr_c ν = cr_c mu ∧ ν - τ ∈ cr_Pos n} :=
        fun τ hτ => ⟨ν, hd, hν, hτ⟩
      exact cr_WS_mono E hsub (isotypic_component_le_lower_weights E hR (Wx ν) ν hx)
  obtain ⟨ν, hd, hc, hp⟩ := cr_WS_mem E (hle hz) hzw hne
  have e : ν - mu = (ν - ν') + (ν' - mu) := by abel
  have h1 : ν - mu ∈ cr_Pos n := by rw [e]; exact add_mem hp hν'
  have h2 : 0 < weightHeight' (ν - mu) := by
    rw [e, cr_ht_add]
    have := cr_Pos_ht hp
    omega
  have := cr_c_lt hd hmu h1 h2
  omega

end Formalism.MainNotions.G.GLWeightTheory
