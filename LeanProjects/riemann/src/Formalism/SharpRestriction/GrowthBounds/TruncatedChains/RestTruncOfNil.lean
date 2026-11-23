import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {n : ℕ} {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem pf_apply (E : GLOps n K V) (a b : Fin n) (c T : ℕ) (x : V) :
    pf E a b c T x = ∑ k ∈ Finset.range (T + 1),
      ((-1 : K) ^ k / ((Nat.choose (c + k) k : ℕ) : K)) •
        (((k.factorial : K)⁻¹) • ((E b a) ^ k) (((k.factorial : K)⁻¹) • ((E a b) ^ k) x)) := by
  unfold pf
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [divPowE, Module.End.mul_apply]

theorem pow_mem_stable (f : Module.End K W) (S : Submodule K W) (h : ∀ w ∈ S, f w ∈ S) (k : ℕ) (w : W)
    (hw : w ∈ S) : (f ^ k) w ∈ S := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact h _ ih

theorem pf_mem (A : GLOps n K W) (S : Submodule K W) (x y : Fin n) (h1 : ∀ w ∈ S, A x y w ∈ S)
    (h2 : ∀ w ∈ S, A y x w ∈ S) (c T : ℕ) (w : W) (hw : w ∈ S) : pf A x y c T w ∈ S := by
  rw [pf_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (pow_mem_stable _ S h2 k _ (Submodule.smul_mem _ _ (pow_mem_stable _ S h1 k w hw))))

theorem pow_intertw (f : Module.End K W) (g : Module.End K V) (π : W →ₗ[K] V) (S : Submodule K W)
    (hS : ∀ w ∈ S, f w ∈ S) (h : ∀ w ∈ S, π (f w) = g (π w)) (k : ℕ) (w : W) (hw : w ∈ S) :
    π ((f ^ k) w) = (g ^ k) (π w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      h _ (pow_mem_stable f S hS k w hw), ih]

theorem pf_intertw (A : GLOps n K W) (E : GLOps n K V) (π : W →ₗ[K] V) (S : Submodule K W) (x y : Fin n)
    (hS : ∀ w ∈ S, A x y w ∈ S) (h1 : ∀ w ∈ S, π (A x y w) = E x y (π w)) (h2 : ∀ w, π (A y x w) = E y x (π w))
    (c T : ℕ) (w : W) (hw : w ∈ S) : π (pf A x y c T w) = pf E x y c T (π w) := by
  rw [pf_apply, pf_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, pow_intertw (A y x) (E y x) π ⊤ (fun _ _ => Submodule.mem_top)
    (fun w _ => h2 w) k _ Submodule.mem_top, map_smul, pow_intertw (A x y) (E x y) π S hS h1 k w hw]

theorem pf_wt {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (ν : Fin n → ℤ) (a b : Fin n) (c T : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : pf E a b c T x ∈ weightSp E ν := by
  have hpow : ∀ (a' b' : Fin n) (k : ℕ) (μ : Fin n → ℤ) (y : V), y ∈ weightSp E μ →
      (E a' b' ^ k) y ∈ weightSp E (μ + k • rootW a' b') := by
    intro a' b' k
    induction k with
    | zero => intro μ y hy; simpa using hy
    | succ k ih =>
      intro μ y hy
      rw [pow_succ', Module.End.mul_apply]
      have := hs a' b' _ _ (ih μ y hy)
      convert this using 2
      rw [succ_nsmul, add_assoc]
  have hr : rootW a b + rootW b a = 0 := by
    unfold rootW
    abel
  rw [pf_apply]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
  have h1 := hpow b a k _ _ (Submodule.smul_mem _ ((k.factorial : K)⁻¹) (hpow a b k ν x hx))
  have he : ν + k • rootW a b + k • rootW b a = ν := by
    rw [add_assoc, ← smul_add, hr, smul_zero, add_zero]
  rw [he] at h1
  exact h1

theorem pf_sub (E : GLOps n K V) (a b : Fin n) (c T : ℕ) (x : V) :
    pf E a b c T x - x ∈ LinearMap.range (E b a) := by
  rw [pf_apply, Finset.sum_range_succ', add_sub_assoc]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => ?_) ?_
  · refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    rw [pow_succ', Module.End.mul_apply]
    exact LinearMap.mem_range_self _ _
  · simp

end Gen

def RestTrunc : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ a b : Fin n, a ≠ b → ∀ c T T' : ℕ, Module.finrank K V ≤ T →
      Module.finrank K V ≤ T' → pf E a b c T = pf E a b c T'

theorem restTrunc_of_nil (hN : RestNil) : RestTrunc := by
  unfold RestTrunc
  unfold RestNil at hN
  intro K V _ _ _ _ _ n E hE a b hab c T T' hT hT'
  have key : ∀ m, Module.finrank K V ≤ m → pf E a b c m = pf E a b c (Module.finrank K V) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [← ih]
      have h0 : (E a b) ^ (m + 1) = 0 := hN K V n E hE a b hab (m + 1) (by omega)
      unfold pf
      rw [Finset.sum_range_succ _ (m + 1)]
      simp [divPowE, h0]
  rw [key T hT, key T' hT']

section Tens

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def tensOps (E : GLOps n K V) : GLOps n K (Fin n → V) := fun x y =>
  LinearMap.pi fun i => E x y ∘ₗ (LinearMap.proj i : (Fin n → V) →ₗ[K] V) +
    if i = x then (LinearMap.proj y : (Fin n → V) →ₗ[K] V) else 0

theorem tensOps_apply (E : GLOps n K V) (x y : Fin n) (w : Fin n → V) (i : Fin n) :
    tensOps E x y w i = E x y (w i) + if i = x then w y else 0 := by
  by_cases h : i = x <;> simp [tensOps, h]

theorem tens_rel {E : GLOps n K V} (hE : IsGLRep E) (a b c d : Fin n) :
    tensOps E a b * tensOps E c d - tensOps E c d * tensOps E a b =
      (if b = c then tensOps E a d else 0) - (if d = a then tensOps E c b else 0) := by
  refine LinearMap.ext fun w => funext fun i => ?_
  have hc := LinearMap.congr_fun (hE.1 a b c d) (w i)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, tensOps_apply, map_add]
  split_ifs at hc ⊢ <;> subst_vars <;>
    (try simp only [tensOps_apply, LinearMap.zero_apply, Pi.zero_apply, map_zero, add_zero, zero_add,
      sub_zero, LinearMap.sub_apply] at hc ⊢) <;>
    (try split_ifs at hc ⊢) <;> (try subst_vars) <;>
    first
    | abel1
    | (rw [sub_eq_iff_eq_add] at hc; rw [hc]; abel1)
    | skip
  all_goals done

theorem tens_single_wt (E : GLOps n K V) (ν : Fin n → ℤ) (i : Fin n) (x : V) (hx : x ∈ weightSp E ν) :
    (Pi.single i x : Fin n → V) ∈ weightSp (tensOps E) (ν + Pi.single i 1) := by
  unfold weightSp at hx ⊢
  rw [Submodule.mem_iInf] at hx ⊢
  intro a
  have ha := hx a
  rw [LinearMap.mem_ker] at ha ⊢
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at ha ⊢
  funext j
  rw [tensOps_apply]
  by_cases hj : j = i
  · subst hj
    by_cases hja : j = a
    · subst hja
      simp [ha, add_smul]
    · simp [ha, hja, Ne.symm hja]
  · by_cases hja : j = a
    · subst hja
      simp [hj]
    · simp [hj, hja]

theorem tens_isGLRep [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) : IsGLRep (tensOps E) := by
  refine ⟨fun a b c d => tens_rel hE a b c d,
    fun x => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hw : w i ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by
    rw [hE.2.2]
    exact Submodule.mem_top
  have hle : (⨆ mu : Fin n → ℤ, weightSp E mu) ≤
      (⨆ mu : Fin n → ℤ, weightSp (tensOps E) mu).comap (LinearMap.single K (fun _ : Fin n => V) i) :=
    iSup_le fun mu y hy => Submodule.mem_iSup_of_mem (mu + Pi.single i 1) (tens_single_wt E mu i y hy)
  exact hle hw

end Tens

end Formalism.MainNotions.G.ExtremalProjector
