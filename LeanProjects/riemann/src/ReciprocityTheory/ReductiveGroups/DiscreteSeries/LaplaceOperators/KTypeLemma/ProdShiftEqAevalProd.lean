import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PartialSumRootNonneg

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Gen

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
  {V : Submodule ℂ M}

theorem generatedSubmodule_stable (a b : Fin n) {v : M} (hv : v ∈ genSub E V) : E a b v ∈ genSub E V := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem le_generatedSubmodule : V ≤ genSub E V := le_sInf fun _ hT => hT.1

theorem eulerAction_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem tensorAction_mem_generated {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) (a b : Fin n) :
    ∀ c, tensV E a b f c ∈ genSub E V := by
  intro c
  rw [entry_bounds_of_partialSum]
  refine Submodule.add_mem _ (generatedSubmodule_stable a b (hf c)) ?_
  split_ifs
  · exact hf b
  · exact Submodule.zero_mem _

theorem eulerAction_mem_generated {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) : ∀ d, eeV E f d ∈ genSub E V := by
  intro d
  rw [eulerAction_apply]
  exact Submodule.sum_mem _ fun c _ => generatedSubmodule_stable c d (hf c)

theorem tensorAction_comm_euler (hE : IsGlRep E) (a b : Fin n) (f : Fin n → M) :
    tensV E a b (eeV E f) = eeV E (tensV E a b f) := by
  have key : ∀ c d, E a b (E d c (f d)) = E d c (E a b (f d)) +
      ((if b = d then E a c (f d) else 0) - (if c = a then E d b (f d) else 0)) := by
    intro c d
    have h := LinearMap.congr_fun (hE a b d c) (f d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply,
      apply_ite (fun T : Module.End ℂ M => T (f d)), LinearMap.zero_apply] at h
    rw [← h]; abel
  funext c
  rw [entry_bounds_of_partialSum, eulerAction_apply, eulerAction_apply, eulerAction_apply, map_sum]
  simp only [entry_bounds_of_partialSum, map_add, key, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ d, (if b = d then E a c (f d) else 0) = E a c (f b) := by simp
  have e2 : ∑ d, E d c (if d = a then f b else 0) = E a c (f b) := by simp [apply_ite]
  rw [e1, e2]
  by_cases hca : c = a
  · subst hca; simp; abel
  · simp [hca]

theorem finiteDimensional_pi_submodule (hV : FiniteDimensional ℂ V) :
    FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : Fin n => V) := by
  let F : (Fin n → V) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun i => V.subtype ∘ₗ LinearMap.proj i
  have : Submodule.pi Set.univ (fun _ : Fin n => V) ≤ LinearMap.range F := by
    intro f hf
    exact ⟨fun i => ⟨f i, hf i (Set.mem_univ i)⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le this

end Gen

section Poly

variable {X' : Type*} [AddCommGroup X'] [Module ℂ X']

theorem aeval_induction (A : Module.End ℂ X') (P : Module.End ℂ X' → Prop) (h1 : ∀ a : ℂ, P (a • 1))
    (hadd : ∀ S T, P S → P T → P (S + T)) (hmul : ∀ S, P S → P (S * A)) (p : ℂ[X]) :
    P (aeval A p) := by
  induction p using Polynomial.induction_on with
  | C a => rw [aeval_C, Algebra.algebraMap_eq_smul_one]; exact h1 a
  | add p q hp hq => rw [map_add]; exact hadd _ _ hp hq
  | monomial k a h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact hmul _ h

theorem aeval_mul_commute {A B : Module.End ℂ X'} (h : A * B = B * A) (p : ℂ[X]) :
    aeval A p * B = B * aeval A p := by
  refine aeval_induction A (fun S => S * B = B * S) ?_ ?_ ?_ p
  · intro a; rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  · intro S T hS hT; rw [add_mul, mul_add, hS, hT]
  · intro S hS; rw [mul_assoc, h, ← mul_assoc, hS, mul_assoc]

theorem aeval_mem_of_stable_alt {A : Module.End ℂ X'} {G : Submodule ℂ X'} (hG : ∀ x ∈ G, A x ∈ G) (p : ℂ[X]) :
    ∀ x ∈ G, aeval A p x ∈ G := by
  refine aeval_induction A (fun S => ∀ x ∈ G, S x ∈ G) ?_ ?_ ?_ p
  · intro a x hx; exact G.smul_mem a hx
  · intro S T hS hT x hx; exact G.add_mem (hS x hx) (hT x hx)
  · intro S hS x hx; exact hS _ (hG x hx)

theorem prodShift_eq_aeval_prod (A : Module.End ℂ X') (θ : Fin n → ℝ) :
    prodShift A θ = aeval A (∏ t, (X - C ((θ t : ℝ) : ℂ))) := by
  rw [prodShift, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun t => ?_)
  simp [Algebra.algebraMap_eq_smul_one]

end Poly

section Xs

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
  {V : Submodule ℂ M}

def k3bP (θ : Fin n → ℝ) (s : Fin n) : ℂ[X] := ∏ t ∈ univ.erase s, (X - C ((θ t : ℝ) : ℂ))

theorem mem_eigenTensorSpace_gen_iff {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs (eeV E) (genSub E V) θ ↔ (∀ c, f c ∈ genSub E V) ∧ eeV E f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_pi, sub_eq_zero]

theorem lagrange_mem_generated (p : ℂ[X]) {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) :
    ∀ c, aeval (eeV E) p f c ∈ genSub E V := by
  have := aeval_mem_of_stable_alt (A := eeV E) (G := Submodule.pi Set.univ fun _ => genSub E V)
    (fun x hx => fun c _ => eulerAction_mem_generated (fun c => hx c (Set.mem_univ c)) c) p f (fun c _ => hf c)
  exact fun c => this c (Set.mem_univ c)

theorem lagrange_mem_eigenTensorSpace {θ : Fin n → ℝ}
    (hK1 : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → prodShift (eeV E) θ f = 0) (s : Fin n)
    {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) :
    aeval (eeV E) (k3bP θ s) f ∈ Xs (eeV E) (genSub E V) (θ s) := by
  rw [mem_eigenTensorSpace_gen_iff]
  refine ⟨lagrange_mem_generated _ hf, ?_⟩
  have h := hK1 f hf
  rw [prodShift_eq_aeval_prod, ← Finset.mul_prod_erase univ (fun t => X - C ((θ t : ℝ) : ℂ)) (mem_univ s),
    map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact h

theorem lagrange_on_eigenTensorSpace (θ : Fin n → ℝ) (s : Fin n) {x : Fin n → M}
    (hx : x ∈ Xs (eeV E) (genSub E V) (θ s)) :
    aeval (eeV E) (k3bP θ s) x = (k3bP θ s).eval ((θ s : ℝ) : ℂ) • x :=
  Module.End.aeval_apply_of_mem_apply_eq_smul (mem_eigenTensorSpace_gen_iff.1 hx).2

theorem lagrangeFactor_eval_ne_zero_of_injective {θ : Fin n → ℝ} (hθ : Function.Injective θ) (s : Fin n) :
    (k3bP θ s).eval ((θ s : ℝ) : ℂ) ≠ 0 := by
  rw [k3bP, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro t ht
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h
  exact (Finset.ne_of_mem_erase ht) (hθ (Complex.ofReal_injective h)).symm

theorem aeval_tensorAction_comm (hE : IsGlRep E) (p : ℂ[X]) (a b : Fin n) (f : Fin n → M) :
    aeval (eeV E) p (tensV E a b f) = tensV E a b (aeval (eeV E) p f) := by
  have h : eeV E * tensV E a b = tensV E a b * eeV E := by
    refine LinearMap.ext fun g => ?_
    exact (tensorAction_comm_euler hE a b g).symm
  exact LinearMap.congr_fun (aeval_mul_commute h p) f

theorem eigenTensorSpace_stable (hE : IsGlRep E) (a b : Fin n) {θ : ℝ} {f : Fin n → M}
    (hf : f ∈ Xs (eeV E) (genSub E V) θ) : tensV E a b f ∈ Xs (eeV E) (genSub E V) θ := by
  rw [mem_eigenTensorSpace_gen_iff] at hf ⊢
  refine ⟨tensorAction_mem_generated hf.1 a b, ?_⟩
  rw [← tensorAction_comm_euler hE, hf.2, map_smul]

theorem generated_eigenspace_annihilate {N : Type*} [AddCommGroup N] [Module ℂ N] (EN : Fin n → Fin n → Module.End ℂ N)
    (φ : (Fin n → M) →ₗ[ℂ] N)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensV E a b f) = EN a b (φ f))
    (T : Module.End ℂ (Fin n → M)) (hT : ∀ a b f, T (tensV E a b f) = tensV E a b (T f))
    (hTG : ∀ f : Fin n → M, (∀ c, f c ∈ genSub E V) → ∀ c, T f c ∈ genSub E V)
    (hz : ∀ u : Fin n → M, (∀ c, u c ∈ V) → φ (T u) = 0) {f : Fin n → M}
    (hf : f ∈ genSub (tensV E) (Submodule.pi Set.univ fun _ => V)) : φ (T f) = 0 := by
  let Z : Submodule ℂ (Fin n → M) :=
    Submodule.pi Set.univ (fun _ => genSub E V) ⊓ LinearMap.ker (φ ∘ₗ T)
  have hZ : ∀ g, g ∈ Z ↔ (∀ c, g c ∈ genSub E V) ∧ φ (T g) = 0 := fun g => by
    simp [Z, Submodule.mem_pi]
  have hle : genSub (tensV E) (Submodule.pi Set.univ fun _ => V) ≤ Z := by
    refine sInf_le ⟨fun u hu => (hZ u).2 ⟨fun c => le_generatedSubmodule (hu c (Set.mem_univ c)),
      hz u fun c => hu c (Set.mem_univ c)⟩, ?_⟩
    intro a b g hg
    rw [hZ] at hg ⊢
    refine ⟨tensorAction_mem_generated hg.1 a b, ?_⟩
    rw [hT, hφ a b _ (hTG g hg.1), hg.2, map_zero]
  exact ((hZ f).1 (hle hf)).2

theorem casimir_map_intertwiner {N : Type*} [AddCommGroup N] [Module ℂ N]
    (EN : Fin n → Fin n → Module.End ℂ N) (φ : (Fin n → M) →ₗ[ℂ] N)
    (hφ : ∀ (a b : Fin n) (f : Fin n → M), (∀ c, f c ∈ genSub E V) → φ (tensV E a b f) = EN a b (φ f))
    {f : Fin n → M} (hf : ∀ c, f c ∈ genSub E V) : casimir EN (φ f) = φ (casimir (tensV E) f) := by
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hφ a b _ (tensorAction_mem_generated hf b a), hφ b a _ hf]

end Xs

theorem casimirValue_add_single (lam : Fin n → ℝ) (s : Fin n) :
    casVal (lam + Pi.single s 1) = casVal lam + n + 2 * thV lam s := by
  simp only [casVal, nsq, dot, thV, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

theorem lowestKType_add_single (ε : Fin n → Bool) (lam : Fin n → ℝ) (s : Fin n) :
    lowK ε (lam + Pi.single s 1) = lowK ε lam + Pi.single s 1 := by
  unfold lowK; abel

theorem lowestKType_shift_inv (ε : Fin n → Bool) (ν : Fin n → ℝ) : lowK ε (ν + rhoC ε - rhoN ε) = ν := by
  unfold lowK; abel

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
