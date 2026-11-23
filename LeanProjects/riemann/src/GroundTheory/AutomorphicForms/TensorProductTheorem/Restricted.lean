import Mathlib
import GroundTheory.AutomorphicForms.SmoothRep

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open PiTensorProduct Filter Function Module Set

open scoped TensorProduct RestrictedProduct

variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

def IsRestricted (ξ x : ∀ v, V v) : Prop :=
  ∀ᶠ v in cofinite, x v = ξ v

theorem isRestricted_iff_finite {ξ x : ∀ v, V v} :
    IsRestricted ξ x ↔ {v | x v ≠ ξ v}.Finite :=
  Filter.eventually_cofinite

theorem isRestricted_self (ξ : ∀ v, V v) : IsRestricted ξ ξ :=
  Eventually.of_forall fun _ => rfl

theorem IsRestricted.update [DecidableEq ι] {ξ x : ∀ v, V v} (h : IsRestricted ξ x) (i : ι)
    (a : V i) : IsRestricted ξ (Function.update x i a) := by
  rw [isRestricted_iff_finite] at h ⊢
  refine (h.union (Set.finite_singleton i)).subset fun v hv => ?_
  by_cases hvi : v = i
  · exact Or.inr hvi
  · left
    simpa [Function.update_of_ne hvi] using hv

theorem isRestricted_update_iff [DecidableEq ι] {ξ x : ∀ v, V v} {i : ι} {a : V i} :
    IsRestricted ξ (Function.update x i a) ↔ IsRestricted ξ x := by
  refine ⟨fun h => ?_, fun h => h.update i a⟩
  have := h.update i (x i)
  rwa [Function.update_idem, Function.update_eq_self] at this

def restrictedTensor (ξ : ∀ v, V v) : Submodule ℂ (⨂[ℂ] v, V v) :=
  Submodule.span ℂ (tprod ℂ '' {x | IsRestricted ξ x})

theorem tprod_mem_restrictedTensor {ξ x : ∀ v, V v} (h : IsRestricted ξ x) :
    tprod ℂ x ∈ restrictedTensor ξ :=
  Submodule.subset_span ⟨x, h, rfl⟩

theorem restrictedTensor_congr {ξ ξ' : ∀ v, V v} (h : ∀ᶠ v in cofinite, ξ v = ξ' v) :
    restrictedTensor ξ = restrictedTensor ξ' := by
  have key : ∀ {ξ ξ' : ∀ v, V v}, (∀ᶠ v in cofinite, ξ v = ξ' v) →
      restrictedTensor ξ ≤ restrictedTensor ξ' := by
    intro ξ ξ' h
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine tprod_mem_restrictedTensor ?_
    filter_upwards [show ∀ᶠ v in cofinite, x v = ξ v from hx, h] with v h1 h2 using h1.trans h2
  exact le_antisymm (key h) (key (h.mono fun v hv => hv.symm))

section Lift

def weight (T : Finset ι) (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) (v : ι) : ℂ := by
  classical
  exact if v ∈ T then 1 else l v (x v)

theorem weight_of_mem {T : Finset ι} (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) {v : ι}
    (hv : v ∈ T) : weight T l x v = 1 := by
  simp [weight, hv]

theorem weight_of_notMem {T : Finset ι} (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) {v : ι}
    (hv : v ∉ T) : weight T l x v = l v (x v) := by
  simp [weight, hv]

theorem mulSupport_weight_subset (ξ : ∀ v, V v) (T : Finset ι) (l : ∀ v, Dual ℂ (V v))
    (x : ∀ v, V v) :
    mulSupport (weight T l x) ⊆ {v | x v ≠ ξ v} ∪ {v | l v (ξ v) ≠ 1} := by
  intro v hv
  rw [mem_mulSupport] at hv
  by_cases hvT : v ∈ T
  · exact absurd (weight_of_mem l x hvT) hv
  · rw [weight_of_notMem l x hvT] at hv
    by_cases hx : x v = ξ v
    · right
      show l v (ξ v) ≠ 1
      rw [← hx]
      exact hv
    · exact Or.inl hx

theorem finite_mulSupport_weight {ξ x : ∀ v, V v} (hx : IsRestricted ξ x) (T : Finset ι)
    {l : ∀ v, Dual ℂ (V v)} (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) :
    (mulSupport (weight T l x)).Finite :=
  ((isRestricted_iff_finite.1 hx).union (Filter.eventually_cofinite.1 hl)).subset
    (mulSupport_weight_subset ξ T l x)

theorem finprod_update_eq_mul [DecidableEq ι] (w : ι → ℂ) (hw : (mulSupport w).Finite) (i : ι) (c : ℂ) :
    ∏ᶠ v, Function.update w i c v = c * ∏ᶠ v, Function.update w i 1 v := by
  classical
  set s : Finset ι := insert i hw.toFinset
  have hs : ∀ c, mulSupport (Function.update w i c) ⊆ (s : Set ι) := by
    intro c v hv
    by_cases hvi : v = i
    · simp [s, hvi]
    · rw [mem_mulSupport, Function.update_of_ne hvi] at hv
      simp [s, hv]
  rw [finprod_eq_prod_of_mulSupport_subset _ (hs c),
    finprod_eq_prod_of_mulSupport_subset _ (hs 1),
    Finset.prod_update_of_mem (Finset.mem_insert_self i _),
    Finset.prod_update_of_mem (Finset.mem_insert_self i _), one_mul]

theorem weight_update_of_mem {T : Finset ι} (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) {i : ι}
    (hi : i ∈ T) (a : V i) {inst : DecidableEq ι} :
    weight T l (@Function.update _ _ inst x i a) = weight T l x := by
  funext v
  by_cases hv : v ∈ T
  · rw [weight_of_mem l _ hv, weight_of_mem l _ hv]
  · rw [weight_of_notMem l _ hv, weight_of_notMem l _ hv,
      Function.update_of_ne (fun h => hv (by rw [h]; exact hi))]

theorem weight_update_of_notMem {T : Finset ι} (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) {i : ι}
    (hi : i ∉ T) (a : V i) {inst : DecidableEq ι} :
    weight T l (@Function.update _ _ inst x i a) =
      @Function.update _ _ inst (weight T l x) i (l i a) := by
  funext v
  by_cases hvi : v = i
  · subst hvi
    rw [Function.update_self, weight_of_notMem l _ hi, Function.update_self]
  · rw [Function.update_of_ne hvi]
    by_cases hv : v ∈ T
    · rw [weight_of_mem l _ hv, weight_of_mem l _ hv]
    · rw [weight_of_notMem l _ hv, weight_of_notMem l _ hv, Function.update_of_ne hvi]

theorem restrict_update_of_mem {T : Finset ι} (x : ∀ v, V v) {i : ι} (hi : i ∈ T) (a : V i)
    {inst : DecidableEq ι} :
    (fun v : T => @Function.update _ _ inst x i a v) =
      Function.update (fun v : T => x v) ⟨i, hi⟩ a := by
  funext ⟨v, hv⟩
  by_cases hvi : v = i
  · subst hvi
    simp
  · rw [Function.update_of_ne hvi, Function.update_of_ne (fun h => hvi (congrArg Subtype.val h))]

theorem restrict_update_of_notMem {T : Finset ι} (x : ∀ v, V v) {i : ι} (hi : i ∉ T) (a : V i)
    {inst : DecidableEq ι} :
    (fun v : T => @Function.update _ _ inst x i a v) = fun v : T => x v := by
  funext ⟨v, hv⟩
  rw [Function.update_of_ne (fun h => hi (by rw [← h]; exact hv))]

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

def restrictedIndicator (ξ x : ∀ v, V v) : ℂ := by
  classical
  exact if IsRestricted ξ x then 1 else 0

theorem restrictedIndicator_of {ξ x : ∀ v, V v} (h : IsRestricted ξ x) :
    restrictedIndicator ξ x = 1 := by
  simp [restrictedIndicator, h]

theorem restrictedIndicator_of_not {ξ x : ∀ v, V v} (h : ¬ IsRestricted ξ x) :
    restrictedIndicator ξ x = 0 := by
  simp [restrictedIndicator, h]

def restrictedLift (ξ : ∀ v, V v) (T : Finset ι) (l : ∀ v, Dual ℂ (V v))
    (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) (f : MultilinearMap ℂ (fun v : T => V v) N) :
    MultilinearMap ℂ V N where
  toFun x := restrictedIndicator ξ x • (∏ᶠ v, weight T l x v) • f (fun v => x v)
  map_update_add' := by
    intro inst x i a b
    by_cases hx : IsRestricted ξ x
    · have h1 : ∀ c : V i, IsRestricted ξ (@Function.update _ _ inst x i c) := fun c => by
        have := @IsRestricted.update _ _ _ _ inst ξ x hx i c
        exact this
      simp only [restrictedIndicator_of (h1 _), one_smul]
      by_cases hi : i ∈ T
      · simp only [weight_update_of_mem l x hi, restrict_update_of_mem x hi]
        rw [f.map_update_add, smul_add]
      · simp only [weight_update_of_notMem l x hi, restrict_update_of_notMem x hi]
        have hw := finite_mulSupport_weight hx T hl
        rw [finprod_update_eq_mul _ hw, finprod_update_eq_mul _ hw (c := l i a),
          finprod_update_eq_mul _ hw (c := l i b), map_add, add_mul, add_smul]
    · have h1 : ∀ c : V i, ¬ IsRestricted ξ (@Function.update _ _ inst x i c) := fun c h => by
        apply hx
        have := @IsRestricted.update _ _ _ _ inst ξ _ h i (x i)
        rwa [Function.update_idem, Function.update_eq_self] at this
      simp [restrictedIndicator_of_not (h1 _)]
  map_update_smul' := by
    intro inst x i c a
    by_cases hx : IsRestricted ξ x
    · have h1 : ∀ c : V i, IsRestricted ξ (@Function.update _ _ inst x i c) := fun c => by
        have := @IsRestricted.update _ _ _ _ inst ξ x hx i c
        exact this
      simp only [restrictedIndicator_of (h1 _), one_smul]
      by_cases hi : i ∈ T
      · simp only [weight_update_of_mem l x hi, restrict_update_of_mem x hi]
        rw [f.map_update_smul, smul_comm]
      · simp only [weight_update_of_notMem l x hi, restrict_update_of_notMem x hi]
        have hw := finite_mulSupport_weight hx T hl
        rw [finprod_update_eq_mul _ hw (c := l i (c • a)), finprod_update_eq_mul _ hw (c := l i a),
          map_smul, smul_eq_mul, mul_assoc, mul_smul]
    · have h1 : ∀ c : V i, ¬ IsRestricted ξ (@Function.update _ _ inst x i c) := fun c h => by
        apply hx
        have := @IsRestricted.update _ _ _ _ inst ξ _ h i (x i)
        rwa [Function.update_idem, Function.update_eq_self] at this
      simp [restrictedIndicator_of_not (h1 _)]

theorem restrictedLift_apply_of {ξ : ∀ v, V v} {T : Finset ι} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} (f : MultilinearMap ℂ (fun v : T => V v) N)
    {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    restrictedLift ξ T l hl f x = (∏ᶠ v, weight T l x v) • f (fun v => x v) := by
  show restrictedIndicator ξ x • ((∏ᶠ v, weight T l x v) • f (fun v => x v)) = _
  rw [restrictedIndicator_of hx, one_smul]

def evalForm (ξ : ∀ v, V v) (l : ∀ v, Dual ℂ (V v)) (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) :
    (⨂[ℂ] v, V v) →ₗ[ℂ] ℂ :=
  lift (restrictedLift ξ ∅ l hl (MultilinearMap.constOfIsEmpty ℂ _ 1))

theorem evalForm_tprod {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    evalForm ξ l hl (tprod ℂ x) = ∏ᶠ v, l v (x v) := by
  rw [evalForm, lift.tprod, restrictedLift_apply_of _ hx]
  simp only [MultilinearMap.constOfIsEmpty_apply, Function.const_apply, smul_eq_mul, mul_one]
  exact finprod_congr fun v => weight_of_notMem l x (Finset.notMem_empty v)

def projSingleton (v : ι) : MultilinearMap ℂ (fun w : ({v} : Finset ι) => V w) (V v) where
  toFun y := y ⟨v, Finset.mem_singleton_self v⟩
  map_update_add' := by
    intro inst y j a b
    obtain rfl : j = ⟨v, Finset.mem_singleton_self v⟩ := Subsingleton.elim _ _
    simp
  map_update_smul' := by
    intro inst y j c a
    obtain rfl : j = ⟨v, Finset.mem_singleton_self v⟩ := Subsingleton.elim _ _
    simp

def contract (ξ : ∀ v, V v) (l : ∀ v, Dual ℂ (V v)) (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1)
    (v : ι) : (⨂[ℂ] w, V w) →ₗ[ℂ] V v :=
  lift (restrictedLift ξ {v} l hl (projSingleton v))

theorem contract_tprod {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} (v : ι) {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    contract ξ l hl v (tprod ℂ x) = (∏ᶠ w, weight {v} l x w) • x v := by
  rw [contract, lift.tprod, restrictedLift_apply_of _ hx]
  rfl

theorem finprod_eq_mul_weight {ξ x : ∀ v, V v} (hx : IsRestricted ξ x) {l : ∀ v, Dual ℂ (V v)}
    (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) (v : ι) :
    ∏ᶠ w, l w (x w) = l v (x v) * ∏ᶠ w, weight {v} l x w := by
  classical
  have h0 : (fun w => l w (x w)) = weight ∅ l x := by
    funext w; rw [weight_of_notMem l x (Finset.notMem_empty w)]
  have h1 : weight {v} l x = Function.update (weight ∅ l x) v 1 := by
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, weight_of_mem l x (Finset.mem_singleton_self w)]
    · rw [Function.update_of_ne hw, weight_of_notMem l x (by simpa using hw),
        weight_of_notMem l x (Finset.notMem_empty w)]
  have h2 : weight ∅ l x = Function.update (weight ∅ l x) v (l v (x v)) := by
    have : weight ∅ l x v = l v (x v) := weight_of_notMem l x (Finset.notMem_empty v)
    rw [← this, Function.update_eq_self]
  rw [h0, h1]
  conv_lhs => rw [h2]
  exact finprod_update_eq_mul _ (finite_mulSupport_weight hx ∅ hl) v _

theorem apply_contract {ξ : ∀ v, V v} {l : ∀ v, Dual ℂ (V v)}
    {hl : ∀ᶠ v in cofinite, l v (ξ v) = 1} (v : ι) (t : ⨂[ℂ] w, V w) :
    l v (contract ξ l hl v t) = evalForm ξ l hl t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, map_smul, map_smul]
    congr 1
    by_cases hx : IsRestricted ξ x
    · rw [contract_tprod v hx, evalForm_tprod hx, map_smul, smul_eq_mul, mul_comm,
        finprod_eq_mul_weight hx hl v]
    · rw [contract, evalForm, lift.tprod, lift.tprod]
      show l v (restrictedIndicator ξ x • _) = restrictedIndicator ξ x • _
      simp [restrictedIndicator_of_not hx]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end Lift

section Finite

variable [DecidableEq ι]

def extend (ξ : ∀ v, V v) (T : Finset ι) (y : ∀ v : T, V v) : ∀ v, V v :=
  fun v => if h : v ∈ T then y ⟨v, h⟩ else ξ v

theorem isRestricted_extend (ξ : ∀ v, V v) (T : Finset ι) (y : ∀ v : T, V v) :
    IsRestricted ξ (extend ξ T y) := by
  rw [isRestricted_iff_finite]
  refine T.finite_toSet.subset fun v hv => ?_
  by_contra hvT
  have hvT' : v ∉ T := by simpa using hvT
  exact hv (by simp [extend, hvT'])

def finiteEmbed (ξ : ∀ v, V v) (T : Finset ι) : (⨂[ℂ] v : T, V v) →ₗ[ℂ] ⨂[ℂ] v, V v :=
  lift ((PiTensorProduct.tprod ℂ).domDomRestrict (· ∈ T) fun w => ξ w)

theorem finiteEmbed_tprod (ξ : ∀ v, V v) (T : Finset ι) (y : ∀ v : T, V v) :
    finiteEmbed ξ T (tprod ℂ y) = tprod ℂ (extend ξ T y) := by
  rw [finiteEmbed, lift.tprod, MultilinearMap.domDomRestrict_apply]
  rfl

theorem range_finiteEmbed_le (ξ : ∀ v, V v) (T : Finset ι) :
    LinearMap.range (finiteEmbed ξ T) ≤ restrictedTensor ξ := by
  rintro _ ⟨t, rfl⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    rw [map_smul, finiteEmbed_tprod]
    exact Submodule.smul_mem _ _ (tprod_mem_restrictedTensor (isRestricted_extend ξ T y))
  | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

theorem extend_restrict {ξ x : ∀ v, V v} {T : Finset ι} (h : ∀ v ∉ T, x v = ξ v) :
    extend ξ T (fun v => x v) = x := by
  funext v
  unfold extend
  split_ifs with hv
  · rfl
  · exact (h v hv).symm

theorem finiteEmbed_injective {ξ : ∀ v, V v} {T : Finset ι} (hξ : ∀ v ∉ T, ξ v ≠ 0) :
    Injective (finiteEmbed ξ T) := by
  have hex : ∀ v, ∃ f : Dual ℂ (V v), v ∉ T → f (ξ v) = 1 := by
    intro v
    by_cases hv : v ∈ T
    · exact ⟨0, fun h => absurd hv h⟩
    · obtain ⟨f, hf⟩ : ∃ f : Dual ℂ (V v), f (ξ v) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hξ v hv ((Module.forall_dual_apply_eq_zero_iff ℂ (ξ v)).1 hcon)
      exact ⟨(f (ξ v))⁻¹ • f, fun _ => by simp [hf]⟩
  choose l hl using hex
  have hl' : ∀ᶠ v in cofinite, l v (ξ v) = 1 :=
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra hvT
      exact hv (hl v hvT))
  let P := lift (restrictedLift ξ T l hl' (PiTensorProduct.tprod ℂ))
  have hP : P ∘ₗ finiteEmbed ξ T = LinearMap.id := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun y => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, finiteEmbed_tprod,
      LinearMap.id_apply, P, lift.tprod]
    rw [restrictedLift_apply_of _ (isRestricted_extend ξ T y)]
    have hw : weight T l (extend ξ T y) = fun _ => 1 := by
      funext v
      by_cases hv : v ∈ T
      · exact weight_of_mem l _ hv
      · rw [weight_of_notMem l _ hv]
        simp [extend, hv, hl v hv]
    rw [hw, finprod_one, one_smul]
    congr 1
    funext ⟨v, hv⟩
    simp [extend, hv]
  exact Function.LeftInverse.injective (g := P) fun t => by
    simpa using congrArg (fun F => F t) hP

theorem exists_mem_range_finiteEmbed {ξ : ∀ v, V v} {t : ⨂[ℂ] v, V v}
    (ht : t ∈ restrictedTensor ξ) : ∃ T₀ : Finset ι, ∀ T, T₀ ⊆ T →
      t ∈ LinearMap.range (finiteEmbed ξ T) := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, hx, rfl⟩ := ht
    refine ⟨(isRestricted_iff_finite.1 hx).toFinset, fun T hT => ⟨tprod ℂ fun v => x v, ?_⟩⟩
    rw [finiteEmbed_tprod, extend_restrict]
    intro v hv
    by_contra hxv
    exact hv (hT (by simpa using hxv))
  | zero => exact ⟨∅, fun T _ => Submodule.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hA⟩ := ha
    obtain ⟨B, hB⟩ := hb
    exact ⟨A ∪ B, fun T hT => Submodule.add_mem _ (hA T (Finset.union_subset_left hT))
      (hB T (Finset.union_subset_right hT))⟩
  | smul c a _ ha =>
    obtain ⟨A, hA⟩ := ha
    exact ⟨A, fun T hT => Submodule.smul_mem _ c (hA T hT)⟩

theorem exists_evalForm_ne_zero {ξ : ∀ v, V v} (hξ : ∀ᶠ v in cofinite, ξ v ≠ 0)
    {t : ⨂[ℂ] v, V v} (ht : t ∈ restrictedTensor ξ) (ht0 : t ≠ 0) :
    ∃ (l : ∀ v, Dual ℂ (V v)) (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1), evalForm ξ l hl t ≠ 0 := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_mem_range_finiteEmbed ht
  set T : Finset ι := T₀ ∪ (Filter.eventually_cofinite.1 hξ).toFinset
  have hξT : ∀ v ∉ T, ξ v ≠ 0 := fun v hv h => hv (Finset.mem_union_right _ (by simpa using h))
  obtain ⟨s, rfl⟩ := hT₀ T Finset.subset_union_left
  have hs0 : s ≠ 0 := by rintro rfl; exact ht0 (map_zero _)
  let b : ∀ v : T, Basis (Basis.ofVectorSpaceIndex ℂ (V v)) ℂ (V v) :=
    fun v => Basis.ofVectorSpace ℂ (V v)
  let B := Basis.piTensorProduct b
  obtain ⟨k, hk⟩ : ∃ k, B.repr s k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hs0 (B.repr.injective (Finsupp.ext fun k => by simp [hcon k]))
  have hex : ∀ v, ∃ f : Dual ℂ (V v), v ∉ T → f (ξ v) = 1 := by
    intro v
    by_cases hv : v ∈ T
    · exact ⟨0, fun h => absurd hv h⟩
    · obtain ⟨f, hf⟩ : ∃ f : Dual ℂ (V v), f (ξ v) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hξT v hv ((Module.forall_dual_apply_eq_zero_iff ℂ (ξ v)).1 hcon)
      exact ⟨(f (ξ v))⁻¹ • f, fun _ => by simp [hf]⟩
  choose f hf using hex
  let l : ∀ v, Dual ℂ (V v) := fun v => if hv : v ∈ T then (b ⟨v, hv⟩).coord (k ⟨v, hv⟩) else f v
  have hl : ∀ᶠ v in cofinite, l v (ξ v) = 1 :=
    Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra hvT
      have hvT' : v ∉ T := by simpa using hvT
      exact hv (by simp [l, hvT', hf v hvT']))
  refine ⟨l, hl, ?_⟩
  have key : evalForm ξ l hl ∘ₗ finiteEmbed ξ T = B.coord k := by
    refine B.ext fun k' => ?_
    rw [Basis.coord_apply, Basis.repr_self, LinearMap.comp_apply, Basis.piTensorProduct_apply,
      finiteEmbed_tprod, evalForm_tprod (isRestricted_extend ξ T _),
      finprod_eq_prod_of_mulSupport_subset (s := T)]
    · rw [← Finset.prod_coe_sort T]
      have hterm : ∀ v : T, l v (extend ξ T (fun i => b i (k' i)) v) =
          if k' v = k v then 1 else 0 := by
        intro v
        simp only [l, extend, Finset.coe_mem, dif_pos, Basis.coord_apply,
          Basis.repr_self, Finsupp.single_apply]
      simp only [hterm, Finsupp.single_apply]
      by_cases hkk : k' = k
      · subst hkk; simp
      · rw [if_neg hkk]
        obtain ⟨v, hv⟩ : ∃ v, k' v ≠ k v := by
          by_contra hcon
          push Not at hcon
          exact hkk (funext hcon)
        exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])
    · intro v hv
      by_contra hvT
      have hvT' : v ∉ T := by simpa using hvT
      apply hv
      simp [l, extend, hvT', hf v hvT']
  have := congrArg (fun F => F s) key
  simp only [LinearMap.comp_apply, Basis.coord_apply] at this
  rw [this]
  exact hk

end Finite

section Rep

variable {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}

variable (K) in

def tensorRep (π : ∀ v, Representation ℂ (G v) (V v)) :
    Representation ℂ (Πʳ v, [G v, K v]) (⨂[ℂ] v, V v) where
  toFun g := PiTensorProduct.map fun v => π v (g v)
  map_one' := by
    simp only [RestrictedProduct.one_apply, map_one]
    exact PiTensorProduct.map_id
  map_mul' g h := by
    simp only [RestrictedProduct.mul_apply, map_mul]
    exact PiTensorProduct.map_mul _ _

theorem tensorRep_tprod (π : ∀ v, Representation ℂ (G v) (V v)) (g : Πʳ v, [G v, K v])
    (x : ∀ v, V v) :
    tensorRep K π g (tprod ℂ x) = tprod ℂ fun v => π v (g v) (x v) :=
  PiTensorProduct.map_tprod _ _

def restrictedSubrep (π : ∀ v, Representation ℂ (G v) (V v)) (ξ : ∀ v, V v)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) :
    Subrepresentation (tensorRep K π) where
  toSubmodule := restrictedTensor ξ
  apply_mem_toSubmodule g t ht := by
    have : restrictedTensor ξ ≤ (restrictedTensor ξ).comap (tensorRep K π g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, tensorRep_tprod]
      refine tprod_mem_restrictedTensor ?_
      filter_upwards [(hx : ∀ᶠ v in cofinite, x v = ξ v), hξ, g.2] with v h1 h2 h3
      rw [h1]
      exact h2 _ h3
    exact this ht

def restrictedTensorRep (π : ∀ v, Representation ℂ (G v) (V v)) (ξ : ∀ v, V v)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) :
    Representation ℂ (Πʳ v, [G v, K v]) (restrictedTensor ξ) :=
  (restrictedSubrep π ξ hξ).toRepresentation

theorem coe_restrictedTensorRep_apply (π : ∀ v, Representation ℂ (G v) (V v)) (ξ : ∀ v, V v)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) (g : Πʳ v, [G v, K v])
    (t : restrictedTensor ξ) :
    (restrictedTensorRep π ξ hξ g t : ⨂[ℂ] v, V v) = tensorRep K π g t :=
  rfl

end Rep

end RestrictedTensor

end GroundTheory.Automorphic
