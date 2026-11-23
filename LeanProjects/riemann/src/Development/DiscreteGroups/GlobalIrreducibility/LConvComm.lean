import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

open Module

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace DiscreteGroups.sglob.LConv.Comm

section Gen
variable {K M N N' : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']

theorem finrank_map_add_inf_ker (P : Submodule K M) (f : M →ₗ[K] N) :
    finrank K (P.map f) + finrank K (P ⊓ LinearMap.ker f : Submodule K M) = finrank K P := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict P)
  have h2 : LinearMap.range (f.domRestrict P) = P.map f := by
    apply Submodule.ext; intro y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
      exact Submodule.mem_map.2 ⟨z, z.2, rfl⟩
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      exact LinearMap.mem_range.2 ⟨⟨z, hz⟩, rfl⟩
  have h3 : finrank K (LinearMap.ker (f.domRestrict P)) =
      finrank K (P ⊓ LinearMap.ker f : Submodule K M) := by
    have e := Submodule.equivMapOfInjective P.subtype (by intro u w h; exact Subtype.ext h)
      (LinearMap.ker (f.domRestrict P))
    rw [e.finrank_eq]
    have heq : Submodule.map P.subtype (LinearMap.ker (f.domRestrict P)) =
        (P ⊓ LinearMap.ker f : Submodule K M) := by
      apply Submodule.ext; intro x
      constructor
      · intro hx'
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx'
        exact Submodule.mem_inf.2 ⟨y.2, LinearMap.mem_ker.2 (by simpa using LinearMap.mem_ker.1 hy)⟩
      · intro hx
        obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
        exact Submodule.mem_map.2
          ⟨⟨x, hx1⟩, LinearMap.mem_ker.2 (by simpa using LinearMap.mem_ker.1 hx2), rfl⟩
    rw [heq]
  rw [← h2, ← h3]; exact h1

theorem finrank_map_le_of_ker (P : Submodule K M) (f : M →ₗ[K] N) (g : M →ₗ[K] N')
    (h : ∀ x ∈ P, g x = 0 → f x = 0) : finrank K (P.map f) ≤ finrank K (P.map g) := by
  have hf := finrank_map_add_inf_ker P f
  have hg := finrank_map_add_inf_ker P g
  have : finrank K (P ⊓ LinearMap.ker g : Submodule K M) ≤
      finrank K (P ⊓ LinearMap.ker f : Submodule K M) := by
    apply Submodule.finrank_mono
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    exact Submodule.mem_inf.2 ⟨hx1, LinearMap.mem_ker.2 (h x hx1 (LinearMap.mem_ker.1 hx2))⟩
  omega

theorem finrank_le_add_of_ker (P : Submodule K M) (f : M →ₗ[K] N) (g : M →ₗ[K] N')
    (h : ∀ x ∈ P, f x = 0 → g x = 0 → x = 0) :
    finrank K P ≤ finrank K (P.map f) + finrank K (P.map g) := by
  have hf := finrank_map_add_inf_ker P f
  have hQ := finrank_map_add_inf_ker (P ⊓ LinearMap.ker f) g
  have h0 : (P ⊓ LinearMap.ker f) ⊓ LinearMap.ker g = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    obtain ⟨hx3, hx4⟩ := Submodule.mem_inf.1 hx1
    exact (Submodule.mem_bot K).2 (h x hx3 (LinearMap.mem_ker.1 hx4) (LinearMap.mem_ker.1 hx2))
  rw [h0] at hQ
  simp only [finrank_bot, add_zero] at hQ
  have : finrank K ((P ⊓ LinearMap.ker f).map g) ≤ finrank K (P.map g) :=
    Submodule.finrank_mono (Submodule.map_mono inf_le_left)
  omega

theorem injective_bound (P : Submodule K M) (f : M →ₗ[K] N) [FiniteDimensional K N]
    (h : ∀ x ∈ P, f x = 0 → x = 0) : finrank K P ≤ finrank K N := by
  have hf := finrank_map_add_inf_ker P f
  have h0 : P ⊓ LinearMap.ker f = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    exact (Submodule.mem_bot K).2 (h x hx1 (LinearMap.mem_ker.1 hx2))
  rw [h0] at hf
  simp only [finrank_bot, add_zero] at hf
  have := Submodule.finrank_le (P.map f)
  omega

end Gen

section Res
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def pre (W : Submodule ℂ V) : Module.End ℂ V →ₗ[ℂ] (W →ₗ[ℂ] V) where
  toFun x := x ∘ₗ W.subtype
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def post (W : Submodule ℂ V) : Module.End ℂ W →ₗ[ℂ] (W →ₗ[ℂ] V) where
  toFun y := W.subtype ∘ₗ y
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def rs (W : Submodule ℂ V) (x : Module.End ℂ V) (h : ∀ v ∈ W, x v ∈ W) : Module.End ℂ W :=
  LinearMap.codRestrict W (x.domRestrict W) (fun v => h v v.2)

theorem rs_coe (W : Submodule ℂ V) (x : Module.End ℂ V) (h : ∀ v ∈ W, x v ∈ W) (v : W) :
    ((rs W x h v : W) : V) = x v := rfl

theorem rs_comm (W : Submodule ℂ V) {ι : Type*} (a : ι → Module.End ℂ V)
    (ha : ∀ i j, a i * a j = a j * a i) (h : ∀ i, ∀ v ∈ W, a i v ∈ W) (i j : ι) :
    rs W (a i) (h i) * rs W (a j) (h j) = rs W (a j) (h j) * rs W (a i) (h i) := by
  apply LinearMap.ext; intro v; apply Subtype.ext
  show a i (a j (v : V)) = a j (a i (v : V))
  exact LinearMap.congr_fun (ha i j) v

theorem comm_of_mem {ι : Type*} (a : ι → Module.End ℂ V) (y : Module.End ℂ V)
    (hy : ∀ i, a i * y = y * a i) {x : Module.End ℂ V} (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    x * y = y * x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hy j
  | algebraMap r => exact Algebra.commutes r y
  | add x z _ _ hx hz => rw [add_mul, mul_add, hx, hz]
  | mul x z _ _ hx hz => rw [mul_assoc, hz, ← mul_assoc, hx, mul_assoc]

theorem exists_post (W : Submodule ℂ V) {ι : Type*} (a : ι → Module.End ℂ V)
    (h : ∀ i, ∀ v ∈ W, a i v ∈ W) {x : Module.End ℂ V}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∃ y ∈ Algebra.adjoin ℂ (Set.range (fun i => rs W (a i) (h i))), post W y = pre W x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨rs W (a i) (h i), Algebra.subset_adjoin (Set.mem_range_self i), LinearMap.ext fun v => rfl⟩
  | algebraMap r =>
    refine ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, LinearMap.ext fun v => ?_⟩
    first
    | rfl
    | simp [pre, post]
    | simp [pre, post, Module.algebraMap_end_apply]
  | add x z _ _ hx hz =>
    obtain ⟨y1, h1, e1⟩ := hx
    obtain ⟨y2, h2, e2⟩ := hz
    exact ⟨y1 + y2, add_mem h1 h2, by rw [map_add, map_add, e1, e2]⟩
  | mul x z _ _ hx hz =>
    obtain ⟨y1, h1, e1⟩ := hx
    obtain ⟨y2, h2, e2⟩ := hz
    refine ⟨y1 * y2, mul_mem h1 h2, LinearMap.ext fun v => ?_⟩
    have e1' := LinearMap.congr_fun e1 (y2 v)
    have e2' := LinearMap.congr_fun e2 v
    change ((y1 (y2 v) : W) : V) = x (z (v : V))
    change ((y1 (y2 v) : W) : V) = x ((y2 v : W) : V) at e1'
    change ((y2 v : W) : V) = z (v : V) at e2'
    rw [e1', e2']

theorem sub_finrank (S : Subalgebra ℂ (Module.End ℂ V)) [FiniteDimensional ℂ V] :
    finrank ℂ (Subalgebra.toSubmodule S) = finrank ℂ S := by
  first
  | exact Subalgebra.finrank_toSubmodule S
  | rfl

theorem finrank_map_pre_le [FiniteDimensional ℂ V] (W : Submodule ℂ V) {ι : Type*}
    (a : ι → Module.End ℂ V) (h : ∀ i, ∀ v ∈ W, a i v ∈ W) :
    finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (pre W)) ≤
      finrank ℂ (Algebra.adjoin ℂ (Set.range (fun i => rs W (a i) (h i)))) := by
  rw [← sub_finrank]
  calc _ ≤ finrank ℂ ((Subalgebra.toSubmodule
          (Algebra.adjoin ℂ (Set.range (fun i => rs W (a i) (h i))))).map (post W)) := by
        apply Submodule.finrank_mono
        intro u hu
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hu
        obtain ⟨y, hy, e⟩ := exists_post W a h hx
        exact Submodule.mem_map.2 ⟨y, hy, e⟩
    _ ≤ _ := Submodule.finrank_map_le _ _

theorem finrank_hom [FiniteDimensional ℂ V] (W : Submodule ℂ V) :
    finrank ℂ (W →ₗ[ℂ] V) = finrank ℂ W * finrank ℂ V := by
  first
  | exact Module.finrank_linearMap ℂ ℂ W V
  | exact Module.finrank_linearMap ℂ W V
  | simp [Module.finrank_linearMap]

theorem finrank_end [FiniteDimensional ℂ V] :
    finrank ℂ (Module.End ℂ V) = finrank ℂ V * finrank ℂ V := by
  first
  | exact Module.finrank_linearMap ℂ ℂ V V
  | exact Module.finrank_linearMap ℂ V V
  | simp [Module.finrank_linearMap]

theorem finrank_sub_le_sq [FiniteDimensional ℂ V] (S : Subalgebra ℂ (Module.End ℂ V)) :
    finrank ℂ S ≤ finrank ℂ V * finrank ℂ V := by
  rw [← sub_finrank, ← finrank_end]
  exact Submodule.finrank_le _

theorem nak_one (U : Submodule ℂ V) (c : Module.End ℂ V) (N : ℕ) (hc : c ^ N = 0)
    (hU : ∀ v ∈ U, c v ∈ U) (h : U ⊔ LinearMap.range c = ⊤) : U = ⊤ := by
  have key : ∀ k : ℕ, U ⊔ LinearMap.range (c ^ k) = ⊤ := by
    intro k
    induction k with
    | zero =>
      rw [eq_top_iff]; intro v _
      exact Submodule.mem_sup_right (LinearMap.mem_range.2 ⟨v, by simp⟩)
    | succ k ih =>
      rw [eq_top_iff]; intro v _
      have hv : v ∈ U ⊔ LinearMap.range c := by rw [h]; exact Submodule.mem_top
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hw
      have hz : z ∈ U ⊔ LinearMap.range (c ^ k) := by rw [ih]; exact Submodule.mem_top
      obtain ⟨u', hu', w', hw', rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨z', rfl⟩ := LinearMap.mem_range.1 hw'
      rw [map_add, ← add_assoc]
      apply Submodule.add_mem_sup (U.add_mem hu (hU _ hu'))
      exact LinearMap.mem_range.2 ⟨z', by rw [pow_succ']; rfl⟩
  have := key N
  rwa [hc, LinearMap.range_zero, sup_bot_eq] at this

theorem iSup_range_inv {ι : Type*} (s : Finset ι) (b : ι → Module.End ℂ V) (x : Module.End ℂ V)
    (hx : ∀ i, x * b i = b i * x) :
    ∀ v ∈ (⨆ i ∈ s, LinearMap.range (b i)), x v ∈ (⨆ i ∈ s, LinearMap.range (b i)) := by
  have hle : (⨆ i ∈ s, LinearMap.range (b i)) ≤ (⨆ i ∈ s, LinearMap.range (b i)).comap x := by
    refine iSup₂_le fun i hi => ?_
    intro w hw
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hw
    rw [Submodule.mem_comap]
    have e : x (b i z) = b i (x z) := LinearMap.congr_fun (hx i) z
    rw [e]
    exact (le_iSup₂ (f := fun i (_ : i ∈ s) => LinearMap.range (b i)) i hi)
      (LinearMap.mem_range_self _ _)
  intro v hv
  exact Submodule.mem_comap.1 (hle hv)

theorem nak {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → Module.End ℂ V)
    (hcomm : ∀ i j, b i * b j = b j * b i) (hnil : ∀ i, ∃ N : ℕ, b i ^ N = 0) :
    ∀ U : Submodule ℂ V, (∀ i, ∀ v ∈ U, b i v ∈ U) →
      U ⊔ (⨆ i ∈ s, LinearMap.range (b i)) = ⊤ → U = ⊤ := by
  induction s using Finset.induction_on with
  | empty => intro U _ h; simpa using h
  | insert j s hj ih =>
    intro U hU h
    rw [Finset.iSup_insert] at h
    apply ih U hU
    obtain ⟨N, hN⟩ := hnil j
    apply nak_one _ (b j) N hN
    · intro v hv
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      exact Submodule.add_mem_sup (hU j u hu)
        (iSup_range_inv s b (b j) (fun i => hcomm j i) w hw)
    · rw [← h]
      apply le_antisymm
      · exact sup_le (sup_le le_sup_left (le_sup_of_le_right le_sup_right))
          (le_sup_of_le_right le_sup_left)
      · exact sup_le (le_sup_of_le_left le_sup_left)
          (sup_le le_sup_right (le_sup_of_le_left le_sup_right))

end Res

def Pl (l t c : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : Fin l → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) →
    t * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      Module.finrank ℂ V ^ 2 + c * Module.finrank ℂ V

theorem base (t : ℕ) : Pl 0 t t := by
  intro V _ _ _ a _
  rw [Set.range_eq_empty a, Algebra.adjoin_empty]
  have hsq := finrank_sub_le_sq (V := V) ⊥
  rcases Nat.eq_zero_or_pos (finrank ℂ V) with h0 | hpos
  · rw [h0] at hsq ⊢
    have : finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) = 0 := by omega
    rw [this]; simp
  · haveI : Nontrivial V := Module.finrank_pos_iff.1 hpos
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    haveI : Nontrivial (Module.End ℂ V) :=
      ⟨⟨1, 0, fun h => hv (by simpa using LinearMap.congr_fun h v)⟩⟩
    have h1 : finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) ≤ 1 := by
      first
      | exact (Subalgebra.finrank_bot).le
      | exact le_of_eq Subalgebra.finrank_bot
      | simp
    have e1 := Nat.mul_le_mul_left t h1
    have e2 := Nat.mul_le_mul_left t (show 1 ≤ finrank ℂ V from hpos)
    nlinarith

def IHn (l t c n : ℕ) : Prop :=
  ∀ m < n, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    finrank ℂ V = m → ∀ (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) →
    t * finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ m ^ 2 + c * m

theorem split_case (l t c n : ℕ) (IH : IHn l t c n) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hn : finrank ℂ V = n) (a : Fin (l + 1) → Module.End ℂ V)
    (ha : ∀ i j, a i * a j = a j * a i) (μ : Fin (l + 1) → ℂ)
    (hμ : ∀ i, Module.End.HasEigenvalue (a i) (μ i)) (N : Fin (l + 1) → ℕ)
    (hN : ∀ i, IsCompl (LinearMap.ker ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i))
      (LinearMap.range ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i)) ∧ 1 ≤ N i)
    (hs : ∃ i, LinearMap.range ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i) ≠ ⊥) :
    t * finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ n ^ 2 + c * n := by
  obtain ⟨i, hi⟩ := hs
  have hc := (hN i).1
  have hfA : (a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i ∈ Algebra.adjoin ℂ (Set.range a) :=
    pow_mem (sub_mem (Algebra.subset_adjoin (Set.mem_range_self i)) (Subalgebra.algebraMap_mem _ _)) _
  generalize hf : (a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i = f at hc hi hfA
  have hxa : ∀ j, f * a j = a j * f := fun j => comm_of_mem a (a j) (fun k => ha k j) hfA
  have hKinv : ∀ j, ∀ v ∈ LinearMap.ker f, a j v ∈ LinearMap.ker f := by
    intro j v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have e : f (a j v) = a j (f v) := LinearMap.congr_fun (hxa j) v
    rw [e, hv, map_zero]
  have hRinv : ∀ j, ∀ v ∈ LinearMap.range f, a j v ∈ LinearMap.range f := by
    intro j v hv
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hv
    have e : f (a j w) = a j (f w) := LinearMap.congr_fun (hxa j) w
    exact LinearMap.mem_range.2 ⟨a j w, e⟩
  have hKne : LinearMap.ker f ≠ ⊥ := by
    obtain ⟨v, hv⟩ := (hμ i).exists_hasEigenvector
    have hav : a i v = μ i • v := by
      first
      | exact hv.apply_eq_smul
      | exact Module.End.mem_eigenspace_iff.1 hv.1
    have hv0 : v ≠ 0 := by
      first
      | exact hv.2
      | exact hv.right
      | exact hv.ne_zero
    have hbv : (a i - algebraMap ℂ (Module.End ℂ V) (μ i)) v = 0 := by
      first
      | rw [LinearMap.sub_apply, Module.algebraMap_end_apply, hav, sub_self]
      | simp [hav]
    intro hK
    apply hv0
    have hvK : v ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, ← hf]
      obtain ⟨k, hk⟩ : ∃ k, N i = k + 1 := ⟨N i - 1, by have := (hN i).2; omega⟩
      rw [hk, pow_succ]
      show ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ k)
        ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) v) = 0
      rw [hbv, map_zero]
    rw [hK] at hvK
    exact (Submodule.mem_bot ℂ).1 hvK
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [hn] at hsum
  have hKpos : 0 < finrank ℂ (LinearMap.ker f) := by
    rcases Nat.eq_zero_or_pos (finrank ℂ (LinearMap.ker f)) with h | h
    · exact (hKne (by first | exact Submodule.finrank_eq_zero.1 h | exact finrank_eq_zero.1 h)).elim
    · exact h
  have hRpos : 0 < finrank ℂ (LinearMap.range f) := by
    rcases Nat.eq_zero_or_pos (finrank ℂ (LinearMap.range f)) with h | h
    · exact (hi (by first | exact Submodule.finrank_eq_zero.1 h | exact finrank_eq_zero.1 h)).elim
    · exact h
  have hK := IH _ (by omega) (LinearMap.ker f) rfl (fun j => rs _ (a j) (hKinv j))
    (rs_comm _ a ha hKinv)
  have hR := IH _ (by omega) (LinearMap.range f) rfl (fun j => rs _ (a j) (hRinv j))
    (rs_comm _ a ha hRinv)
  have h1 := finrank_le_add_of_ker (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)))
    (pre (LinearMap.ker f)) (pre (LinearMap.range f)) (by
      intro x _ hx1 hx2
      apply LinearMap.ext; intro v
      have hv : v ∈ LinearMap.ker f ⊔ LinearMap.range f := by
        rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.1 hv
      have e1 := LinearMap.congr_fun hx1 ⟨k, hk⟩
      have e2 := LinearMap.congr_fun hx2 ⟨r, hr⟩
      change x k = 0 at e1
      change x r = 0 at e2
      rw [map_add, e1, e2, add_zero, LinearMap.zero_apply])
  have h2 := finrank_map_pre_le (LinearMap.ker f) a hKinv
  have h3 := finrank_map_pre_le (LinearMap.range f) a hRinv
  rw [sub_finrank] at h1
  have h4 := Nat.mul_le_mul_left t (le_trans h1 (Nat.add_le_add h2 h3))
  rw [← hsum]
  nlinarith [Nat.zero_le (finrank ℂ (LinearMap.ker f) * finrank ℂ (LinearMap.range f))]

theorem decomp (l : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (a : Fin (l + 1) → Module.End ℂ V)
    (b0 : Module.End ℂ V) (μ0 : ℂ) (hb0 : b0 = a 0 - algebraMap ℂ (Module.End ℂ V) μ0)
    (hxb : ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * b0 = b0 * x)
    (hb0mem : b0 ∈ Algebra.adjoin ℂ (Set.range a))
    (hle : Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ) ≤ Algebra.adjoin ℂ (Set.range a))
    {x : Module.End ℂ V} (hx : x ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∃ y ∈ Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ),
      ∃ z ∈ Algebra.adjoin ℂ (Set.range a), x = y + b0 * z := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact ⟨algebraMap ℂ _ μ0, Subalgebra.algebraMap_mem _ _, 1, one_mem _,
        by rw [hb0, mul_one]; abel⟩
    · exact ⟨a j.succ, Algebra.subset_adjoin (Set.mem_range_self j), 0, zero_mem _, by rw [mul_zero, add_zero]⟩
  | algebraMap r =>
    exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ _, 0, zero_mem _,
      by rw [mul_zero, add_zero]⟩
  | add x1 x2 _ _ h1 h2 =>
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ := h1
    obtain ⟨y2, hy2, z2, hz2, rfl⟩ := h2
    exact ⟨y1 + y2, add_mem hy1 hy2, z1 + z2, add_mem hz1 hz2, by rw [mul_add]; abel⟩
  | mul x1 x2 _ _ h1 h2 =>
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ := h1
    obtain ⟨y2, hy2, z2, hz2, rfl⟩ := h2
    have hc1 : y1 * b0 = b0 * y1 := hxb y1 (hle hy1)
    have e : y1 * (b0 * z2) = b0 * (y1 * z2) := by rw [← mul_assoc, hc1, mul_assoc]
    refine ⟨y1 * y2, mul_mem hy1 hy2, z1 * y2 + y1 * z2 + z1 * (b0 * z2),
      add_mem (add_mem (mul_mem hz1 (hle hy2)) (mul_mem (hle hy1) hz2))
        (mul_mem hz1 (mul_mem hb0mem hz2)), ?_⟩
    simp only [add_mul, mul_add, mul_assoc]
    rw [e]; abel

theorem arith_local (t c n m n1 dA dA' d1 : ℕ) (hdim : n1 + m = n) (hI : dA ≤ m * n)
    (hsum2 : dA ≤ dA' + d1) (hA' : t * t * dA' ≤ n ^ 2 + c * n)
    (h1 : 1 ≤ m → t * d1 ≤ n1 ^ 2 + c * n1) : t * dA ≤ n ^ 2 + c * n := by
  by_cases hcase : t * m ≤ n + c
  · calc t * dA ≤ t * (m * n) := Nat.mul_le_mul_left _ hI
      _ = n * (t * m) := by ring
      _ ≤ n * (n + c) := Nat.mul_le_mul_left _ hcase
      _ = n ^ 2 + c * n := by ring
  · rw [not_le] at hcase
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hcase; omega
      · exact h
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h] at hcase; omega
      · exact h
    have hd1 := h1 hm
    subst hdim
    have e3 := Nat.mul_le_mul_left (t * t) hsum2
    have h5 := Nat.mul_le_mul_left t hd1
    have h3 : (n1 + m) * (n1 + m + c) ≤ (t * m) * (n1 + m + c) := Nat.mul_le_mul_right _ (by omega)
    have h4 : (t * m) * (n1 + m + c) ≤ (t * m) * (2 * n1 + m + c) := Nat.mul_le_mul_left _ (by omega)
    have key : t * (t * dA) ≤ t * ((n1 + m) ^ 2 + c * (n1 + m)) := by nlinarith
    by_contra hlt
    rw [not_le] at hlt
    have := Nat.mul_lt_mul_of_pos_left hlt htpos
    omega

theorem local_case (l t c : ℕ) (hP : Pl l (t * t) c) (n : ℕ) (IH : IHn l t c n) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (hn : finrank ℂ V = n)
    (a : Fin (l + 1) → Module.End ℂ V) (ha : ∀ i j, a i * a j = a j * a i) (μ : Fin (l + 1) → ℂ)
    (N : Fin (l + 1) → ℕ)
    (hs : ¬∃ i, LinearMap.range ((a i - algebraMap ℂ (Module.End ℂ V) (μ i)) ^ N i) ≠ ⊥) :
    t * finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ n ^ 2 + c * n := by
  simp only [not_exists, not_not] at hs
  let b : Fin (l + 1) → Module.End ℂ V := fun i => a i - algebraMap ℂ (Module.End ℂ V) (μ i)
  have hbmem : ∀ i, b i ∈ Algebra.adjoin ℂ (Set.range a) :=
    fun i => sub_mem (Algebra.subset_adjoin (Set.mem_range_self i)) (Subalgebra.algebraMap_mem _ _)
  have hab : ∀ i j, a j * b i = b i * a j := by
    intro i j; show a j * (a i - _) = (a i - _) * a j
    rw [mul_sub, sub_mul, ha j i, Algebra.commutes]
  have hxb : ∀ i, ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * b i = b i * x :=
    fun i x hx => comm_of_mem a (b i) (fun j => hab i j) hx
  have hbb : ∀ i j, b i * b j = b j * b i := fun i j => hxb j (b i) (hbmem i)
  have hnil : ∀ i, ∃ M : ℕ, b i ^ M = 0 := fun i => ⟨N i, LinearMap.range_eq_bot.1 (hs i)⟩
  obtain ⟨V1, hV1⟩ : ∃ V1 : Submodule ℂ V,
      V1 = ⨆ i ∈ (Finset.univ : Finset (Fin (l + 1))), LinearMap.range (b i) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ := Submodule.exists_isCompl V1
  have hdim := Submodule.finrank_add_eq_of_isCompl hL
  rw [hn] at hdim
  have hV1inv : ∀ j, ∀ v ∈ V1, a j v ∈ V1 := by
    rw [hV1]; exact fun j => iSup_range_inv _ b (a j) (fun i => hab i j)

  have hI : finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ finrank ℂ L * n := by
    rw [← sub_finrank, ← hn, ← finrank_hom L]
    apply injective_bound _ (pre L)
    intro x hx hx0
    have hLk : L ≤ LinearMap.ker x := by
      intro v hv
      have e := LinearMap.congr_fun hx0 ⟨v, hv⟩
      change x v = 0 at e
      exact LinearMap.mem_ker.2 e
    have hU : LinearMap.ker x = ⊤ := by
      apply nak Finset.univ b hbb hnil
      · intro i v hv
        rw [LinearMap.mem_ker] at hv ⊢
        have e : x (b i v) = b i (x v) := LinearMap.congr_fun (hxb i x hx) v
        rw [e, hv, map_zero]
      · rw [← hV1, eq_top_iff, ← hL.sup_eq_top]
        exact sup_le le_sup_right (le_sup_of_le_left hLk)
    exact LinearMap.ker_eq_top.1 hU
  have hle : Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ) ≤
      Algebra.adjoin ℂ (Set.range a) :=
    Algebra.adjoin_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.succ, rfl⟩)
  have hAsup : Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ)) ⊔
      (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (LinearMap.mulLeft ℂ (b 0)) := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := decomp l a (b 0) (μ 0) rfl (hxb 0) (hbmem 0) hle hx
    exact Submodule.add_mem_sup hy (Submodule.mem_map.2 ⟨z, hz, rfl⟩)
  have hmul : finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
      (LinearMap.mulLeft ℂ (b 0))) ≤
      finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (pre V1)) := by
    apply finrank_map_le_of_ker
    intro x hx hx0
    apply LinearMap.ext; intro v
    have hbv : b 0 v ∈ V1 := by
      rw [hV1]
      exact (le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin (l + 1)))) =>
        LinearMap.range (b i)) 0 (Finset.mem_univ 0)) (LinearMap.mem_range_self _ _)
    have e1 := LinearMap.congr_fun hx0 ⟨b 0 v, hbv⟩
    change x (b 0 v) = 0 at e1
    have e2 : (b 0 * x) v = (x * b 0) v := (LinearMap.congr_fun (hxb 0 x hx) v).symm
    show (b 0 * x) v = 0
    rw [e2]; exact e1
  have h3 := finrank_map_pre_le V1 a hV1inv
  have h4 := Submodule.finrank_mono hAsup
  have h5 := Submodule.finrank_add_le_finrank_add_finrank
    (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ)))
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map (LinearMap.mulLeft ℂ (b 0)))
  have eA := sub_finrank (Algebra.adjoin ℂ (Set.range a))
  have eA' := sub_finrank (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ))
  have hsum2 : finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      finrank ℂ (Algebra.adjoin ℂ (Set.range fun j : Fin l => a j.succ)) +
      finrank ℂ (Algebra.adjoin ℂ (Set.range fun j => rs V1 (a j) (hV1inv j))) := by
    omega
  have hA' := hP V (fun j : Fin l => a j.succ) (fun i j => ha i.succ j.succ)
  rw [hn] at hA'
  exact arith_local t c n (finrank ℂ L) (finrank ℂ V1) _ _ _ hdim hI hsum2 hA'
    (fun hm => IH _ (by omega) V1 rfl (fun j => rs V1 (a j) (hV1inv j)) (rs_comm V1 a ha hV1inv))

theorem step (l t c : ℕ) (hP : Pl l (t * t) c) : Pl (l + 1) t c := by
  suffices H : ∀ n : ℕ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = n → ∀ (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, a i * a j = a j * a i) →
      t * finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ n ^ 2 + c * n by
    intro V _ _ _ a ha
    exact H _ V rfl a ha
  intro n
  refine Nat.strong_induction_on n ?_
  intro n IH V _ _ _ hn a ha
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h := finrank_sub_le_sq (Algebra.adjoin ℂ (Set.range a))
    rw [hn] at h
    have : finrank ℂ (Algebra.adjoin ℂ (Set.range a)) = 0 := by omega
    rw [this]; simp
  haveI : Nontrivial V := Module.finrank_pos_iff.1 (show 0 < finrank ℂ V by omega)
  choose μ hμ using fun i => Module.End.exists_eigenvalue (a i)
  let b : Fin (l + 1) → Module.End ℂ V := fun i => a i - algebraMap ℂ (Module.End ℂ V) (μ i)
  have hb : ∀ i, b i = a i - algebraMap ℂ (Module.End ℂ V) (μ i) := fun i => rfl
  have hamem : ∀ i, a i ∈ Algebra.adjoin ℂ (Set.range a) := fun i => Algebra.subset_adjoin (Set.mem_range_self i)
  have hbmem : ∀ i, b i ∈ Algebra.adjoin ℂ (Set.range a) :=
    fun i => sub_mem (hamem i) (Subalgebra.algebraMap_mem _ _)
  have hab : ∀ i j, a j * b i = b i * a j := by
    intro i j; rw [hb, mul_sub, sub_mul, ha j i, Algebra.commutes]
  have hxa : ∀ i, ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * a i = a i * x :=
    fun i x hx => comm_of_mem a (a i) (fun j => ha j i) hx
  have hxb : ∀ i, ∀ x ∈ Algebra.adjoin ℂ (Set.range a), x * b i = b i * x :=
    fun i x hx => comm_of_mem a (b i) (fun j => hab i j) hx
  have hbb : ∀ i j, b i * b j = b j * b i := fun i j => hxb j (b i) (hbmem i)
  have hfit : ∀ i, ∃ N : ℕ, IsCompl (LinearMap.ker (b i ^ N)) (LinearMap.range (b i ^ N)) ∧ 1 ≤ N := by
    intro i
    first
    | exact ((LinearMap.eventually_isCompl_ker_pow_range_pow (b i)).and
        (Filter.eventually_ge_atTop 1)).exists
    | exact ((Module.End.eventually_isCompl_ker_pow_range_pow (b i)).and
        (Filter.eventually_ge_atTop 1)).exists
  choose N hN using hfit
  by_cases hs : ∃ i, LinearMap.range (b i ^ N i) ≠ ⊥
  · exact split_case l t c n IH V hn a ha μ hμ N hN hs
  · exact local_case l t c hP n IH V hn a ha μ N hs

theorem allP : ∀ l t : ℕ, ∃ c, Pl l t c := by
  intro l
  induction l with
  | zero => intro t; exact ⟨t, base t⟩
  | succ l ih => intro t; obtain ⟨c, hc⟩ := ih (t * t); exact ⟨c, step l t c hc⟩

end DiscreteGroups.sglob.LConv.Comm

namespace DiscreteGroups.sglob.LConv

theorem commBound : CommBound := by
  intro l t
  obtain ⟨c, hc⟩ := Comm.allP l t
  exact ⟨c, hc⟩

end DiscreteGroups.sglob.LConv
