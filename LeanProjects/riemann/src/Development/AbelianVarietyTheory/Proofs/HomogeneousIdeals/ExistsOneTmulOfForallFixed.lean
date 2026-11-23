import Mathlib

open TensorProduct Module

namespace GlobalTheory.GaloisDescent

section Basis

variable {K L M G ι : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module L M]

theorem repr_apply_of_semilinear (s : L →+* L) (b : Basis ι L M) (φ : M →+ M)
    (hφ : ∀ a i, φ (a • b i) = s a • b i) (w : M) (i : ι) :
    b.repr (φ w) i = s (b.repr w i) := by
  classical
  conv_lhs => rw [← b.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_sum]
  simp only [hφ, map_smul, Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.1 h, map_zero]

theorem exists_rational_support_subset (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (b : Basis ι L M) (φ : G → M →+ M) (hφ : ∀ g a i, φ g (a • b i) = s g a • b i)
    (W : Submodule L M) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) (w : M) (hw : w ∈ W) (h0 : w ≠ 0) :
    ∃ u ∈ W, (∀ i, b.repr u i ∈ Set.range (algebraMap K L)) ∧
      (b.repr u).support ⊆ (b.repr w).support ∧ ∃ i, b.repr u i = 1 := by
  classical
  induction h : (b.repr w).support.card using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    obtain ⟨i, hi⟩ : ∃ i, b.repr w i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 (b.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
    set w' := (b.repr w i)⁻¹ • w with hw'
    have hw'W : w' ∈ W := W.smul_mem _ hw
    have hrep : ∀ j, b.repr w' j = (b.repr w i)⁻¹ * b.repr w j := fun j => by simp [hw']
    have hi' : b.repr w' i = 1 := by rw [hrep, inv_mul_cancel₀ hi]
    have hsub : (b.repr w').support ⊆ (b.repr w).support := fun j hj => by
      rw [Finsupp.mem_support_iff] at hj ⊢
      intro hj0
      exact hj (by rw [hrep, hj0, mul_zero])
    by_cases hfix : ∀ g, φ g w' = w'
    · refine ⟨w', hw'W, fun j => hs _ fun g => ?_, hsub, i, hi'⟩
      rw [← repr_apply_of_semilinear (s g) b (φ g) (hφ g), hfix]
    · push Not at hfix
      obtain ⟨g, hg⟩ := hfix
      have hd : (b.repr (φ g w' - w')).support ⊆ (b.repr w).support.erase i := fun j hj => by
        rw [Finsupp.mem_support_iff, map_sub, Finsupp.sub_apply,
          repr_apply_of_semilinear (s g) b (φ g) (hφ g)] at hj
        rw [Finset.mem_erase, Finsupp.mem_support_iff]
        constructor
        · rintro rfl
          exact hj (by rw [hi', map_one, sub_self])
        · intro hj0
          exact hj (by rw [hrep, hj0, mul_zero, map_zero, sub_self])
      have hlt : (b.repr (φ g w' - w')).support.card < n := by
        rw [← h]
        exact (Finset.card_le_card hd).trans_lt
          (Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.2 hi))
      obtain ⟨u, hu, hur, hus, hui⟩ := ih _ hlt (φ g w' - w') (W.sub_mem (hW g _ hw'W) hw'W)
        (sub_ne_zero.2 hg) rfl
      exact ⟨u, hu, hur, hus.trans (hd.trans (Finset.erase_subset _ _)), hui⟩

theorem span_rational_eq (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (b : Basis ι L M) (φ : G → M →+ M) (hφ : ∀ g a i, φ g (a • b i) = s g a • b i)
    (W : Submodule L M) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) :
    Submodule.span L {u | u ∈ W ∧ ∀ i, b.repr u i ∈ Set.range (algebraMap K L)} = W := by
  classical
  refine le_antisymm (Submodule.span_le.2 fun u hu => hu.1) fun w hw => ?_
  induction h : (b.repr w).support.card using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases h0 : w = 0
    · rw [h0]; exact Submodule.zero_mem _
    obtain ⟨u, hu, hur, hus, i, hi⟩ := exists_rational_support_subset s hs b φ hφ W hW w hw h0
    have hiw : i ∈ (b.repr w).support := hus (Finsupp.mem_support_iff.2 (by simp [hi]))
    have hd : (b.repr (w - b.repr w i • u)).support ⊆ (b.repr w).support.erase i := fun j hj => by
      rw [Finsupp.mem_support_iff, map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply,
        smul_eq_mul] at hj
      rw [Finset.mem_erase]
      constructor
      · rintro rfl
        exact hj (by rw [hi, mul_one, sub_self])
      · by_contra hj0
        have h1 : b.repr u j = 0 := Finsupp.notMem_support_iff.1 fun h => hj0 (hus h)
        exact hj (by rw [h1, Finsupp.notMem_support_iff.1 hj0, mul_zero, sub_self])
    have hlt : (b.repr (w - b.repr w i • u)).support.card < n := by
      rw [← h]
      exact (Finset.card_le_card hd).trans_lt (Finset.card_erase_lt_of_mem hiw)
    have h1 := ih _ hlt _ (W.sub_mem hw (W.smul_mem _ hu)) rfl
    have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ (b.repr w i)
      (Submodule.subset_span (R := L) (s := {u | u ∈ W ∧
        ∀ i, b.repr u i ∈ Set.range (algebraMap K L)}) ⟨hu, hur⟩))
    rwa [sub_add_cancel] at h2

end Basis

section IsBaseChange

variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}

theorem mem_range_of_repr_mem_range (hf : IsBaseChange L f) {ι : Type*} (b : Basis ι K V) (u : M)
    (hu : ∀ i, (hf.basis b).repr u i ∈ Set.range (algebraMap K L)) : u ∈ LinearMap.range f := by
  classical
  choose k hk using hu
  rw [← (hf.basis b).linearCombination_repr u, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← hk, algebraMap_smul, hf.basis_apply]
  exact Submodule.smul_mem _ _ ⟨_, rfl⟩

theorem span_image_comap_eq (hf : IsBaseChange L f) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → M →+ M) (hφ : ∀ g a v, φ g (a • f v) = s g a • f v)
    (W : Submodule L M) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) :
    Submodule.span L (f '' (W.restrictScalars K).comap f) = W := by
  let b := Basis.ofVectorSpace K V
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact hv
  · conv_lhs => rw [← span_rational_eq s hs (hf.basis b) φ
      (fun g a i => by rw [hf.basis_apply, hφ]) W hW]
    refine Submodule.span_mono fun u hu => ?_
    obtain ⟨v, rfl⟩ := mem_range_of_repr_mem_range hf b u hu.2
    exact ⟨v, hu.1, rfl⟩

noncomputable def contract (hf : IsBaseChange L f) (l : L →ₗ[K] K) : M →ₗ[K] V :=
  (TensorProduct.lid K V).toLinearMap ∘ₗ l.rTensor V ∘ₗ
    (hf.equiv.symm.toLinearMap.restrictScalars K)

@[simp]
theorem contract_smul (hf : IsBaseChange L f) (l : L →ₗ[K] K) (a : L) (v : V) :
    contract hf l (a • f v) = l a • v := by
  simp [contract, hf.equiv_symm_apply, smul_tmul']

theorem induction_smul (hf : IsBaseChange L f) {p : M → Prop} (x : M) (h0 : p 0)
    (hs : ∀ (a : L) (v : V), p (a • f v)) (ha : ∀ x y, p x → p y → p (x + y)) : p x := by
  obtain ⟨t, rfl⟩ := hf.equiv.surjective x
  induction t with
  | zero => rwa [map_zero]
  | tmul a v => rw [hf.equiv_tmul]; exact hs a v
  | add x y hx hy => rw [map_add]; exact ha _ _ hx hy

theorem contract_smul_left (hf : IsBaseChange L f) (l : L →ₗ[K] K) (a : L) (x : M) :
    contract hf l (a • x) = contract hf (l ∘ₗ LinearMap.mulLeft K a) x := by
  refine induction_smul hf (p := fun x =>
    contract hf l (a • x) = contract hf (l ∘ₗ LinearMap.mulLeft K a) x) x (by simp) ?_ ?_
  · intro c v
    rw [smul_smul, contract_smul, contract_smul]
    rfl
  · intro x y hx hy
    rw [smul_add, map_add, map_add, hx, hy]

theorem exists_finsupp_contract (hf : IsBaseChange L f) {ι : Type*} (e : Basis ι K L) (x : M) :
    ∃ c : ι →₀ V, (∀ i, c i = contract hf (e.coord i) x) ∧ x = c.sum fun i v => e i • f v := by
  refine induction_smul hf (p := fun x => ∃ c : ι →₀ V,
    (∀ i, c i = contract hf (e.coord i) x) ∧ x = c.sum fun i v => e i • f v) x
    ⟨0, by simp, by simp⟩ ?_ ?_
  · intro a v
    refine ⟨(e.repr a).mapRange (· • v) (zero_smul _ _), fun i => by simp, ?_⟩
    rw [Finsupp.sum_mapRange_index (by simp)]
    conv_lhs => rw [← e.linearCombination_repr a, Finsupp.linearCombination_apply, Finsupp.sum,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    beta_reduce
    rw [map_smul, smul_assoc, smul_comm]
  · rintro x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩
    refine ⟨c + d, fun i => ?_, ?_⟩
    · rw [map_add, ← hc, ← hd, Finsupp.add_apply]
    · rw [Finsupp.sum_add_index' (by simp) (by simp), ← hx, ← hy]

theorem mem_span_image_iff (hf : IsBaseChange L f) (N : Submodule K V) (x : M) :
    x ∈ Submodule.span L (f '' N) ↔ ∀ l : L →ₗ[K] K, contract hf l x ∈ N := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      intro l
      rw [← one_smul L (f v), contract_smul]
      exact N.smul_mem _ hv
    | zero => simp
    | add x y _ _ hx hy => intro l; rw [map_add]; exact N.add_mem (hx l) (hy l)
    | smul a x _ hx => intro l; rw [contract_smul_left]; exact hx _
  · intro hx
    obtain ⟨c, hc, h⟩ := exists_finsupp_contract hf (Basis.ofVectorSpace K L) x
    rw [h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, by rw [hc]; exact hx _, rfl⟩)

theorem comap_span_image (hf : IsBaseChange L f) (N : Submodule K V) :
    ((Submodule.span L (f '' N)).restrictScalars K).comap f = N := by
  refine le_antisymm (fun v hv => ?_) fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero (α := L))
  have := (mem_span_image_iff hf N _).1 hv l
  rwa [← one_smul L (f v), contract_smul, hl, one_smul] at this

theorem span_image_injective (hf : IsBaseChange L f) :
    Function.Injective fun N : Submodule K V => Submodule.span L (f '' N) := fun N N' h => by
  rw [← comap_span_image hf N, ← comap_span_image hf N']
  exact congrArg (fun W : Submodule L M => (W.restrictScalars K).comap f) h

theorem span_image_iInf (hf : IsBaseChange L f) {J : Sort*} (N : J → Submodule K V) :
    Submodule.span L (f '' (⨅ j, N j : Submodule K V)) = ⨅ j, Submodule.span L (f '' N j) := by
  ext x
  simp only [mem_span_image_iff hf, Submodule.mem_iInf]
  exact forall_comm

section Maps

variable {V' M' : Type*} [AddCommGroup V'] [Module K V']
  [AddCommGroup M'] [Module K M'] [Module L M'] [IsScalarTower K L M'] {f' : V' →ₗ[K] M'}

theorem contract_map (hf : IsBaseChange L f) (hf' : IsBaseChange L f') (p : V →ₗ[K] V')
    (F : M →ₗ[L] M') (hF : ∀ v, F (f v) = f' (p v)) (l : L →ₗ[K] K) (x : M) :
    contract hf' l (F x) = p (contract hf l x) := by
  refine induction_smul hf (p := fun x => contract hf' l (F x) = p (contract hf l x)) x
    (by simp) ?_ ?_
  · intro a v
    rw [map_smul, hF, contract_smul, contract_smul, map_smul]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem span_image_comap_map (hf : IsBaseChange L f) (hf' : IsBaseChange L f') (p : V →ₗ[K] V')
    (F : M →ₗ[L] M') (hF : ∀ v, F (f v) = f' (p v)) (N : Submodule K V') :
    Submodule.span L (f '' N.comap p) = (Submodule.span L (f' '' N)).comap F := by
  ext x
  simp only [mem_span_image_iff hf, Submodule.mem_comap, mem_span_image_iff hf',
    contract_map hf hf' p F hF]

theorem span_image_ker (hf : IsBaseChange L f) (hf' : IsBaseChange L f') (p : V →ₗ[K] V')
    (F : M →ₗ[L] M') (hF : ∀ v, F (f v) = f' (p v)) :
    Submodule.span L (f '' LinearMap.ker p) = LinearMap.ker F := by
  rw [← Submodule.comap_bot, span_image_comap_map hf hf' p F hF]
  simp

end Maps

end IsBaseChange

section Tensor

variable {K L V G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]

variable (K) in

def rationalPart (W : Submodule L (L ⊗[K] V)) : Submodule K V :=
  (W.restrictScalars K).comap (TensorProduct.mk K L V 1)

@[simp]
theorem mem_rationalPart {W : Submodule L (L ⊗[K] V)} {v : V} :
    v ∈ rationalPart K W ↔ (1 : L) ⊗ₜ[K] v ∈ W := Iff.rfl

theorem baseChange_eq_span_image (N : Submodule K V) :
    N.baseChange L = Submodule.span L (TensorProduct.mk K L V 1 '' N) :=
  Submodule.baseChange_eq_span L N

@[simp]
theorem rationalPart_baseChange (N : Submodule K V) : rationalPart K (N.baseChange L) = N := by
  rw [baseChange_eq_span_image]
  exact comap_span_image (TensorProduct.isBaseChange K V L) N

theorem baseChange_rationalPart (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (W : Submodule L (L ⊗[K] V)) (hW : ∀ g, ∀ w ∈ W, (s g).toLinearMap.rTensor V w ∈ W) :
    (rationalPart K W).baseChange L = W := by
  rw [baseChange_eq_span_image]
  exact span_image_comap_eq (TensorProduct.isBaseChange K V L) (fun g => (s g).toRingHom) hs
    (fun g => ((s g).toLinearMap.rTensor V).toAddMonoidHom)
    (fun g a v => by simp [smul_tmul']) W hW

theorem stable_iff_exists_baseChange (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (W : Submodule L (L ⊗[K] V)) :
    (∀ g, ∀ w ∈ W, (s g).toLinearMap.rTensor V w ∈ W) ↔
      ∃! N : Submodule K V, N.baseChange L = W := by
  constructor
  · intro hW
    refine ⟨_, baseChange_rationalPart s hs W hW, fun N hN => ?_⟩
    rw [← hN, rationalPart_baseChange]
  · rintro ⟨N, rfl, -⟩ g _ ⟨t, rfl⟩
    exact ⟨(s g).toLinearMap.rTensor N t, (LinearMap.rTensor_baseChange (s g) t N.subtype).symm⟩

end Tensor

end GlobalTheory.GaloisDescent
