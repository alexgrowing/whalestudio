import Mathlib

noncomputable section

namespace Formalism.L2.G.Cmp

variable {LL Kf : Type*} [Field LL] [Field Kf] {e : LL →+* Kf}
  {V0 V1 W0 W1 ι : Type*} [AddCommGroup V0] [Module LL V0] [AddCommGroup V1] [Module LL V1]
  [AddCommGroup W0] [Module Kf W0] [AddCommGroup W1] [Module Kf W1]

def spanK (c0 : V0 →ₛₗ[e] W0) : Submodule Kf W0 := Submodule.span Kf (Set.range c0)

theorem mem_spanK (c0 : V0 →ₛₗ[e] W0) (x : V0) : c0 x ∈ spanK c0 := Submodule.subset_span ⟨x, rfl⟩

private theorem lc_repr_lemma (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0) (x : V0) :
    Finsupp.linearCombination Kf (fun i => c0 (b i)) (Finsupp.mapRange e (map_zero e) (b.repr x)) = c0 x := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (h := fun i a => a • c0 (b i)) (fun i => zero_smul _ _)]
  conv_rhs => rw [← b.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, LinearMap.map_smulₛₗ]

theorem span_basis_eq (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0) :
    Submodule.span Kf (Set.range fun i => c0 (b i)) = spanK c0 := by
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨b i, rfl⟩)
  · rw [spanK, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [← lc_repr_lemma c0 b x, ← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ _

theorem inj_of_li (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) : Function.Injective c0 := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 := linearIndependent_iff.1 hli _ ((lc_repr_lemma c0 b x).trans hx)
  have h2 : b.repr x = 0 := by
    ext i
    have h3 := DFunLike.congr_fun h1 i
    simpa using h3
  exact b.repr.map_eq_zero_iff.1 h2

def complK (c0 : V0 →ₛₗ[e] W0) : Submodule Kf W0 := Classical.choose (Submodule.exists_isCompl (spanK c0))

theorem isCompl_complK (c0 : V0 →ₛₗ[e] W0) : IsCompl (spanK c0) (complK c0) := Classical.choose_spec (Submodule.exists_isCompl (spanK c0))

def extSpan (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) :
    Submodule.span Kf (Set.range fun i => c0 (b i)) →ₗ[Kf] W1 :=
  (Finsupp.linearCombination Kf fun i => c1 (KL (b i))) ∘ₗ hli.repr

def extK (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) : W0 →ₗ[Kf] W1 :=
  (extSpan c0 c1 b hli KL) ∘ₗ
    (LinearEquiv.ofEq _ _ (span_basis_eq c0 b).symm).toLinearMap ∘ₗ
      Submodule.projectionOnto (spanK c0) (complK c0) (isCompl_complK c0)

theorem extK_basis (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (i : ι) :
    extK c0 c1 b hli KL (c0 (b i)) = c1 (KL (b i)) := by
  have hm : c0 (b i) ∈ spanK c0 := mem_spanK c0 (b i)
  have hp := Submodule.projectionOnto_apply_left (isCompl_complK c0) ⟨c0 (b i), hm⟩
  dsimp only at hp
  simp only [extK, LinearMap.comp_apply]
  rw [hp]
  have e2 : (LinearEquiv.ofEq _ _ (span_basis_eq c0 b).symm) (⟨c0 (b i), hm⟩ : spanK c0) =
      ⟨c0 (b i), Submodule.subset_span ⟨i, rfl⟩⟩ := Subtype.ext rfl
  rw [LinearEquiv.coe_toLinearMap, e2]
  simp only [extSpan, LinearMap.comp_apply]
  rw [hli.repr_eq_single i _ rfl]
  simp

theorem extK_apply (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (x : V0) :
    extK c0 c1 b hli KL (c0 x) = c1 (KL x) := by
  have e1 : ⇑(extK c0 c1 b hli KL) ∘ (fun i => c0 (b i)) = fun i => c1 (KL (b i)) :=
    funext fun i => extK_basis c0 c1 b hli KL i
  rw [← lc_repr_lemma c0 b x, Finsupp.apply_linearCombination, e1]
  exact lc_repr_lemma (c1.comp KL) b x

theorem extK_unique (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (g : W0 →ₗ[Kf] W1)
    (hg : ∀ x, g (c0 x) = c1 (KL x)) (y : W0) (hy : y ∈ spanK c0) : g y = extK c0 c1 b hli KL y := by
  unfold spanK at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    rw [hg, extK_apply]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul a y _ hy => rw [map_smul, map_smul, hy]

theorem extK_mem_spanK (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (y : W0) :
    extK c0 c1 b hli KL y ∈ spanK c1 := by
  have h1 : extK c0 c1 b hli KL y ∈ LinearMap.range (Finsupp.linearCombination Kf fun i => c1 (KL (b i))) :=
    LinearMap.mem_range.2 ⟨_, rfl⟩
  rw [Finsupp.range_linearCombination] at h1
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨KL (b i), rfl⟩) h1

section Indep

open TensorProduct

variable {ι' : Type*}

private theorem li_core_lemma_2 {κ : Type*} (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (v : κ → V0) (hv : LinearIndependent LL v) :
    LinearIndependent Kf fun k => c0 (v k) := by
  classical
  rw [linearIndependent_iff']
  intro s g hs k hk
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Finsupp.lapply k) ∘ₗ hv.repr)
  let c1 : LL →ₛₗ[e] Kf := { toFun := e, map_add' := e.map_add, map_smul' := fun a x => e.map_mul a x }
  have hφv : ∀ i, φ (v i) = if i = k then 1 else 0 := by
    intro i
    have h1 := LinearMap.congr_fun hφ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.lapply_apply] at h1
    rw [h1, hv.repr_eq_single i _ rfl, Finsupp.single_apply]
  have h2 := congrArg (extK c0 c1 b hli φ) hs
  rw [map_sum, map_zero] at h2
  simp only [map_smul, extK_apply] at h2
  rw [Finset.sum_eq_single k (fun i _ hik => by rw [hφv, if_neg hik]; simp [c1])
    (fun h => absurd hk h), hφv, if_pos rfl] at h2
  simpa [c1] using h2

theorem li_basis (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (b' : Module.Basis ι' LL V0) :
    LinearIndependent Kf fun i => c0 (b' i) := by
  exact li_core_lemma_2 c0 b hli b' b'.linearIndependent

theorem li_of_li {κ : Type*} (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (v : κ → V0) (hv : LinearIndependent LL v) :
    LinearIndependent Kf fun k => c0 (v k) := by
  exact li_core_lemma_2 c0 b hli v hv

end Indep

section Rat

variable {Cc : Type*} [Field Cc] {s : LL →+* Cc} {M0 M1 : Type*} [AddCommGroup M0] [Module Cc M0]
  [AddCommGroup M1] [Module Cc M1]

def ratDom (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (f : M0 →ₗ[Cc] M1) : Submodule LL V0 where
  carrier := {x | ∃ y, e1 y = f (e0 x)}
  add_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, by rw [map_add, map_add, map_add, hy, hz]⟩
  zero_mem' := ⟨0, by rw [map_zero, map_zero, map_zero]⟩
  smul_mem' := by
    rintro a x ⟨y, hy⟩
    exact ⟨a • y, by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, hy]⟩

theorem mem_ratDom (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (f : M0 →ₗ[Cc] M1) (x : V0) :
    x ∈ ratDom e0 e1 f ↔ ∃ y, e1 y = f (e0 x) := Iff.rfl

def ratPart (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (hinj : Function.Injective e1) (f : M0 →ₗ[Cc] M1) :
    ratDom e0 e1 f →ₗ[LL] V1 where
  toFun x := Classical.choose x.2
  map_add' x y := by
    apply hinj
    rw [map_add, Classical.choose_spec x.2, Classical.choose_spec y.2, Classical.choose_spec (x + y).2]
    rw [Submodule.coe_add, map_add, map_add]
  map_smul' a x := by
    apply hinj
    rw [RingHom.id_apply, LinearMap.map_smulₛₗ, Classical.choose_spec x.2, Classical.choose_spec (a • x).2]
    rw [Submodule.coe_smul, LinearMap.map_smulₛₗ, map_smul]

theorem ratPart_spec (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (hinj : Function.Injective e1) (f : M0 →ₗ[Cc] M1)
    (x : ratDom e0 e1 f) : e1 (ratPart e0 e1 hinj f x) = f (e0 x) := Classical.choose_spec x.2

def ratCompl (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (f : M0 →ₗ[Cc] M1) : Submodule LL V0 :=
  Classical.choose (Submodule.exists_isCompl (ratDom e0 e1 f))

theorem isCompl_ratCompl (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (f : M0 →ₗ[Cc] M1) :
    IsCompl (ratDom e0 e1 f) (ratCompl e0 e1 f) := Classical.choose_spec (Submodule.exists_isCompl (ratDom e0 e1 f))

def ratMap (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (hinj : Function.Injective e1) (f : M0 →ₗ[Cc] M1) :
    V0 →ₗ[LL] V1 :=
  ratPart e0 e1 hinj f ∘ₗ
    Submodule.projectionOnto (ratDom e0 e1 f) (ratCompl e0 e1 f) (isCompl_ratCompl e0 e1 f)

theorem ratMap_eq (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (hinj : Function.Injective e1) (f : M0 →ₗ[Cc] M1)
    (x : V0) (y : V1) (h : e1 y = f (e0 x)) : ratMap e0 e1 hinj f x = y := by
  have hx : x ∈ ratDom e0 e1 f := (mem_ratDom e0 e1 f x).2 ⟨y, h⟩
  apply hinj
  have hp := Submodule.projectionOnto_apply_left (isCompl_ratCompl e0 e1 f) ⟨x, hx⟩
  dsimp only at hp
  simp only [ratMap, LinearMap.comp_apply]
  rw [hp, ratPart_spec]
  exact h.symm

theorem ratMap_spec (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (hinj : Function.Injective e1) (f : M0 →ₗ[Cc] M1)
    (h : ∀ x, ∃ y, e1 y = f (e0 x)) (x : V0) : e1 (ratMap e0 e1 hinj f x) = f (e0 x) := by
  obtain ⟨y, hy⟩ := h x
  rw [ratMap_eq e0 e1 hinj f x y hy]
  exact hy

end Rat

end Formalism.L2.G.Cmp

end
