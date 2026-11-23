import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {k K : Type} [Field k] [Field K] [Algebra k K]

private theorem rank_eq_of_scalar_extension_data {H H' : Type} [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module K H']
    (ι : H →+ H') (hι : ∀ (a : k) h, ι (a • h) = algebraMap k K a • ι h)
    (π : (K →ₗ[k] k) → H' →+ H) (hπ : ∀ l c h, π l (c • ι h) = l c • h)
    (hs : Submodule.span K (Set.range ι) = ⊤) : Module.rank K H' = Module.rank k H := by
  classical
  let e := Module.Free.chooseBasis k H
  have hli : LinearIndependent K (fun j => ι (e j)) := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro l
    have h1 := congrArg (π l) hc
    rw [map_sum, map_zero] at h1
    simp only [hπ] at h1
    exact linearIndependent_iff'.1 e.linearIndependent s (fun j => l (c j)) h1 j hj
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun j => ι (e j)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    have hh : h ∈ Submodule.span k (Set.range e) := by rw [e.span_eq]; trivial
    induction hh using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [hι]; exact Submodule.smul_mem _ _ hx
  rw [← (Module.Basis.mk hli hsp).mk_eq_rank'', ← e.mk_eq_rank'']

variable {W : Type} [AddCommGroup W] [Module k W]

private noncomputable def n4p (l : K →ₗ[k] k) : K ⊗[k] W →ₗ[k] W :=
  (TensorProduct.lid k W).toLinearMap ∘ₗ l.rTensor W

@[simp] private theorem tensor_proj_tmul (l : K →ₗ[k] k) (c : K) (x : W) : n4p l (c ⊗ₜ[k] x) = l c • x := by
  simp [n4p]

private theorem tensor_proj_smul_one_tmul (l : K →ₗ[k] k) (c : K) (x : W) : n4p l (c • ((1 : K) ⊗ₜ[k] x)) = l c • x := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, tensor_proj_tmul]

private theorem tensor_proj_baseChange_map (l : K →ₗ[k] k) (f : W →ₗ[k] W) (x : K ⊗[k] W) :
    n4p l (f.baseChange K x) = f (n4p l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simp
  | add x y hx hy => simp [hx, hy]

private theorem tensor_proj_mem_of_mem_baseChange (l : K →ₗ[k] k) (b : Submodule k W) (x : K ⊗[k] W) (hx : x ∈ b.baseChange K) :
    n4p l x ∈ b := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simpa using b.smul_mem _ x.2
  | add x y hx hy => simpa using add_mem hx hy

private theorem baseChange_eq_sum_coord_basis {I : Type} (e : Module.Basis I k K) (x : K ⊗[k] W) :
    ∃ s : Finset I, ∀ t : Finset I, s ⊆ t → x = ∑ i ∈ t, e i • ((1 : K) ⊗ₜ[k] n4p (e.coord i) x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun t _ => by simp⟩
  | tmul c x =>
    refine ⟨(e.repr c).support, fun t ht => ?_⟩
    have h1 : c = ∑ i ∈ t, e.repr c i • e i := by
      conv_lhs => rw [← e.linearCombination_repr c, Finsupp.linearCombination_apply]
      exact Finsupp.sum_of_support_subset _ ht _ (fun _ _ => by simp)
    conv_lhs => rw [h1]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tensor_proj_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun t ht => ?_⟩
    conv_lhs => rw [hs t (Finset.subset_union_left.trans ht), hs' t (Finset.subset_union_right.trans ht)]
    simp [← Finset.sum_add_distrib, TensorProduct.tmul_add]

variable {G V : Type}

variable (K) in
private noncomputable def n4i : ((G → W) × (V → W)) →+ ((G → K ⊗[k] W) × (V → K ⊗[k] W)) where
  toFun y := (fun g => (1 : K) ⊗ₜ y.1 g, fun v => (1 : K) ⊗ₜ y.2 v)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [TensorProduct.tmul_add]

private noncomputable def n4q (l : K →ₗ[k] k) : ((G → K ⊗[k] W) × (V → K ⊗[k] W)) →+ ((G → W) × (V → W)) where
  toFun y := (fun g => n4p l (y.1 g), fun v => n4p l (y.2 v))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private theorem inclusion_smul_algebraMap (a : k) (y : (G → W) × (V → W)) :
    n4i (k := k) K (a • y) = algebraMap k K a • n4i (k := k) K y := by
  ext <;> simp [n4i]

private theorem descend_smul_inclusion (l : K →ₗ[k] k) (c : K) (y : (G → W) × (V → W)) :
    n4q l (c • n4i (k := k) K y) = l c • y := by
  ext <;> simp [n4i, n4q, tensor_proj_smul_one_tmul]

variable [Group G] [TopologicalSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G)
  (ρ : Representation k G W) (b : V → Submodule k W) (ρ' : Representation K G (K ⊗[k] W))
  (hρ : ∀ g, ρ' g = (ρ g).baseChange K)

include hρ

private theorem inclusion_cocycle_mem_Z1 (y) (hy : y ∈ Z1C loc ρ b) :
    n4i (k := k) K y ∈ Z1C loc ρ' (fun v => (b v).baseChange K) := by
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.comp (fun x => (1 : K) ⊗ₜ[k] x), fun s t => ?_, fun v s => ?_⟩
  · simp [n4i, hρ, h2, TensorProduct.tmul_add]
  · have := Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v s)
    simpa [n4i, hρ, TensorProduct.tmul_sub] using this

private theorem descend_cocycle_mem_Z1 (l : K →ₗ[k] k) (y) (hy : y ∈ Z1C loc ρ' (fun v => (b v).baseChange K)) :
    n4q l y ∈ Z1C loc ρ b := by
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.comp (n4p l), fun s t => ?_, fun v s => ?_⟩
  · simp [n4q, hρ, h2, tensor_proj_baseChange_map]
  · have := tensor_proj_mem_of_mem_baseChange l _ _ (h3 v s)
    simpa [n4q, hρ, tensor_proj_baseChange_map] using this

omit [TopologicalSpace G] in
private theorem inclusion_coboundary_mem_B1 (y) (hy : y ∈ continuousCoboundaries1 ρ b) :
    n4i (k := k) K y ∈ continuousCoboundaries1 ρ' (fun v => (b v).baseChange K) := by
  obtain ⟨X, h2, h3⟩ := hy
  refine ⟨1 ⊗ₜ X, fun s => ?_, fun v => ?_⟩
  · simp [n4i, hρ, h2, TensorProduct.tmul_sub]
  · have := Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v)
    simpa [n4i, TensorProduct.tmul_sub] using this

omit [TopologicalSpace G] in
private theorem descend_coboundary_mem_B1 (l : K →ₗ[k] k) (y) (hy : y ∈ continuousCoboundaries1 ρ' (fun v => (b v).baseChange K)) :
    n4q l y ∈ continuousCoboundaries1 ρ b := by
  obtain ⟨X, h2, h3⟩ := hy
  refine ⟨n4p l X, fun s => ?_, fun v => ?_⟩
  · simp [n4q, hρ, h2, tensor_proj_baseChange_map]
  · have := tensor_proj_mem_of_mem_baseChange l _ _ (h3 v)
    simpa [n4q] using this

private theorem cocycles_baseChange_eq_span [CompactSpace G] [Finite V] :
    Z1C loc ρ' (fun v => (b v).baseChange K) =
      Submodule.span K (n4i (k := k) K '' (Z1C loc ρ b : Set ((G → W) × (V → W)))) := by
  classical
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · let e := Module.Free.chooseBasis k K
    choose s hs using fun x : K ⊗[k] W => baseChange_eq_sum_coord_basis e x
    have hf : (Set.range y.1 ∪ Set.range y.2).Finite := hy.1.range_finite.union (Set.finite_range _)
    have hy' : y = ∑ i ∈ hf.toFinset.biUnion s, e i • n4i (k := k) K (n4q (e.coord i) y) := by
      ext g
      · rw [Prod.fst_sum, Finset.sum_apply]
        exact hs _ _ (Finset.subset_biUnion_of_mem s (by simp))
      · rw [Prod.snd_sum, Finset.sum_apply]
        exact hs _ _ (Finset.subset_biUnion_of_mem s (by simp))
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, descend_cocycle_mem_Z1 loc ρ b ρ' hρ _ y hy, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    exact inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ y hy

private theorem rank_H1_baseChange_eq [CompactSpace G] [Finite V] :
    Module.rank K (H1C loc ρ' fun v => (b v).baseChange K) = Module.rank k (H1C loc ρ b) := by
  let i0 : Z1C loc ρ b →+ Z1C loc ρ' (fun v => (b v).baseChange K) :=
    { toFun := fun y => ⟨n4i (k := k) K y.1, inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ _ y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  let q0 (l : K →ₗ[k] k) : Z1C loc ρ' (fun v => (b v).baseChange K) →+ Z1C loc ρ b :=
    { toFun := fun y => ⟨n4q l y.1, descend_cocycle_mem_Z1 loc ρ b ρ' hρ l _ y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  let i1 : H1C loc ρ b →+ H1C loc ρ' (fun v => (b v).baseChange K) :=
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) i0
      (fun y hy => inclusion_coboundary_mem_B1 ρ b ρ' hρ _ hy)
  let q1 (l : K →ₗ[k] k) : H1C loc ρ' (fun v => (b v).baseChange K) →+ H1C loc ρ b :=
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) (q0 l)
      (fun y hy => descend_coboundary_mem_B1 ρ b ρ' hρ l _ hy)
  have hi : ∀ y, i1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (i0 y) := fun _ => rfl
  have hq : ∀ l y, q1 l (Submodule.Quotient.mk y) = Submodule.Quotient.mk (q0 l y) := fun _ _ => rfl
  refine rank_eq_of_scalar_extension_data i1 (fun a h => ?_) q1 (fun l c h => ?_) ?_
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [← Submodule.Quotient.mk_smul, hi, hi, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (inclusion_smul_algebraMap a y.1)
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [hi, ← Submodule.Quotient.mk_smul, hq, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (descend_smul_inclusion l c y.1)
  · rw [eq_top_iff]
    intro h hT
    clear hT
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    have hy' := hy
    rw [cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hy'
    revert hy
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      intro hy
      exact Submodule.subset_span ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩
    | zero => intro hy; exact zero_mem _
    | add x y hx' hy' hx hy =>
      intro _
      rw [← cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hx' hy'
      exact add_mem (hx hx') (hy hy')
    | smul a x hx' hx =>
      intro _
      rw [← cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hx'
      exact Submodule.smul_mem _ a (hx hx')

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.n4 :
    ∀ {k K G W V : Type} [Field k] [Field K] [Algebra k K] [Group G] [TopologicalSpace G] [CompactSpace G] [AddCommGroup W] [Module k W] [Module.Finite k W] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b : V → Submodule k W) (ρ' : Representation K G (TensorProduct k K W)), (∀ g, ρ' g = (ρ g).baseChange K) → Z1C loc ρ' (fun v => (b v).baseChange K) = Submodule.span K ((fun y : (G → W) × (V → W) => (fun g => (1 : K) ⊗ₜ y.1 g, fun v => (1 : K) ⊗ₜ y.2 v)) '' (Z1C loc ρ b : Set ((G → W) × (V → W)))) ∧ Module.rank K (H1C loc ρ' fun v => (b v).baseChange K) = Module.rank k (H1C loc ρ b) := by
  intro k K G W V _ _ _ _ _ _ _ _ _ Gv _ _ loc ρ b ρ' hρ
  exact ⟨cocycles_baseChange_eq_span loc ρ b ρ' hρ, rank_H1_baseChange_eq loc ρ b ρ' hρ⟩
