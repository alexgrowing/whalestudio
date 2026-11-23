import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

open ReciprocityTheory.Gal UpperTheory.V.Base

namespace UpperTheory.V.Base.SelmerBaseEigenCoordinates

open TensorProduct

section Abstract

variable {R O ι : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype ι] (b : Module.Basis ι R O)
  {N N' : Type} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module O N']

private structure Coords (J : N →+ N') (C : ι → N' →+ N) : Prop where
  smul : ∀ (r : R) x, J (r • x) = algebraMap R O r • J x
  sum : ∀ y, ∑ i, b i • J (C i y) = y
  coord : ∀ i (o : O) x, C i (o • J x) = b.repr o i • x

variable {b} {J : N →+ N'} {C : ι → N' →+ N}

private theorem Coords.comm (h : Coords b J C) (f : N → N) (f' : N' →ₗ[O] N') (hf : ∀ x, J (f x) = f' (J x))
    (i : ι) (y : N') : C i (f' y) = f (C i y) := by
  conv_lhs => rw [← h.sum y]
  simp only [map_sum, LinearMap.map_smul, ← hf, h.coord, Module.Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    rw [Finsupp.single_eq_of_ne hk.symm, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem Coords.length [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] (h : Coords b J C) :
    Module.length O N' =
      Module.length R N * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  classical
  haveI : Module.Free R O := Module.Free.of_basis b
  let F : O →+ N →+ N' :=
    { toFun := fun o =>
        { toFun := fun x => o • J x
          map_zero' := by simp
          map_add' := fun x y => by simp [smul_add] }
      map_zero' := by ext; simp
      map_add' := fun o o' => by ext; simp [add_smul] }
  have hF : ∀ (r : R) (o : O) (x : N), F (r • o) x = F o (r • x) := by
    intro r o x
    show (r • o) • J x = o • J (r • x)
    rw [h.smul, smul_smul, Algebra.smul_def, mul_comm]
  let φ : O ⊗[R] N →+ N' := TensorProduct.liftAddHom F hF
  have hφ : ∀ (o : O) (x : N), φ (o ⊗ₜ[R] x) = o • J x := fun o x => by
    simp [φ, F, TensorProduct.liftAddHom_tmul]
  let ψ : N' → O ⊗[R] N := fun y => ∑ i, b i ⊗ₜ[R] C i y
  have hψφ : ∀ t, ψ (φ t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [ψ]
    | tmul o x =>
      simp only [ψ, hφ, h.coord]
      simp only [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
    | add s t hs ht =>
      simp only [ψ, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib] at hs ht ⊢
      rw [hs, ht]
  have hφψ : ∀ y, φ (ψ y) = y := by
    intro y
    simp only [ψ, map_sum, hφ, h.sum]
  have hφs : ∀ (o : O) t, φ (o • t) = o • φ t := by
    intro o t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul o' x => rw [TensorProduct.smul_tmul', hφ, hφ, smul_eq_mul, mul_smul]
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
  let e : N' ≃ₗ[O] O ⊗[R] N :=
    { toFun := ψ
      invFun := φ
      left_inv := hφψ
      right_inv := hψφ
      map_add' := fun y y' => by simp [ψ, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      map_smul' := fun o y => by
        show ψ (o • y) = o • ψ y
        conv_lhs => rw [← hφψ y, ← hφs, hψφ] }
  rw [e.length_eq, IsLocalRing.length_baseChange]

end Abstract

section Coh

variable {G : Type} [Group G] [TopologicalSpace G]
  {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
  {O M' : Type} [CommRing O] [AddCommGroup M'] [Module O M']
  [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M']
  (ρ : Representation R G M) (ρ' : Representation O G M') (u : M →+ M') (hu : ∀ g m, u (ρ g m) = ρ' g (u m))
  (U : Subgroup G)

private def zMap : Z1U ρ U →+ Z1U ρ' U where
  toFun f := ⟨u ∘ f.1, continuous_of_discreteTopology.comp f.2.1, fun g h => by
    simp only [Function.comp_apply, f.2.2 g h, map_add]
    exact congrArg _ (hu _ _)⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero u)
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)

private def hMap : H1U ρ U →+ H1U ρ' U :=
  QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) (zMap ρ ρ' u hu U) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    have e : f.1 g = ρ g m - m := hm g
    change u (f.1 g) = ρ' g (u m) - u m
    rw [e, map_sub, hu]

private theorem hMap_mk (z : Z1U ρ U) :
    hMap ρ ρ' u hu U (Submodule.Quotient.mk z) = Submodule.Quotient.mk (zMap ρ ρ' u hu U z) := rfl

end Coh

end UpperTheory.V.Base.SelmerBaseEigenCoordinates

private theorem UpperTheory.V.Base.exists_coords_of_isBaseChange {R O ι M M' : Type} [CommRing R] [CommRing O] [Algebra R O]
    [Fintype ι] (b : Module.Basis ι R O)
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M']
    (j : M →ₗ[R] M') (hj : IsBaseChange O j) :
    ∃ C : ι → M' →+ M, UpperTheory.V.Base.SelmerBaseEigenCoordinates.Coords b j.toAddMonoidHom C := by
  classical
  let F : ι → O →+ M →+ M := fun i =>
    { toFun := fun o =>
        { toFun := fun x => b.repr o i • x
          map_zero' := by simp
          map_add' := fun x y => by simp [smul_add] }
      map_zero' := by ext; simp
      map_add' := fun o o' => by ext; simp [add_smul] }
  have hF : ∀ i (r : R) (o : O) (x : M), F i (r • o) x = F i o (r • x) := by
    intro i r o x
    show b.repr (r • o) i • x = b.repr o i • r • x
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm, mul_smul]
  have hFt : ∀ i (o : O) (x : M), TensorProduct.liftAddHom (F i) (hF i) (o ⊗ₜ[R] x) = b.repr o i • x :=
    fun i o x => by simp [F, TensorProduct.liftAddHom_tmul]
  refine ⟨fun i => (TensorProduct.liftAddHom (F i) (hF i)).comp hj.equiv.symm.toLinearMap.toAddMonoidHom,
    ?_, ?_, ?_⟩
  · intro r x
    simp [algebraMap_smul]
  · intro y
    obtain ⟨t, rfl⟩ := hj.equiv.surjective y
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul o x =>
      simp only [hFt, IsBaseChange.equiv_tmul, map_smul]
      simp only [smul_comm (b _) (b.repr o _)]
      simp only [← smul_assoc, ← Finset.sum_smul, b.sum_repr]
    | add s t hs ht =>
      simp only [map_add, smul_add, Finset.sum_add_distrib, hs, ht]
  · intro i o x
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]
    rw [← IsBaseChange.equiv_tmul hj, LinearEquiv.symm_apply_apply, hFt]

private theorem UpperTheory.V.Base.coords_restrict_to_submodules {R O ι : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype ι]
    {b : Module.Basis ι R O} {N N' : Type} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module O N']
    {J : N →+ N'} {C : ι → N' →+ N} (h : UpperTheory.V.Base.SelmerBaseEigenCoordinates.Coords b J C)
    (P : Submodule R N) (P' : Submodule O N') (hJ : ∀ x ∈ P, J x ∈ P') (hC : ∀ i, ∀ y ∈ P', C i y ∈ P) :
    ∃ (J0 : P →+ P') (C0 : ι → P' →+ P), UpperTheory.V.Base.SelmerBaseEigenCoordinates.Coords b J0 C0 ∧
      (∀ x, (J0 x : N') = J x) ∧ (∀ i y, (C0 i y : N) = C i y) := by
  refine ⟨{ toFun := fun x => ⟨J x, hJ x x.2⟩
            map_zero' := by ext; simp
            map_add' := fun x y => by ext; simp },
    fun i => { toFun := fun y => ⟨C i y, hC i y y.2⟩
               map_zero' := by ext; simp
               map_add' := fun x y => by ext; simp }, ⟨?_, ?_, ?_⟩, fun _ => rfl, fun _ _ => rfl⟩
  · intro r x
    ext
    simp [h.smul]
  · intro y
    ext
    simp [Submodule.coe_sum, h.sum]
  · intro i o x
    ext
    simp [h.coord]

private theorem UpperTheory.V.Base.selBaseEig_lemma_3 {G : Type} [Group G] [TopologicalSpace G]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    {O M' : Type} [CommRing O] [Algebra R O] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M']
    {ι : Type} [Fintype ι] {b : Module.Basis ι R O}
    (ρ : Representation R G M) (ρ' : Representation O G M') (u : M →+ M') (hu : ∀ g m, u (ρ g m) = ρ' g (u m))
    {C : ι → M' →+ M} (h : UpperTheory.V.Base.SelmerBaseEigenCoordinates.Coords b u C)
    (hcomm : ∀ i g y, C i (ρ' g y) = ρ g (C i y)) :
    ∃ CH : (V : Subgroup G) → ι → H1U ρ' V →+ H1U ρ V,
      (∀ V, UpperTheory.V.Base.SelmerBaseEigenCoordinates.Coords b (UpperTheory.V.Base.SelmerBaseEigenCoordinates.hMap ρ ρ' u hu V) (CH V)) ∧
      (∀ (V' V : Subgroup G) (hV : V' ≤ V) i y, CH V' i (resU ρ' hV y) = resU ρ hV (CH V i y)) := by
  classical
  let CZ : (V : Subgroup G) → ι → Z1U ρ' V →+ Z1U ρ V := fun V i =>
    { toFun := fun f => ⟨fun g => C i (f.1 g), (continuous_of_discreteTopology (f := C i)).comp f.2.1,
        fun g g' => by
          show C i (f.1 (g * g')) = C i (f.1 g) + ρ g (C i (f.1 g'))
          rw [f.2.2 g g', map_add]
          exact congrArg _ (hcomm i _ _)⟩
      map_zero' := Subtype.ext (funext fun _ => map_zero (C i))
      map_add' := fun f f' => Subtype.ext (funext fun g => map_add (C i) _ _) }
  let CH : (V : Subgroup G) → ι → H1U ρ' V →+ H1U ρ V := fun V i =>
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) (CZ V i) fun f hf => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
      refine (mem_coboundaries1 _ _).2 ⟨C i m, fun g => ?_⟩
      have e : f.1 g = ρ' g m - m := hm g
      change C i (f.1 g) = ρ g (C i m) - C i m
      rw [e, map_sub, hcomm]
  have hCH : ∀ V i (z : Z1U ρ' V), CH V i (Submodule.Quotient.mk z) = Submodule.Quotient.mk (CZ V i z) :=
    fun _ _ _ => rfl
  refine ⟨CH, fun V => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro r x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, UpperTheory.V.Base.SelmerBaseEigenCoordinates.hMap_mk, UpperTheory.V.Base.SelmerBaseEigenCoordinates.hMap_mk,
      ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => h.smul r (z.1 g)))
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have key : (∑ i, b i • UpperTheory.V.Base.SelmerBaseEigenCoordinates.zMap ρ ρ' u hu V (CZ V i z)) = z := by
      refine Subtype.ext (funext fun g => ?_)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
      exact h.sum (z.1 g)
    conv_rhs => rw [← key]
    simp only [hCH, UpperTheory.V.Base.SelmerBaseEigenCoordinates.hMap_mk, ← Submodule.Quotient.mk_smul]
    exact (map_sum (Submodule.mkQ _) _ _).symm
  · intro i o x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [UpperTheory.V.Base.SelmerBaseEigenCoordinates.hMap_mk, ← Submodule.Quotient.mk_smul, hCH, ← Submodule.Quotient.mk_smul]
    exact congrArg _ (Subtype.ext (funext fun g => h.coord i o (z.1 g)))
  · intro V' V hV i y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rfl

private theorem UpperTheory.V.Base.resU_hMap_comm {G : Type} [Group G] [TopologicalSpace G]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    {O M' : Type} [CommRing O] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M']
    (ρ : Representation R G M) (ρ' : Representation O G M') (u : M →+ M') (hu : ∀ g m, u (ρ g m) = ρ' g (u m))
    (V' V : Subgroup G) (hV : V' ≤ V) (x : H1U ρ V) :
    resU ρ' hV (UpperTheory.V.Base.SelmerBaseEigenCoordinates.hMap ρ ρ' u hu V x) =
      UpperTheory.V.Base.SelmerBaseEigenCoordinates.hMap ρ ρ' u hu V' (resU ρ hV x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

private theorem UpperTheory.V.Base.selBaseEig_lemma_5 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
    {O M' : Type} [CommRing O] [AddCommGroup M'] [Module O M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M']
    (ρ : Representation R G M) (ρ' : Representation O G M') (u : M →+ M') (hu : ∀ g m, u (ρ g m) = ρ' g (u m))
    (U : Subgroup G) [U.Normal] (g : G) (x : H1U ρ U) :
    conjU ρ' U g (UpperTheory.V.Base.SelmerBaseEigenCoordinates.hMap ρ ρ' u hu U x) =
      UpperTheory.V.Base.SelmerBaseEigenCoordinates.hMap ρ ρ' u hu U (conjU ρ U g x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun w => (hu _ _).symm))

set_option maxHeartbeats 800000 in
open UpperTheory.V.Base.SelmerBaseEigenCoordinates in
theorem UpperTheory.V.Base.selBaseEig :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (O M' : Type) [CommRing O] [Algebra R O] [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] [Module.Free R O]
      [Module.Finite R O] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M'] [TopologicalSpace M']
      [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M'] (ρ' : Representation O G M') (j : M →ₗ[R] M'),
      IsBaseChange O j → (∀ g m, j (ρ g m) = ρ' g (j m)) → ∀ (U : Subgroup G) [U.Normal] (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      (∀ (W : Subgroup G) (ψ : W →* Rˣ), Module.length O (selEig ρ' U h𝒟 W ((Units.map (algebraMap R O).toMonoidHom).comp ψ)) =
        Module.length R (selEig ρ U h𝒟 W ψ) * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O))) ∧
      ∀ (g : G) (s : R), Module.length O (Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s)) =
        Module.length R (Module.End.eigenspace (selRep ρ U h𝒟 g) s) * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ O M' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' j hj hu U _ 𝒟 h𝒟
  classical
  let b := Module.Free.chooseBasis R O
  obtain ⟨C, hC⟩ := UpperTheory.V.Base.exists_coords_of_isBaseChange b j hj
  have hu' : ∀ g m, j.toAddMonoidHom (ρ g m) = ρ' g (j.toAddMonoidHom m) := fun g m => hu g m
  have hcomm : ∀ i g y, C i (ρ' g y) = ρ g (C i y) := fun i g y =>
    Coords.comm hC (fun m => ρ g m) (ρ' g) (fun x => hu g x) i y
  obtain ⟨CH, hCH, hres⟩ := UpperTheory.V.Base.selBaseEig_lemma_3 ρ ρ' j.toAddMonoidHom hu' hC hcomm
  have hLJ : ∀ x ∈ LocSel ρ U 𝒟, hMap ρ ρ' j.toAddMonoidHom hu' U x ∈ LocSel ρ' U 𝒟 := by
    intro x hx
    simp only [LocSel, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    intro D hD
    rw [UpperTheory.V.Base.resU_hMap_comm, hx D hD, map_zero]
  have hLC : ∀ i, ∀ y ∈ LocSel ρ' U 𝒟, CH U i y ∈ LocSel ρ U 𝒟 := by
    intro i y hy
    simp only [LocSel, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
    intro D hD
    rw [← hres, hy D hD, map_zero]
  obtain ⟨JL, CL, hL, hJL, -⟩ := UpperTheory.V.Base.coords_restrict_to_submodules (hCH U) _ _ hLJ hLC
  have hJconj : ∀ g x, JL (selRep ρ U h𝒟 g x) = selRep ρ' U h𝒟 g (JL x) := by
    intro g x
    apply Subtype.ext
    rw [hJL]
    exact (UpperTheory.V.Base.selBaseEig_lemma_5 ρ ρ' _ hu' U g x.1).symm.trans (congrArg _ (hJL x).symm)
  have hCconj : ∀ i g y, CL i (selRep ρ' U h𝒟 g y) = selRep ρ U h𝒟 g (CL i y) := fun i g y =>
    Coords.comm hL (fun x => selRep ρ U h𝒟 g x) (selRep ρ' U h𝒟 g) (hJconj g) i y
  have hCs : ∀ i (s : R) y, CL i (algebraMap R O s • y) = s • CL i y := fun i s y =>
    Coords.comm hL (fun x => s • x) (algebraMap R O s • LinearMap.id) (fun x => by simp [hL.smul]) i y
  constructor
  · intro W ψ
    have hEJ : ∀ x ∈ selEig ρ U h𝒟 W ψ, JL x ∈ selEig ρ' U h𝒟 W ((Units.map (algebraMap R O).toMonoidHom).comp ψ) := by
      intro x hx
      simp only [selEig, eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, sub_eq_zero, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hx ⊢
      intro w
      rw [← hJconj, hx w, hL.smul]
    have hEC : ∀ i, ∀ y ∈ selEig ρ' U h𝒟 W ((Units.map (algebraMap R O).toMonoidHom).comp ψ),
        CL i y ∈ selEig ρ U h𝒟 W ψ := by
      intro i y hy
      simp only [selEig, eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, sub_eq_zero, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hy ⊢
      intro w
      rw [← hCconj, hy w, hCs]
    obtain ⟨JE, CE, hE, -, -⟩ := UpperTheory.V.Base.coords_restrict_to_submodules hL _ _ hEJ hEC
    exact Coords.length hE
  · intro g s
    have hEJ : ∀ x ∈ Module.End.eigenspace (selRep ρ U h𝒟 g) s,
        JL x ∈ Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s) := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [← hJconj, hx, hL.smul]
    have hEC : ∀ i, ∀ y ∈ Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s),
        CL i y ∈ Module.End.eigenspace (selRep ρ U h𝒟 g) s := by
      intro i y hy
      rw [Module.End.mem_eigenspace_iff] at hy ⊢
      calc selRep ρ U h𝒟 g (CL i y) = CL i (selRep ρ' U h𝒟 g y) := (hCconj i g y).symm
        _ = CL i (algebraMap R O s • y) := congrArg _ hy
        _ = s • CL i y := hCs i s y
    obtain ⟨JE, CE, hE, -, -⟩ := UpperTheory.V.Base.coords_restrict_to_submodules hL (Module.End.eigenspace (selRep ρ U h𝒟 g) s)
      (Module.End.eigenspace (selRep ρ' U h𝒟 g) (algebraMap R O s)) hEJ hEC
    exact Coords.length hE
